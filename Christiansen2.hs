-- runhaskell Christiansen2.hs examples/untyped/christiansen-sec1.rkt
-- runhaskell Christiansen2.hs examples/untyped/christiansen-sec2.rkt

import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

-- Now implement NBE
-- :main examples/untyped/christiansen-sec2.rkt
-- This is the sophisticated version that maintains a separate universe of "Neutral". 
-- It should be possible to peform a more naive translation if we are willing to store expression
-- trees directly. 

type Name = String

-- 1.2 The Evaluator --
-- Untyped LC
data Exp = 
    Elam Name Exp 
  | Eident String
  | Eap Exp Exp
  deriving(Eq, Ord)

instance Show Exp where
  show (Elam name exp) = "(λ " <> name <> " " <> show exp <> ")"
  show (Eident name) = name
  show (Eap f x) = "($ " <> show f <> " " <> show x <> ")"
type Choice = (String, Exp)

toExp :: AST -> Either Error Exp
toExp (Atom span ident) = Right $ Eident ident
toExp tuple = do
  head  <- tuplehd atom tuple
  case head of 
      "λ" -> do 
        ((), x, body) <- tuple3f astignore atom toExp tuple
        return $ Elam x body
      "$" -> do 
        ((), f, x) <- tuple3f astignore toExp toExp tuple
        return $ Eap f x
      _ -> Left $ "unknown head |" ++ head ++ "| in " ++ "|" ++ astPretty tuple ++ "|"


toDecl :: AST -> Either Error (Name, Exp)
toDecl = tuple2f atom toExp

foldM' :: (Monoid s, Monad m, Traversable t) => t a -> (s -> a -> m s) -> m s
foldM' t f = foldM f mempty t

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
           [path] -> pure path
           _ -> (putStrLn "expected single file path to parse") >> exitFailure
  file <- readFile path
  putStrLn $"file contents:"
  putStrLn $ file
  putStrLn $ "parsing..."
  ast <- case AST.parse file of
           Left failure -> putStrLn failure >> exitFailure
           Right success -> pure success
  putStrLn $ astPretty ast

  putStrLn $ "convering to intermediate repr..."
  decls <- case tuplefor toDecl ast of
            Left failure -> putStrLn failure >> exitFailure
            Right d -> pure d

  foldM' decls $ \env (name,exp) -> do
     v <- case eval env exp of
            Left failure -> putStrLn failure >> exitFailure
            Right v -> pure v
     ev <- case readBack [] v of
            Left failure -> putStrLn failure >> exitFailure
            Right ev -> pure ev
     putStrLn $ name <> ":\n\t"  <> show ev
     return ((name,v):env)
  return ()


-- 6.2: Values
type Env a = [(Name, a)]

-- | Domain of values, can either be closures (created from lambdas),
-- or neutral [stuck terms], which are either variables whose values are unknown,
-- or applications which cannot be reduced.
data Val = VClosure CLOSURE | VNeutral NEUTRAL

instance Show Val where
  show (VClosure c) = show c
  show (VNeutral n) = show n

-- | Γ/context (Env Val) |- \x (Name) -> body (Expr)
data CLOSURE = CLOSURE (Env Val)  Name  Exp

data NEUTRAL = NeutralVar Name | NeutralAp NEUTRAL Val 

-- | the `.` indicates that it is stuck/full stop/neutral.
instance Show NEUTRAL where
  show (NeutralVar v) = "." <> v
  show (NeutralAp  f x) = ".(" <> show f <> " " <> show x <> " )."

instance Show CLOSURE where
  show (CLOSURE env x body) = 
     let envstr = intercalate ";" [n <> ":" <> show v | (n, v) <- env]
     in "{" <> envstr <> " | " <> x <> " | " <> show body <> "}"

type M a = Either a Name


eval :: Env Val -> Exp -> Either String Val
-- Create a closure to evaluate a lambda
eval env (Elam name rhs) = Right $ VClosure $ CLOSURE env name rhs 
-- Lookup a value in the environment to evaluate an identifier.
eval env (Eident name) = 
  case lookup name env of
    Just v -> Right v
    Nothing -> Left $ "unable to find variable |" <> name <> "|"
-- Evaluate the operator and the operand, and then eval the ap,
-- such that we take care of neutral terms.
eval env (Eap rator rand) = do
  vrator <- eval env rator
  vrand <- eval env rand
  evalap vrator vrand

evalap :: Val -> Val -> Either String Val
-- If we have an honest closure, then evaluate it.
evalap (VClosure (CLOSURE env x body)) arg = 
    eval ((x,arg):env) body
-- If we have a neutral, then it's a ball of mud, clump more into the ball of mud!
evalap (VNeutral f) arg = 
  return $ VNeutral (NeutralAp f arg)

fresh :: [Name] -> Name -> Name
fresh used x = 
  case find (== x) used of
    Just _ -> fresh used (x <> "*")
    Nothing -> x

readBack :: [Name] -> Val -> Either String Exp
-- generate a fresh name for x, create a neutral variable for x [ball of mud],
-- then send it into the body. Finally, read the value back.
readBack names (VClosure (CLOSURE env x ebody)) = do
  let y = fresh names x
  let neutraly = NeutralVar y
  vbody <- eval ((x,(VNeutral neutraly)):env) ebody
  ebody' <- readBack (y:names) vbody
  return $ Elam y ebody'
-- If we have a neutral, then read it bak as normal.
readBack names (VNeutral neutral) = 
  readBackNeutral names neutral

readBackNeutral :: [Name] -> NEUTRAL -> Either String Exp
readBackNeutral names (NeutralVar v) = Right $ Eident v
readBackNeutral names (NeutralAp neutralf valx) = do 
  ef <- (readBackNeutral names neutralf)
  ex <- (readBack names valx)
  return $ Eap ef ex
