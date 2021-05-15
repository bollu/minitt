import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

-- A rewrite of ./Christiansen2.hs without using Neut, but simply reusing Exp
-- (ie, store syntax within semantics)

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

data Val = VClosure CLOSURE | VStx Exp

instance Show Val where
  show (VClosure c) = show c
  show (VStx e) = show e

-- | context, \x (Name) -> body (Expr)
data CLOSURE = CLOSURE (Env Val)  Name  Exp

instance Show CLOSURE where
  show (CLOSURE env x body) = 
     let envstr = intercalate ";" [n <> ":" <> show v | (n, v) <- env]
     in "{" <> envstr <> " | " <> x <> " | " <> show body <> "}"

type M a = Either a Name


eval :: Env Val -> Exp -> Either String Val
eval env (Elam name rhs) = Right $ VClosure $ CLOSURE env name rhs 
eval env (Eident name) = 
  case lookup name env of
    Just v -> Right v
    Nothing -> Left $ "unable to find variable |" <> name <> "|"
eval env (Eap rator rand) = do
  vrator <- eval env rator
  vrand <- eval env rand
  case vrator of
    (VClosure (CLOSURE env x body)) -> do
        eval ((x, vrand):env) body
    VStx rator' -> do
        rand' <- readBack [] vrand
        return $ VStx $ Eap rator' rand'

fresh :: [Name] -> Name -> Name
fresh used x = 
  case find (== x) used of
    Just _ -> fresh used (x <> "*")
    Nothing -> x

readBack :: [Name] -> Val -> Either String Exp
readBack names (VClosure (CLOSURE env x ebody)) = do
  let y = fresh names x
  let yv = VStx . Eident $ y
  vbody <- eval ((x, yv):env) ebody
  ebody' <- readBack (y:names) vbody
  -- return $ Elam y ebody'
  return $ Elam x ebody
readBack names (VStx expr) = return $ expr
