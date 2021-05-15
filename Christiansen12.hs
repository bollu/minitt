import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

-- :main examples/untyped/christiansen-sec1.rkt

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
     putStrLn $ name <> ":\n\t"  <> show v
     return ((name,v):env)
  return ()


data Val = VClosure CLOSURE 
instance Show Val where
  show (VClosure c) = show c

-- 6.2: Values
type Env a = [(Name, a)]
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
  evalap vrator vrand

evalap :: Val -> Val -> Either String Val
evalap (VClosure (CLOSURE env x body)) arg = 
    eval ((x,arg):env) body
