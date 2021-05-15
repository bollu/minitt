-- Untyped calculus with
-- normalization by evaluation.
-- https://en.wikipedia.org/wiki/Normalisation_by_evaluation
-- A Denotational Account of Untyped Normalization by Evaluation
-- https://link.springer.com/content/pdf/10.1007%2F978-3-540-24727-2_13.pdf
import System.Environment
import System.Exit
import AST
import Data.List (intercalate)
import Data.Maybe (fromJust)
import Data.Monoid (All, getAll)
import Control.Monad(forM_, forM, foldM)
import Debug.Trace(trace)

type Name = String

-- | syntax
data Stx = 
    Stxlam Name Stx  -- λ x f x
  | Stxident Name -- x
  | Stxap Stx Stx -- (f x)
  deriving(Eq, Ord)

instance Show Stx where
  show (Stxlam name body) = "(λ " ++ name  ++ "  " ++ show body ++ ")"
  show (Stxident x) = x
  show (Stxap f x) = "($ " ++ show f ++ " " ++ show x  ++ ")"

-- | counter to generate fresh variables
type FreshCount = Int

-- | semantics, deep embedding
data Value = VUnit 
  | Vlam (Value -> Value)
  | Vstx (FreshCount -> Stx)

instance Show Value where
  show (Vlam f) = "(sem:λ" ++ "<<code>>" ++ ")"
  show (Vstx stx) =  "(sem:stx " ++ show (stx 0) ++ ")"

toExp :: AST -> Either Error Stx
toExp (Atom span ident) = Right $ Stxident ident
toExp tuple = do
  head  <- tuplehd atom tuple
  case head of 
      "λ" -> do 
        ((), x, body) <- tuple3f astignore atom toExp tuple
        return $ Stxlam x body
      "$" -> do 
        ((), f, x) <- tuple3f astignore toExp toExp tuple
        return $ Stxap f x
      _ -> Left $ "unknown head |" ++ head ++ "| in " ++ "|" ++ astPretty tuple ++ "|"


toDecl :: AST -> Either Error (Name, Stx)
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

  foldM' decls $ \env (name, stx) -> do
     let v = stx2sem env  stx
     let vstx = sem2stx 0 v
     putStrLn $ name <> ":\n\t"  <> show vstx
     return ((name,v):env)
  return ()


-- | type directed reification into syntax
sem2stx :: FreshCount -> Value -> Stx
sem2stx n (Vstx n2stx) = n2stx n
sem2stx n (Vlam f) = 
 let var = "#" ++ show n
     semvar = Vstx $ \_ -> Stxident var
 in Stxlam var $ sem2stx (n+1) (f semvar)

-- | type directed semantic lifting
stx2sem :: [(Name, Value)] -> Stx -> Value
stx2sem env (Stxident name) = fromJust $ lookup name env
stx2sem env (Stxlam x body) = 
    Vlam $ \xval -> stx2sem ((x,xval):env) body 
stx2sem env (Stxap f x) = 
    case stx2sem env f of
        Vlam f -> f (stx2sem env x)
        Vstx n2fstx -> Vstx $ \n -> 
            Stxap (n2fstx n) (sem2stx n (stx2sem env x))


nbe :: [(Name, Value)] -> Stx -> Stx
nbe env stx = sem2stx 0 (stx2sem env stx)
