-- Untyped calculus with
-- normalization by evaluation.
-- https://en.wikipedia.org/wiki/Normalisation_by_evaluation
-- A Denotational Account of Untyped Normalization by Evaluation
-- https://link.springer.com/content/pdf/10.1007%2F978-3-540-24727-2_13.pdf
import System.Environment
import System.Exit
import AST
import Data.Maybe (fromJust)
import Data.Monoid (All, getAll)
import Control.Monad(forM_)

type Name = String

-- | syntax
data Stx = 
    Stxlam Name Stx 
  | Stxident Name
  | Stxap Stx Stx
  -- | Stxmkpair Stx Stx
  -- | Stxfst Stx
  -- | Stxsnd Stx
  -- | Stxdiamond -- Lozenge symbol (C-k lz); inhabitant of ()
  deriving(Eq, Ord)

instance Show Stx where
  show (Stxlam name body) = "(λ " ++ name  ++ "  " ++ show body ++ ")"
  show (Stxident x) = x
  show (Stxap f x) = "($ " ++ show f ++ " " ++ show x  ++ ")"
  -- show (Stxmkpair l r) = "(, " ++ show l ++ " " ++ show r  ++ ")"
  -- show (Stxfst p) = "(fst " ++ show p ++ ")"
  -- show (Stxsnd p) = "(snd " ++ show p ++ ")"
  -- show Stxdiamond = "◊"

-- | counter to generate fresh variables
type FreshCount = Int

-- | semantics, deep embedding
data Value = VUnit 
  | Vlam (Value -> Value)
  | Vstx (FreshCount -> Stx)

instance Show Value where
  show (Vlam f) = "(sem:λ" ++ "<<code>>" ++ ")"
  show (Vstx stx) =  "(sem:stx " ++ show (stx 0) ++ ")"


-- | declaration
data Decl = Decl Name Stx deriving (Eq, Ord, Show)

toStx :: AST -> Either Error Stx
-- toStx (Atom span "◊") = Right $ Stxdiamond
toStx (Atom span ident) = Right $ Stxident ident
toStx tuple = do
    head <- tuplehd atom tuple
    case head of 
        "λ" -> do 
          ((), x, body) <- tuple3f astignore atom toStx tuple
          return $ Stxlam x body
        "$" -> do 
          ((), f, x) <- tuple3f astignore toStx toStx tuple
          return $ Stxap f x
        -- "," -> do
        --     ((), l, r) <- tuple3f astignore toStx toStx tuple
        --     return $ Stxmkpair l r
        -- "fst" -> do 
        --     ((), x) <- tuple2f astignore toStx tuple
        --     return $ Stxfst x
        -- "snd" -> do 
        --     ((), x) <- tuple2f astignore toStx tuple
        --     return $ Stxsnd x
        _ -> Left $ "unknown head: " ++ "|" ++ astPretty tuple ++ "|"


-- (foo <type> <body>)
toDecl :: AST -> Either Error Decl
toDecl tuple = do
    (name, body) <- tuple2f atom toStx tuple
    return $ Decl name body

toToplevel :: AST -> Either Error [Decl]
toToplevel ast = tuplefor toDecl ast

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
           [path] -> pure path
           _ -> (print "expected single file path to parse") >> exitFailure
  file <- readFile path
  putStrLn $"file contents:"
  putStrLn $ file
  putStrLn $ "parsing..."
  ast <- case AST.parse file of
           Left failure -> print failure >> exitFailure
           Right success -> pure success
  putStrLn $ astPretty ast

  putStrLn $ "\nconvering to intermediate repr..."
  decls <- case toToplevel ast of
            Left failure -> print failure >> exitFailure
            Right d -> pure d
  putStrLn $ show decls
  forM_ decls  $ \(Decl name stx) -> do
        putStrLn $ "\nrunning |" ++ name  ++ "|..."
        let outstx = nbe stx 
        putStr $ "  output: "
        putStrLn $ show outstx
  return ()


-- | type directed reification into syntax
sem2stx :: FreshCount -> Value -> Stx
sem2stx n (Vstx n2stx) = n2stx n
sem2stx n (Vlam f) = 
 let var = "fresh" ++ show n
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



nbe :: Stx -> Stx
nbe stx =  let ctx = [] in sem2stx 0 (stx2sem ctx stx)

