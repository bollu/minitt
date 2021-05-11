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
import Control.Monad(forM_, forM)
import Debug.Trace(trace)

type Name = String

-- | syntax
data Stx = 
    Stxlam Name Stx  -- λ x f x
  | Stxlet [(Name, Stx)] Stx -- let xi := fooi in bar
  | Stxident Name -- x
  | Stxap Stx Stx -- (f x)
  deriving(Eq, Ord)

instance Show Stx where
  show (Stxlam name body) = "(λ " ++ name  ++ "  " ++ show body ++ ")"
  show (Stxident x) = x
  show (Stxlet namevals body) = 
    "(let " ++ 
       intercalate " " [n ++ " " ++ show v|(n, v)<-namevals] ++ 
         " " ++ show body ++ ")"
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


-- | declaration
data Decl = Decl Name Stx deriving (Eq, Ord, Show)

withErr :: a -> Either a b -> Either a b
withErr a (Left _) = Left a
withErr _ (Right b) = Right b

unless :: Bool -> String -> Either String ()
unless True _ = Right ()
unless False err = Left err

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
        "let" -> do
            -- let x1 v1 x2 v2 .. xn vn result
            -- 1   --2-- --2-- .. --2-- 1
            -- total: even
            -- unless (even . length . tupleget $ tuple)
            --        ("expected even number of arguments to let |" ++ astPretty ++ "|")
            let n = length . tupleget $ tuple
            nvs <- forM [1,3..(n-3)] $ \ix -> do
                     -- | TODO: find good method to have good error messages!
                     name <- atom (tupleget tuple !! ix)
                     val <- toStx (tupleget tuple !! (ix+1))
                     return (name, val)
            body <- toStx . last . tupleget $ tuple
            return $ Stxlet nvs body
        _ -> Left $ "unknown head: " ++ "|" ++ astPretty tuple ++ "|"


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
  ast <- case AST.parse file >>= at 0 of
           Left failure -> putStrLn failure >> exitFailure
           Right success -> return success
  putStrLn $ astPretty ast

  putStrLn $ "\nconverting to intermediate repr..."
  stx <- case toStx ast of
            Left failure -> putStrLn failure >> exitFailure
            Right  stx -> do print stx; pure stx
  let outstx = nbe stx 
  putStr $ "\n\n@output: "
  putStrLn $ show outstx
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
stx2sem env (Stxlet namevals body) = 
    stx2sem ([(n, stx2sem env v) | (n,v) <-namevals] ++ env) body



nbe :: Stx -> Stx
nbe stx =  let ctx = [] in sem2stx 0 (stx2sem ctx stx)
