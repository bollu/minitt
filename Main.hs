import System.Environment
import System.Exit
import AST
import Data.Either
-- Parse
data Exp = 
    Elam Pat Exp 
  | Eident String
  | Eap Exp Exp
  | Epi Pat Exp Exp
  | Eu
  | Epair Exp Exp
  | Efst Exp
  | Esnd Exp
  | Esigma Pat Exp Exp
  | E0
  | E1
  | Econ String Exp
  | Efun [Choice]
  | Esum [Choice]
  -- | local let?
  | Edec Decl Exp
  deriving(Eq, Ord, Show)
type Choice = (String, Exp)

toExp :: AST -> Either Error Exp
toExp (Atom span ident) = 
    case ident of
        "U" -> Right $ Eu
        "0" -> Right $ E0
        "1" -> Right $ E1
        _ -> Right $ Eident ident
-- | TODO: check if we have (x y) where x is not a special form
-- and in that case, make it an application.
toExp ast = toExpSpecialForm ast

-- | convert special form such as (foo xxx)
-- into an expr
toExpSpecialForm :: AST -> Either Error Exp
toExpSpecialForm tuple = do
    (head, tail) <- tupleatomtail tuple
    case head of 
        "λ" -> do 
          (x, body) <- tuple2f toPat toExp tail
          return $ Elam x body
        "$" -> do 
          (f, x) <- tuple2f toExp toExp tail
          return $ Eap f x
        "Π" -> do
            ((x, tyin), tyout) <- tuple2f (tuple2f toPat toExp) toExp tail
            return $ Epi x tyin tyout
        "→" -> do -- sugar
            (tyin, tyout) <- tuple2f toExp toExp tail
            return $ Epi Pblank tyin tyout
        -- "U" 
        "pair" -> do
            (l, r) <- tuple2f toExp toExp tail
            return $ Epair l r
        "fst" -> Efst <$> toExp tail
        "snd" -> Esnd <$> toExp tail
        "sigma" -> do
            (x, ty, body) <- tuple3f toPat toExp toExp tail
            return $ Esigma x ty body
        -- "0"
        -- "1" 
        -- c M ???
        -- "con" -> ECon <$> tuple2f atom  toExp tail
        "fun" -> Efun <$> tuplefor toChoice tail
        "Sum" -> Esum <$> tuplefor toChoice tail
        "decl" -> do 
            (decl, body) <- tuple2f toDecl toExp tail
            return $ Edec decl body
        _ -> Left $ "unknown head: " ++ "|" ++ astPretty tuple ++ "|"
  

data Decl =
   Dlet Pat Exp Exp
 | Dletrec Pat Exp Exp
  deriving (Eq,Ord,Show)

data Pat =
   Ppair Pat Pat
 | Pblank
 | Pvar String
  deriving (Eq,Ord,Show)

-- (let/letrec pat type val)
toDecl :: AST -> Either Error Decl
toDecl ast = do
  -- [x, y, z] <- tuple 3 ast
  (astdecl, astpat, astty, astrhs) <- tuple4 ast
  head <- atomOneOf ["let", "letrec"] astdecl
  pat <- toPat astpat
  ty <- toExp astty
  rhs <- toExp astrhs
  case head of
    "let" -> Right $ Dlet pat ty rhs
    "letrec" -> Right $ Dletrec pat ty rhs

-- atom: x || atom: _ || atom: (x x)
toPat :: AST -> Either Error Pat
toPat (Atom span "_") = Right $ Pblank
toPat (Atom span name) = Right $ Pvar name
toPat (Tuple span _ (l:r:[])) = do
 l <- toPat l
 r <- toPat r
 return $ Ppair l r
toPat (Tuple span _ _) = 
  Left $ errAtSpan span $ "expected pattern; pat := name | _ | (pat pat)"


-- | TODO: consider changing this to :atom exp
-- | choice: (atom exp)
toChoice :: AST -> Either Error Choice
toChoice ast = tuple2f atom toExp ast


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

  putStrLn $ "convering to intermediate repr..."
  decls <- case toToplevel ast of
            Left failure -> print failure >> exitFailure
            Right d -> pure d
  putStrLn $ show decls
