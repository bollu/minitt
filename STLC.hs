-- Simply typed lambda calculus
import System.Environment
import System.Exit
import AST
import Data.Either

type Name = String

-- | syntax
data Stx = 
    Stxlam Name Stx 
  | Stxident Name
  | Stxap Stx Stx
  | Stxmkpair Stx Stx
  | Stxfst Stx
  | Stxsnd Stx
  | Stxdiamond -- inhabitant of ()
  deriving(Eq, Ord, Show)

-- | type system
data Type = Tyfn Type Type | Typair Type Type | Tyunit deriving(Eq, Ord, Show)

-- | semantics, deep embedding
data Value = VUnit 
  | Vpair Value Value
  | Vlam (Value -> Value)
  | Vstx Stx
  | Vdiamond -- inhabitant of ()

instance Show Value where
  show (Vpair l r) = "(sem:," ++ show l ++ " " ++ show r  ++ ")"
  show (Vlam f) = "(sem:λ" ++ "<<code>>" ++ ")"
  show (Vstx stx) =  "(sem:stx" ++ show stx ++ ")"
  show Vdiamond = "sem:◊"


-- | declaration
data Decl = Decl Name Type Stx deriving (Eq, Ord, Show)

toStx :: AST -> Either Error Stx
toStx (Atom span "◊") = Right $ Stxdiamond
toStx (Atom span ident) = Right $ Stxident ident
toStx tuple = do
    (head, tail) <- tupleatomtail tuple
    case head of 
        "λ" -> do 
          (x, body) <- tuple2f atom toStx tail
          return $ Stxlam x body
        "$" -> do 
          (f, x) <- tuple2f toStx toStx tail
          return $ Stxap f x
        "," -> do
            (l, r) <- tuple2f toStx toStx tail
            return $ Stxmkpair l r
        "fst" -> Stxfst <$> toStx tail
        "snd" -> Stxsnd <$> toStx tail
        _ -> Left $ "unknown head: " ++ "|" ++ astPretty tuple ++ "|"

toType :: AST -> Either Error Type
toType (Atom span "1") = Right Tyunit
toType tuple = do
    (head, tail) <- tupleatomtail tuple
    case head of
        "*" -> do
            (l, r) <- tuple2f toType toType tail
            return $ Typair l r
        "→" -> do
            (l, r) <- tuple2f toType toType tail
            return $ Tyfn l r
        _ -> Left $ "unknown type head: " ++ "|" ++ astPretty tuple ++ "|"


-- (foo <type> <body>)
toDecl :: AST -> Either Error Decl
toDecl tuple = do
    (name, ty, body) <- tuple3f atom toType toStx tuple
    return $ Decl name ty body

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

stx2sem :: Type -> Stx -> Value
stx2sem Tyunit _ =  Vdiamond
stx2sem (Tyfn i o) f =  
  Vlam (\x -> stx2sem o (Stxap f (sem2stx i x)))
stx2sem (Typair l r) p = Vpair (stx2sem l $ Stxfst p) (stx2sem r $ Stxsnd p)

sem2stx :: Type -> Value -> Stx
sem2stx (Typair tl tr) (Vpair l r) = 
  Stxmkpair (sem2stx tl l) (sem2stx tr r)
-- | TODO: need fresh names
sem2stx (Tyfn i o) (Vlam f) = 
    let fresh = "fresh_x"
    in Stxlam fresh (sem2stx o $ f (stx2sem i (Stxident fresh)))
sem2stx _ (Vstx stx) = stx -- how do stuck terms make progress?
