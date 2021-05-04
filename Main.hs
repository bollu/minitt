import AST
import Data.Either
-- Parse
data Exp = Elam Pat Exp 
  | Eident String
  | Eapp Exp Exp
  | Epi Pat Exp Exp
  | Eu
  | Epair Exp Exp
  | Efst Exp
  | Esnd Exp
  | Esigma Exp Exp
  | Ezero
  | Eone
  | Econ String Exp
  | Efun [Choice]
  | Esum [Choice]
  | Edec Decl Exp deriving(Eq, Ord, Show)
type Choice = (String, Exp)

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

toExp :: AST -> Either Error Exp
toExp = undefined

