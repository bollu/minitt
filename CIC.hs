-- This is on hiatus because this is very complex, much more than what I feel
-- is useful for learning *right now*.
-- An implementation of CIC from "a compact kernel for CIC"
-- | max of universes, +1 if bool is true.
type Univ = (Bool, [URI])
data Sort = Prop | Type Univ
data ImplicitAnnotation =  Closed | Hole | Type | Term
-- | no idea what this is.
-- | subst(Irl n) means id of length n ???
data LCKind = Irl Int | Ctx [Term]
-- | shift: 0 -> no shift
type LocalCtx = (Int, LCKind)

data Term = Rel Int  -- debruijn, 1-indexed.
  | Meta (Int, LocalCtx)
  | Appl [Term] -- arguments.
  | Prod (String, Term, Term) -- ^ binder, src, target
  | Lambda (String, Term, Term) -- ^ binder, src target
  | LetIn (String, Term, Term, Term) -- ^ binder, type, tm, body
  | Const Reference -- ^ ref: (IndType | Constr)no
  | Sort Sort
  | Implicit ImplicitAnnotation
  | Match Reference Term Term [Term] -- ^ inductive reference, output type, inductive term, branches


