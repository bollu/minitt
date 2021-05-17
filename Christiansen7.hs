{-# LANGUAGE NoImplicitPrelude #-}
import Prelude hiding(EQ)
import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

-- 7. Dependently yped lang
-- http://davidchristiansen.dk/tutorials/nbe/

type Name = String

-- TODO: HOW TO PROVE GALOIS CORRESPONDENCE BETWEEN STX AND SEM?

-- data Type = Tnat | Tarrow Type Type deriving(Eq, Ord) 

-- Value: 
--   An expression with a constructor at the top is called as a value.
--   Not every value is in normal form. This is because the
--   arguments to a constructor need not be normal. Each
--   expression has only one normal form, but it is sometimes
--   possible to write it as a value in more than one way.
--   (add (+ (addi zero) (addi one))) is a value, but is NOT a normal form.
-- Atom:
--   A tick mark directly followed by one or more letters or hyphens is an Atom.
--   Two expressions are the same Atom if their values are tick marks followed
--   by identical letters and hyphens.
--   Atom is a type.
-- Neutral Expressions:
--   Neutral expressions that are written identically are the same, no matter
--   their type.
-- Pair:
--   Pair is a type.
--   Two cons-expressions are the same (Pair A D) if their cars are the same A and
--   their cdrs are the same D, where A and D stand for any type.
--
-- Replace:
--   If target is an (= X from to),
--   mot is an (→ X U),
--   and base isa (mot from)
--   then (replace target mot base)
--   is a (mot to).
--  
-- Absurd: / Void
--   Absurd is a type.
--   Every expression of type Absurd is neutral, and all
--   of them are the same.
--   The expression (ind-absurd target mot) is mot if 
--   target is an Absurd and mot is a U
-- Ind-Nat and Motive:
--   the extra argument to ind-nat is called as the motive, and is any (→ Nat U)
--   An ind-Nat-expression’s type is the motive applied to the target Nat.
--   If target is a Nat, mot is a (→ Nat U), base is a (mot zero), 
--   step is a (Π (nprev Nat) (→ (mot nprev) (mot (add1 nprev)))), then
--   (ind-nat target mot base step) is is a (mot target).
--   The motive explains *why* the target is to be eliminated. Intuitively,
--   it tells us why we are eliminating the nat, and what we want to build next
--   after consuming the nat. So it tells us *why* we are eliminating the nat.
--   Motive ~= dependent return type.
--   Sole (◊): Trivial (Unit)
--
--
--   Eq/Same:
--     Eq A from to :: Univ;  witnesses  equality between (from:A) and (to:A).
--     SAME is the sole inhabitant of Eq.
--
--   Quote/Atom:
--     (Quote x) is of type ATOM.
--     ATOMs are equal if their quoted values are equal.
--    

-- Don't call stuff "scrutinee", call stuff "motive"! 
data Exp = 
    Elam Name Exp  -- (λ f x)
  | Epi Name Exp Exp -- (Π [x tdom] tran)
  | Eap Exp Exp -- ($ f x)
  | Esigma Name Exp Exp -- [Σ [x tfst] tsnd]
  | Econs Exp Exp -- (x, v)
  | Ecar Exp 
  | Ecdr Exp 
  | Enat
  | E0
  | Eadd1 Exp
  | Eindnat Exp Exp Exp Exp -- (ind-nat <target> <motive> <base> <step>)
  | Eeq Exp Exp Exp -- (= ty a b)
  | Esame 
  | Ereplace Exp Exp Exp  -- (replace <target> <motive> <base>)
  | Etrivial -- type ~= Unit
  | Esole -- sole inhabitant of trivial ~= ◊=sole : Unit=Trivial 
  | Eabsurd -- empty type / void
  | Eindabsurd Exp Exp  -- (ind-absurd <target> <motive>)
  | Eatom -- ? What is Atom? 
  | Equote Exp -- ' id
  | Euniv -- U
  | Eident String -- x
  | Eannotate Exp Exp -- type exp
  deriving(Eq, Ord)

-- | Check if expression is a simple expression with no data,
-- so like a keyword
expIsKeyword :: Exp -> Bool
expIsKeyword Euniv = True
expIsKeyword Esame = True
expIsKeyword Etrivial = True
expIsKeyword Esole = True
expIsKeyword Eabsurd = True
expIsKeyword Eatom = True


-- This is kinda sus:
-- -----------------
-- TODO: look at nominal sets and see if they improve dealing with binders.
-- >  In the interest of keeping the α-equivalence procedure short, it does not
-- > reject invalid programs, so it cannot be used to check for syntactically valid
-- > programs the way that the reflexive case of type=? could be used to test for
-- > syntactically valid simple types.

-- | Can have false positives (accepts incorrect programs (!))
-- Will never reject two alpha equivalent terms
alphaEquiv :: Exp -> Exp -> Bool
alphaEquiv a b = fst $ alphaEquivGo a b [] [] 0

-- | int is used to generate new names
alphaEquivGo :: Exp -> Exp -> [(Name, Int)] -> [(Name, Int)] -> Int -> (Bool, Int)
alphaEquivGo (Eident x) (Eident y) xs ys n = 
    case (lookup x xs, lookup y ys) of
      (Nothing, Nothing) -> (x == y, n)
      (Just x', Just y') -> (x' == y', n)
alphaEquivGo (Elam x b) (Elam x' b') xs xs' n = 
    let fresh = n
        bigger = (x,fresh):xs
        bigger' = (x',fresh):xs'
    in alphaEquivGo b b' bigger bigger' (n+1)

alphaEquivGo (Epi x t b) (Epi x' t' b') xs xs' n = 
    let fresh = n
        bigger = (x,fresh):xs
        bigger' = (x',fresh):xs'
    in alphaEquivGo b b' bigger bigger' (n+1)

alphaEquivGo (Esigma x t b) (Esigma x' t' b') xs xs' n = 
    let fresh = n
        bigger = (x,fresh):xs
        bigger' = (x',fresh):xs'
    in alphaEquivGo b b' bigger bigger' (n+1)

-- | WTF is quote
alphaEquivGo (Equote x) (Equote x') _ _ n = (x == x', n)
alphaEquivGo (Econs op args) (Econs op' args') _ _ n = 
    error $ "unimplemented α equivalence for cons"

-- | This, together with read-back-norm, implements the η law for Absurd.
alphaEquivGo (Eannotate t Eabsurd) (Eannotate t' Eabsurd) _ _ n = (True, n)

alphaEquivGo e e' _ _ n = (expIsKeyword e && e == e', n)

instance Show Exp where
  show (Elam name exp) = "(λ " <> name <> " " <> show exp <> ")"
  show (Eident name) = name
  show (Eap f x) = "($ " <> show f <> " " <> show x <> ")"
  show (E0) = "0"
  show (Eadd1 x) = "(+1 " <> show x <> ")"
  show (Eannotate e t) = "(∈ " <> show e <> " " <> show t <> ")"
  -- show (Erec t target base step) = "(rec " <> show target <> " " <> show base <> " " <> show step <> ")"
type Choice = (String, Exp)


toExp :: AST -> Either Error Exp
toExp (Atom span "0") = Right $ E0
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
    "∈" -> do 
      ((), t, e) <- tuple3f astignore toExp toExp tuple
      return $ Eannotate t e
    "+1" -> do 
      ((), e) <- tuple2f astignore toExp tuple
      return $ Eadd1 e
    -- "rec" -> do 
    --   ((), ty, target, base, step) <- 
    --     tuple5f astignore toType toExp toExp toExp tuple
    --   return $ Erec ty target base step
    _ -> Left $ "unknown special form |" ++ head ++ 
                  "| in " ++ "|" ++ astPretty tuple ++ "|"


toDecl :: AST -> Either Error (Name, Exp)
toDecl = tuple2f atom toExp


foldM' :: (Semigroup s, Monad m, Traversable t) => 
  s -> t a -> (s -> a -> m s) -> m s
foldM' s t f = foldM f s t

foldM1' :: (Monoid s, Monad m, Traversable t) => 
  t a -> (s -> a -> m s) -> m s
foldM1' t f = foldM f mempty t

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
          [path] -> pure path
          _ -> (putStrLn "expected single file path to parse") >> exitFailure
  file <- readFile path
  putStrLn $ "file contents:"
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

  putStrLn $ "type checking and evaluating..."
  foldM1' decls $ \(tenv, venv) (name,exp) -> do
    putStrLn $ "- " <> name <> ":"
    -- t <- case synth tenv exp of
    --        Left failure -> putStrLn failure >> exitFailure
    --        Right t -> pure t
    t <- pure $ error "undefined type"
    putStrLn $ "\t+type: " <> show t
    v <- case val venv exp of
             Left failure -> putStrLn failure >> exitFailure 
             Right v -> pure v
    putStrLn $ "\t+evaluated. reading back..."
    exp' <- case  readbackVal [] t v of
             Left failure -> putStrLn failure >> exitFailure 
             Right v -> pure v
    putStrLn $ "\t+readback: " <> show exp'
    return ((name, t):tenv, (name,v):venv)
  return ()


errTyMismatch :: (Exp, Type) -> Type -> String
errTyMismatch (e, ety) expectedty = 
  "Found expression |" <> show e <> "|" <>
  "to have type " <> show ety <> "|." <>
  "Expected type |" <> show expectedty <> "|."


--- 6: NBE
data Val = 
    NAT |
    PI Val Closure | 
    LAM Closure |
    SIGMA Val Closure |
    PAIR Type Type |
    ZERO |
    ADD1 Val |
    EQ Type Val Val | -- Eq type from to
    SAME |
    TRIVIAL |
    SOLE |
    ABSURD |
    ATOM |
    QUOTE Exp | -- I really don't know what symbol? is
    UNIV |
    NEU Type Neutral -- NEU type neutral data
    deriving(Show)

type Type = Val

-- | the embedding is shallow because it's used by shallow people in a hurry
-- who don't want to deal with binders!
data Closure = 
    ClosureShallow Name (Val -> Either String Val) | 
    ClosureDeep [(Name, Val)] Name Exp 

-- for a closure (ρ, \x. e) return x
closureArgumentName  :: Closure -> Name
closureArgumentName (ClosureShallow name _) = name
closureArgumentName (ClosureDeep _ name _) = name

instance Show Closure where
  show (ClosureShallow arg _) = 
    "ClosureShallow(" <> show arg <> " " <> "<<code>>)"
  show (ClosureDeep env arg body) = 
    "ClosureDeep(" <> show env <> " " <> show arg <> " " <> show body <> ")"

   
data TyAndVal = TyAndVal Type Val deriving(Show)
--- | The thing at the "to be reduced" position is stuck
data Neutral = 
    Nvar Name 
  | Nap Neutral TyAndVal
  | Ncar Neutral
  | Ncdr Neutral
  | Nindnat Neutral TyAndVal TyAndVal TyAndVal -- target motive base step
  -- | what does replace eliminate? EQ?
  | Nreplace Neutral TyAndVal TyAndVal -- target motive base 
  | Nindabsurd Neutral TyAndVal -- target motive 
  deriving(Show)

data Ctx = CtxEmpty | CtxDef Name Type Val Ctx | CtxBind Name Type Ctx

lookupType :: Ctx -> Name -> Maybe Val
lookupType (CtxEmpty) _ = Nothing
lookupType (CtxDef n t _ ctx') name = 
    if n == name then Just t else lookupType ctx' name
lookupType (CtxBind n t ctx') name = 
    if n == name then Just t else lookupType ctx' name

extendCtx :: Ctx -> Name -> Type -> Ctx
extendCtx ctx name ty = CtxBind name ty  ctx

-- 7.3.1
-- | evaluate closure, instantiating bound variable with v
valOfClosure :: Closure -> Val -> Either String Val
valOfClosure (ClosureShallow x f) v = f v
valOfClosure (ClosureDeep env x body) v = val ((x,v):env) body

val :: [(Name, Val)] -> Exp -> Either String Val
val env (Eannotate t e) = val env e
val env (Euniv) = return $ UNIV
val env (Epi x etdom etcodom) = do
  tdom <- val env etdom
  return $ PI tdom (ClosureDeep env x etcodom)
val env (Elam x ebody) = do
    return $ LAM $ ClosureDeep env x ebody
val env (Esigma x etfst etsnd) = do
    tfst <- val env etfst
    return $ SIGMA tfst (ClosureDeep env x etsnd)
val env (Econs ex exs) = do
    x <- val env ex
    xs <- val env exs
    return $ PAIR x xs
val env (Ecar ex) = do
    x <- val env ex
    doCar x
val env (Ecdr ex) = do
    x <- val env ex
    doCdr x
val env (Enat) = return $ NAT
val env (E0) = return $ ZERO
val env (Eadd1 ex) = do
    x <- val env ex
    return $ ADD1 x
val env (Eindnat etarget emotive ebase estep) = do
    target <- val env etarget
    motive <- val env emotive
    base <- val env ebase
    step <- val env estep
    doIndNat target motive base step
val env (Eeq ety efrom eto) = do
    ty <- val env ety
    from <- val env efrom
    to <- val env eto
    return $ EQ ty from to
val env (Esame) = return $ SAME
val env (Ereplace etarget emotive ebase) = do 
    target <- val env etarget
    motive <- val env emotive
    base <- val env ebase
    doReplace target motive base
val env (Etrivial) = return $ TRIVIAL
val env (Esole) = return $ SOLE
val env (Eabsurd) = return $ ABSURD
val env (Eindabsurd etarget emotive) = do
    target <- val env etarget
    motive <- val env emotive
    doIndAbsurd target motive
val env (Eatom) = return $ ATOM
val env (Equote e) = return $ QUOTE e
      
doAp :: Val -> Val -> Either String Val
doAp (LAM c) arg = valOfClosure c arg
-- | why is PI a NEU? Is it because it can only occur as a TYPE of something?
doAp (NEU (PI ti toclosure) piInhabitantv) arg = do 
  to <- valOfClosure toclosure arg
  return $ NEU to (Nap piInhabitantv (TyAndVal ti arg))


doCar:: Val -> Either String Val
doCar (PAIR a d) = return a
doCar (NEU (SIGMA ta _) v) = 
    return $ NEU ta (Ncar v)

doCdr :: Val -> Either String Val
doCdr v = error "unimplemented"

-- | Because every absurd is neutral (why?)
-- (is it because it has no constructors?)
-- | is ABSURD a type of a value?
-- | TODO: I don't understand the below declaration.
doIndAbsurd :: Val -> Val -> Either String Val
doIndAbsurd (NEU (ABSURD) ne) motive = 
  return $ NEU motive (Nindabsurd ne (TyAndVal UNIV motive))

-- | When equality is same, both sides are returned as is
doReplace :: Val -- target 
          -> Val -- motive
          -> Val -- base
          -> Either String Val
doReplace (SAME) motive base = return base
doReplace (NEU (EQ tA from to) neutvtarget) motive base = do
    tto <- doAp motive to
    tfrom <- doAp motive from
    return $ NEU tto $ Nreplace neutvtarget 
      (TyAndVal (PI tA (ClosureShallow "x" $ \_ -> return UNIV)) motive)
      (TyAndVal tfrom base)

-- | Motive -> final type
-- Π (n: nat) -> |(m n)  -> m (n + 1)
--               | ^^lhs |   ^^^^rhs  |
indNatStepType :: Val -> Val
indNatStepType motive = 
  PI NAT $ ClosureShallow "n" $ \n -> do
             lhs <- (doAp motive n)
             -- | TODO: why is this a closure? Why can't this be
             -- rhs <- doAp motive (ADD1 n)
             let rhs = ClosureShallow  "_" $ \_ -> doAp motive (ADD1 n)
             return $ PI lhs rhs


doIndNat :: Val -> Val -> Val -> Val -> Either String Val
-- doIndNat target motive base step = 
doIndNat ZERO motive base step = return $ base
doIndNat (ADD1 n) motive base step = do 
    -- step N _
    stepN_ <- doAp step n
    indn <- doIndNat n motive base step
    doAp stepN_ indn
doIndNat target@(NEU NAT neutv) motive base step = do
    retty <- doAp motive target
    let motive' = TyAndVal (PI NAT (ClosureShallow "x" $ \_ -> return UNIV)) motive
    motive0 <- doAp motive ZERO
    let base' = TyAndVal motive0 base
    let step' = TyAndVal (indNatStepType motive) step
    return $ NEU retty $ Nindnat neutv motive' base' step'


-- 7.3.3 READING BACK
fresh :: [Name] -> Name -> Name
fresh used x = 
  case find (== x) used of
    Just _ -> fresh used (x <> "*")
    Nothing -> x

readbackVal :: [(Name, Type)] -> Type -> Val -> Either String Exp
-- | NAT
readbackVal ctx NAT ZERO = return E0
readbackVal ctx NAT (ADD1 n) = do
    en <- readbackVal ctx NAT n
    return $ Eadd1 en
readbackVal ctx (PI ta a2tb) f = do
    -- | get closure argument name
    let aident = fresh (map fst ctx) (closureArgumentName a2tb)
    let aval = NEU ta (Nvar aident)
    -- | notice how data is propagated at both value and type level
    -- AT THE SAME TIME!
    tb <- valOfClosure a2tb aval
    fout <- doAp f aval
    expr_fout <- readbackVal ((aident,ta):ctx) tb fout
    return $ Elam aident expr_fout
readbackVal ctx (SIGMA ta a2tb) p = do
    -- | get closure argument name
    car <- doCar p
    cdr <- doCdr p
    tb <- valOfClosure a2tb car

    ecar <- readbackVal ctx ta car
    ecdr <- readbackVal ctx tb cdr
    return $ Econs ecar ecdr
-- | type-directed: sole inhabitant of TRIVIAL is SOLE
readbackVal ctx TRIVIAL _ = return $ Esole
-- | TODO: absurd can only be neutral (why?)
readbackVal ctx ABSURD (NEU ABSURD nv) = do 
    readbackNeutral ctx nv
readbackVal ctx (EQ tA from to) (SAME) = return Esame
readbackVal ctx ATOM (QUOTE x) = return $ Equote x
readbackVal ctx UNIV NAT = return Enat
readbackVal ctx UNIV ATOM = return Eatom
readbackVal ctx UNIV TRIVIAL = return Etrivial
readbackVal ctx UNIV ABSURD = return Eabsurd
readbackVal ctx UNIV (EQ tA from to) = do
    etA <- readbackVal ctx UNIV tA
    efrom <- readbackVal ctx tA from
    eto   <- readbackVal ctx tA to
    return $ Eeq etA efrom eto
readbackVal ctx UNIV (SIGMA ta a2tb) = do
    eta <- readbackVal ctx UNIV ta
    let aident = fresh (map fst ctx) (closureArgumentName a2tb)
    let aval = NEU ta (Nvar aident)
    tb <- valOfClosure a2tb aval
    etb <- readbackVal ((aident,ta):ctx) UNIV tb
    return $ Esigma aident eta etb
-- | exactly the same as sigma.
readbackVal ctx UNIV (PI ta a2tb) = do
    eta <- readbackVal ctx UNIV ta
    let aident = fresh (map fst ctx) (closureArgumentName a2tb)
    let aval = NEU ta (Nvar aident)
    tb <- valOfClosure a2tb aval
    etb <- readbackVal ((aident,ta):ctx) UNIV tb
    return $ Epi aident eta etb
readbackVal ctx t1 (NEU t2 ne) = readbackNeutral ctx ne
-- | Inconsistent theory? x(
-- How to exhibit inconsistence given Univ: Univ?
readbackVal ctx UNIV UNIV = return $ Euniv

-- | Read back a neutral expression as syntax.
-- | users are:
--     readbackVal Absurd
readbackNeutral :: [(Name, Type)] -> Neutral -> Either String Exp
readbackNeutral ctx (Nvar x) = return $ Eident x
readbackNeutral ctx (Nap nf (TyAndVal nxty nx)) = do
  ef <- readbackNeutral ctx nf
  ex <- readbackVal ctx nxty nx
  return $ Eap ef ex
readbackNeutral ctx (Ncar nv) = do
    ev <- readbackNeutral ctx nv
    return $ Ecar ev
readbackNeutral ctx (Ncdr nv) = do
    ev <- readbackNeutral ctx nv
    return $ Ecdr ev
readbackNeutral ctx (Nindnat target
                    (TyAndVal tmotive vmotive)
                    (TyAndVal tbase vbase)
                    (TyAndVal tstep vstep)) = do
    etarget <- readbackNeutral ctx target
    emotive <- readbackVal ctx tmotive vmotive
    ebase <- readbackVal ctx tbase vbase
    estep <- readbackVal ctx tstep vstep
    return $ Eindnat etarget emotive ebase estep 
readbackNeutral ctx (Nreplace target
                    (TyAndVal tmotive vmotive)
                    (TyAndVal tbase vbase)) = do
    etarget <- readbackNeutral ctx target
    emotive <- readbackVal ctx tmotive vmotive
    ebase <- readbackVal ctx tbase vbase
    return $ Ereplace etarget emotive ebase 
readbackNeutral ctx (Nindabsurd target
                    (TyAndVal tmotive vmotive)) = do
    etarget <- readbackNeutral ctx target
    emotive <- readbackVal ctx tmotive vmotive
    return $ Eindabsurd etarget emotive 


-- 7.4: type checking.

-- When examining types, looking for specific type constructors, the type
-- checker matches against their values. This ensures that the type checker
-- never forgets to normalize before checking, which could lead to types
-- that contain unrealized computation not being properly matche


-- | FML, do I need a monad transformer here.
synth :: [(Name, Type)] -> Exp -> Either String [Exp]
check :: [(Name, Type)] -> Exp -> Val -> Either String Exp
synth = undefined
check = undefined
