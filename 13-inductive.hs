-- NBE for dependently typed language.
-- More of the same =) 
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances #-}
import Prelude hiding(EQ)
import System.Environment
import System.Exit
import Debug.Trace
import Data.List
import Data.Either
import qualified Control.Monad as M
import qualified Data.List as L
import Control.Monad(foldM, forM)


-- generating the correct motive for inductives.


-- 7. Dependently typed lang
-- http://davidchristiansen.dk/tutorials/nbe/

instance MonadFail (Either Error) where
    fail s = Left (Error dummySpan s)

type Name = String


-- TODO: HOW TO PROVE GALOIS CORRESPONDENCE BETWEEN STX AND SEM?

-- data TYPE = Tnat | Tarrow TYPE TYPE deriving(Eq, Ord)

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
--   replace :: (X: U) ->
--      (from: X) ->
--      (to: X) ->
--      (target: = X from to) ->
--      (mot: X -> U)
--      (base: mot from) -> mot to
--
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


type InductiveName = String
type CtorName = String

-- A sequence of binders
type TelescopeExp = [(Name, Type)]

-- | Definition of an InductiveDef type.
-- https://hal.inria.fr/hal-01094195/document
data InductiveDef = InductiveDef {
  inductiveDefName :: InductiveName -- name of the inductive
  , inductiveIndexes :: TelescopeExp -- types of indexes
  , inductiveCtors :: [InductiveCtor]
} deriving(Eq, Show)

-- Constructor for inductive types
data InductiveCtor = InductiveCtor {
  ctorParentName :: InductiveName -- name of the inductive type.
  , ctorName :: CtorName -- name of the constructor.
  , ctorTelescope :: TelescopeExp -- telescope of arguments.
  , ctorIndexes :: Exp -- indexes of the inductive type built by the constructor
} deriving(Eq, Show)



-- Don't call stuff "scrutinee", call stuff "motive"!
data Exp =
    Elam Name Exp  -- intro Π: (λ f x)
  | Epi Name Exp Exp -- type: (Π [x tdom] tran)
  | Eap Exp Exp -- elim Π: ($ f x)
  | Esigma Name Exp Exp -- type: [Σ [x tfst] tsnd]
  | Econs Exp Exp -- intro: (x, v)
  | Ecar Exp  -- elim: (x, y) -> x
  | Ecdr Exp -- elim: (x, y) -> y
  | Enat -- type: Nat
  | E0 -- intro: 0
  | Eadd1 Exp -- intro: +1
  | Eindnat Exp Exp Exp Exp -- elim: (ind-nat <target> <motive> <base> <step>)
  | Eeq Exp Exp Exp -- type: (= ty a b)
  | Esame -- intro: (= ty a b)
  | Ereplace Exp Exp Exp  -- elim: (replace <target> <motive> <base>)
  | Etrivial -- type: Unit/Trivial
  | Esole -- intro:  (sole inhabitant of unit) ◊=sole : Unit=Trivial
  | Eabsurd -- type: absurd/Void
  | Eindabsurd Exp Exp  -- elim absurd: (ind-absurd <target> <motive>)
  | Eatom -- type: Atom
  | Equote Exp -- intro: atom
  | Euniv -- U
  | Eident String -- x
  | Eannotate Exp Exp -- annotation: type exp
  | Emk Name [Exp] -- call a constructor: (mk <name> <arg>*)
  | Eind Name [Exp] -- inductive type: (ind <name> <index>*)
  | Eelim Name Exp Exp [Exp] -- eliminator: (elim <name> <val> <motive> <args>)
  deriving(Eq, Ord)
type Type = Exp

-- | Check if expression is a simple expression with no data,
-- so like a keyword
expIsKeyword :: Exp -> Bool
expIsKeyword Euniv = True
expIsKeyword Esame = True
expIsKeyword Etrivial = True
expIsKeyword Esole = True
expIsKeyword Eabsurd = True
expIsKeyword Eatom = True
expIsKeyword Enat = True
expIsKeyword _ = False

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

-- | Quote are just variables.
alphaEquivGo (Equote x) (Equote x') _ _ n = (x == x', n)
alphaEquivGo (Econs op args) (Econs op' args') _ _ n =
    error $ "unimplemented α equivalence for cons"

-- | This, together with read-back-norm, implements the η law for Absurd.
alphaEquivGo (Eannotate t Eabsurd) (Eannotate t' Eabsurd) _ _ n = (True, n)

alphaEquivGo e e' _ _ n = (expIsKeyword e && e == e', n)

instance Show Exp where
  show (Elam name exp) = "(λ " <> name <> " " <> show exp <> ")"
  show (Epi name dom codom) =
    "(Π " <> name <> " " <> show dom <> " " <> show codom <> ")"
  show (Eap f x) =
    "($ " <> show f <> " " <> show x <> ")"
  show (Esigma name dom codom) =
    "(Σ " <> name <> " " <> show dom <> " " <> show codom <> ")"
  show (Econs x y) =
    "(cons " <> show x <> " " <> show y <> ")"
  show (Ecar e) =
    "(car " <> show e <> ")"
  show (Ecdr e) =
    "(cdr " <> show e <> ")"
  show Enat = "nat"
  show (E0) = "0"
  show (Eadd1 x) = "(+1 " <> show x <> ")"
  show (Eindnat target motive base step) =
    "(ind-nat " <>
     show target <> " " <>
     show motive <> " " <>
     show base <> " " <>
     show step <> ")"
  show (Eeq t from to) =
      "(= " <> show t <> " " <> show from <> show to <> ")"
  show (Esame) = "same"
  show (Ereplace target motive base) =
      "(replace " <>
      show target <> " " <>
      show motive <> " " <>
      show base <> ")"
  show Etrivial = "trivial"
  show Esole = "sole"
  show Eabsurd = "absurd"
  show Eatom = "atom"
  show (Equote e) = "('" <> show e <> ")"
  show Euniv = "univ"
  show (Eident name) = name
  show (Eannotate t e) = "(∈ " <> show t <> " " <> show e <> ")"
  -- show (Erec t target base step) = "(rec " <> show target <> " " <> show base <> " " <> show step <> ")"
type Choice = (String, Exp)


elaborateExp :: AST -> Either Error Exp
elaborateExp (Atom span "0") = Right $ E0
elaborateExp (Atom span "nat") = Right $ Enat
elaborateExp (Atom span ident) = Right $ Eident ident
elaborateExp tuple = do
  head  <- tuplehd atom tuple
  case head of
    "λ" -> do
      ((), x, body) <- tuple3f astignore atom elaborateExp tuple
      return $ Elam x body
    "$" -> do
      ((), f, x) <- tuple3f astignore elaborateExp elaborateExp tuple
      return $ Eap f x
    "∈" -> do
      ((), t, e) <- tuple3f astignore elaborateExp elaborateExp tuple
      return $ Eannotate t e
    ":" -> do
      ((), t, e) <- tuple3f astignore elaborateExp elaborateExp tuple
      return $ Eannotate t e
    "+1" -> do
      ((), e) <- tuple2f astignore elaborateExp tuple
      return $ Eadd1 e
    "→" -> do
      ((), ti, to) <- tuple3f astignore elaborateExp elaborateExp tuple
      return $ Epi "_" ti to
    "ind-nat" -> do
        ((), target, motive, base, step) <- tuple5f
            astignore elaborateExp elaborateExp elaborateExp elaborateExp tuple
        return $ Eindnat target motive base step
    "ind" -> do
      name <- atomget <$> at 1 tuple
      args <- unTuple <$> astDrop 2 tuple
      args <- forM args elaborateExp -- elaborate the arguments
      return $ Eind name args
    "mk" -> do
      name <- atomget <$> at 1 tuple
      args <- unTuple <$> astDrop 2 tuple
      args <- forM args elaborateExp -- elaborate the arguments
      return $ Emk name args
    "elim" -> do
      name <- atomget <$> at 1 tuple
      val <- at 2 tuple >>= elaborateExp
      motive <- at 3 tuple >>= elaborateExp
      args <- unTuple <$> astDrop 4 tuple
      args <- forM args elaborateExp -- elaborate the arguments
      return $ Eelim name val motive args
    _ -> Left $ Error (astSpan tuple) $ "unknown special form |" ++ head ++
                  "| in " ++ "|" ++ astPretty tuple ++ "|"


elaborateInductiveDef :: AST -> Either Error InductiveDef
elaborateInductiveDef ast = Left $ Error dummySpan "elaborating inductive"

elaborateToplevel :: AST -> Either Error ([InductiveDef], [(Name, Exp)])
elaborateToplevel tuple = do
  head  <- tuplehd atom tuple
  tail <- astDrop 1 tuple
  case head of
    "def" -> do
      (name, exp) <- tuple2f atom elaborateExp tail
      return ([], [(name, exp)])
    "ind" -> do
      ind <- elaborateInductiveDef tail
      return $ ([ind], [])

foldM' :: (Monad m, Traversable t) =>
  s -> t a -> (s -> a -> m s) -> m s
foldM' s t f = foldM f s t

main_ :: String -> IO ()
main_ path = do
  file <- readFile path
  putStrLn $ "file contents:"
  putStrLn $ file
  putStrLn $ "parsing..."
  ast <- case parse file of
           Left failure -> putStrLn (showError failure file) >> exitFailure
           Right success -> pure success
  putStrLn $ astPretty ast

  putStrLn $ "convering to intermediate repr..."
  (inductives, decls) <- case tupleFoldMap elaborateToplevel ast of
            Left failure -> putStrLn (showError failure file) >> exitFailure
            Right d -> pure d

  putStrLn $ "processing inductives..."
  ctx <- foldM' CtxEmpty inductives $ \ctx ind -> do
           putStrLn $ "***" <> show ind 
           return (CtxInductiveDef ind ctx)
  putStrLn $ "type checking and evaluating..."
  ctx <- foldM' ctx decls $ \ctx (name, exp) -> do
        putStrLn $ "***" <> name <> ": " <> show exp <> "***"
        putStrLn $ "\t+elaborating..."
        (te, exp') <- case synth ctx exp of
               Left failure -> putStrLn (showError failure file) >> exitFailure
               Right (Eannotate te exp') -> pure (te, exp')
               Right notEannotate -> do
                   putStrLn $ "expected Eannotate from synth, " <>
                       "found |" <> show notEannotate <> "|."
                   exitFailure

        putStrLn $ "\t+elaborated: " <> show (Eannotate te exp')
        putStr $ "\t+Evaluating type..."
        tv <- case val (ctxEnv ctx) te of
                Left failure -> putStrLn "***ERR***" >> putStrLn (showError failure file) >> exitFailure
                Right tv -> pure tv
        -- putStrLn $ "\t+type-v: " <> show tv
        putStr $ "OK. "
        putStr $ "Evaluating value..."
        v <- case val (ctxEnv ctx) exp' of
                 Left failure -> putStrLn (showError failure file) >> exitFailure
                 Right v -> pure v
        putStr $ "OK."
        putStr $ " Reading back..."
        vexp <- case  readbackVal ctx tv v of
                 Left failure -> putStrLn (showError failure file) >> exitFailure
                 Right vexp -> pure vexp
        putStr $ "OK.\n"
        putStrLn $ "\t+FINAL: " <> show vexp
        return (CtxDef name tv v ctx)
  return ()

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
          [path] -> pure path
          _ -> (putStrLn "expected single file path to parse") >> exitFailure
  main_ path


errTyMismatch :: (Exp, TYPE) -> TYPE -> String
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
    PAIR TYPE TYPE |
    ZERO |
    ADD1 Val |
    EQ TYPE Val Val | -- Eq type from to
    SAME |
    TRIVIAL |
    SOLE |
    ABSURD |
    ATOM |
    QUOTE Exp | -- I really don't know what symbol? is
    UNIV |
    IND_TY InductiveDef |
    NEU TYPE Neutral -- NEU type neutral data
    deriving(Show)

type TYPE = Val

-- | the embedding is shallow because it's used by shallow people in a hurry
-- who don't want to deal with binders!
data Closure =
    ClosureShallow Name (Val -> Either Error Val) |
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


data TY_VAL = TY_VAL TYPE Val deriving(Show)
--- | The thing at the "to be reduced" position is stuck
data Neutral =
    Nvar Name
  | Nap Neutral TY_VAL
  | Ncar Neutral
  | Ncdr Neutral
  | Nindnat Neutral TY_VAL TY_VAL TY_VAL -- target motive base step
  -- | what does replace eliminate? EQ?
  | Nreplace Neutral TY_VAL TY_VAL -- target motive base
  | Nindabsurd Neutral TY_VAL -- target motive
  deriving(Show)

data Ctx = CtxEmpty
  | CtxDef Name TYPE Val Ctx
  | CtxBind Name TYPE Ctx
  | CtxInductiveDef InductiveDef Ctx


instance Show Ctx where
    show (CtxEmpty) = "[]"
    show (CtxDef n t v ctx') = show n <> show ":" <> show t <> "=" <> show v <> "; " <> show ctx'
    show (CtxBind n t ctx') = show n <> show ":" <> show t <> "; " <> show ctx'
    show (CtxInductiveDef def ctx') = show def <> "; " <> show ctx'

ctxLookupTYPE :: Ctx -> Name -> Maybe Val
ctxLookupTYPE (CtxEmpty) _ = Nothing
ctxLookupTYPE (CtxDef n t _ ctx') name =
    if n == name then Just t else ctxLookupTYPE ctx' name
ctxLookupTYPE (CtxBind n t ctx') name =
    if n == name then Just t else ctxLookupTYPE ctx' name
ctxLookupTYPE (CtxInductiveDef def ctx') name =
    if name == inductiveDefName def then Just (IND_TY def) else ctxLookupTYPE ctx' name

type Environment = [(Name, Val)]
ctxEnv :: Ctx -> Environment
ctxEnv CtxEmpty = []
ctxEnv (CtxDef n t v ctx') = (n,v):ctxEnv ctx'
ctxEnv (CtxBind n t ctx') = (n, NEU t (Nvar n)):ctxEnv ctx'
ctxEnv (CtxInductiveDef ind ctx') = ctxEnv ctx'

ctxExtend :: Ctx -> Name -> TYPE -> Ctx
ctxExtend ctx name ty = CtxBind name ty ctx

-- 7.3.1
-- | evaluate closure, instantiating bound variable with v
valOfClosure :: Closure -> Val -> Either Error Val
valOfClosure (ClosureShallow x f) v = f v
valOfClosure (ClosureDeep env x body) v = val ((x,v):env) body


val :: Environment -> Exp -> Either Error Val
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
val env (Eident n) =
  case lookup n env of
    Just v -> Right v
    Nothing -> Left $ Error dummySpan $ "unknown variable |" <> n <> "|"
val env (Eap f x) = do
    vf <- val env f
    vx <- val env x
    doAp vf vx
-- val env e = Left $ Error dummySpan $ "unknown expression for val: |" <> show e <> "|"

doAp :: Val -> Val -> Either Error Val
doAp (LAM c) arg = valOfClosure c arg
-- | why is PI a NEU? Is it because it can only occur as a TYPE of something?
doAp (NEU (PI ti toclosure) piInhabitantv) arg = do
  to <- valOfClosure toclosure arg
  return $ NEU to (Nap piInhabitantv (TY_VAL ti arg))
doAp v arg =
    Left $ Error dummySpan $ "ERR: illegal application of |" <> show v <> "|" <>
            " to |" <> show arg <> "|."


doCar:: Val -> Either Error Val
doCar (PAIR a d) = return a
doCar (NEU (SIGMA ta _) v) =
    return $ NEU ta (Ncar v)

doCdr :: Val -> Either Error Val
doCdr v = error "unimplemented"

-- | Because every absurd is neutral (why?)
-- (is it because it has no constructors?)
-- | is ABSURD a type of a value?
-- | TODO: I don't understand the below declaration.
doIndAbsurd :: Val -> Val -> Either Error Val
doIndAbsurd (NEU (ABSURD) ne) motive =
  return $ NEU motive (Nindabsurd ne (TY_VAL UNIV motive))

-- | When equality is same, both sides are returned as is
doReplace :: Val -- target
          -> Val -- motive
          -> Val -- base
          -> Either Error Val
doReplace (SAME) motive base = return base
doReplace (NEU (EQ tA from to) neutvtarget) motive base = do
    tto <- doAp motive to
    tfrom <- doAp motive from
    return $ NEU tto $ Nreplace neutvtarget
      (TY_VAL (PI tA (ClosureShallow "x" $ \_ -> return UNIV)) motive)
      (TY_VAL tfrom base)

-- | Motive -> final type
-- Π (n: nat) -> |(m n)  -> m (n + 1)
--               | ^^lhs |   ^^^^rhs  |
indNatStepTYPE :: Val -> Val
indNatStepTYPE motive =
  PI NAT $ ClosureShallow "n" $ \n -> do
             lhs <- (doAp motive n)
             -- | TODO: why is this a closure? Why can't this be
             -- rhs <- doAp motive (ADD1 n)
             let rhs = ClosureShallow  "_" $ \_ -> doAp motive (ADD1 n)
             return $ PI lhs rhs


doIndNat :: Val -> Val -> Val -> Val -> Either Error Val
-- doIndNat target motive base step =
doIndNat ZERO motive base step = return $ base
doIndNat (ADD1 n) motive base step = do
    -- step N _
    stepN_ <- doAp step n
    indn <- doIndNat n motive base step
    doAp stepN_ indn
doIndNat target@(NEU NAT neutv) motive base step = do
    retty <- doAp motive target
    let motive' = TY_VAL (PI NAT (ClosureShallow "x" $ \_ -> return UNIV)) motive
    motive0 <- doAp motive ZERO
    let base' = TY_VAL motive0 base
    let step' = TY_VAL (indNatStepTYPE motive) step
    return $ NEU retty $ Nindnat neutv motive' base' step'


-- 7.3.3 READING BACK

fresh :: [Name] -> Name -> Name
fresh used x =
  case find (== x) used of
    Just _ -> fresh used (x <> "*")
    Nothing -> x

ctxNames :: Ctx -> [Name]
ctxNames CtxEmpty = []
ctxNames (CtxBind n t ctx')  = n:ctxNames ctx'
ctxNames (CtxDef n t v ctx')  = n:ctxNames ctx'

ctxFresh :: Ctx -> Name -> Name
ctxFresh ctx name = fresh (ctxNames ctx) name

readbackVal :: Ctx -> TYPE -> Val -> Either Error Exp

-- | NAT
readbackVal ctx NAT ZERO = return E0
readbackVal ctx NAT (ADD1 n) = do
    en <- readbackVal ctx NAT n
    return $ Eadd1 en
readbackVal ctx (PI ta a2tb) f = do
    -- | get closure argument name
    let aident = ctxFresh ctx (closureArgumentName a2tb)
    let aval = NEU ta (Nvar aident)
    -- | notice how data is propagated at both value and type level
    -- AT THE SAME TIME!
    tb <- valOfClosure a2tb aval
    fout <- doAp f aval
    expr_fout <- readbackVal (ctxExtend ctx aident ta) tb fout
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
    let aident = ctxFresh ctx (closureArgumentName a2tb)
    let aval = NEU ta (Nvar aident)
    tb <- valOfClosure a2tb aval
    etb <- readbackVal (ctxExtend ctx aident ta) UNIV tb
    return $ Esigma aident eta etb
-- | exactly the same as sigma.
readbackVal ctx UNIV (PI ta a2tb) = do
    eta <- readbackVal ctx UNIV ta
    let aident = ctxFresh ctx (closureArgumentName a2tb)
    let aval = NEU ta (Nvar aident)
    tb <- valOfClosure a2tb aval
    etb <- readbackVal (ctxExtend ctx aident ta) UNIV tb
    return $ Epi aident eta etb
readbackVal ctx t1 (NEU t2 ne) = readbackNeutral ctx ne
-- | Inconsistent theory? x(
-- How to exhibit inconsistence given Univ: Univ?
readbackVal ctx UNIV UNIV = return $ Euniv
readbackVal ctx t v =
    Left $ Error dummySpan $ "unknown readback |" <> show v <>  " :: " <> show t <> "|"

-- | Read back a neutral expression as syntax.
-- | users are:
--     readbackVal Absurd
readbackNeutral :: Ctx -> Neutral -> Either Error Exp
readbackNeutral ctx (Nvar x) = return $ Eident x
readbackNeutral ctx (Nap nf (TY_VAL nxty nx)) = do
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
                    (TY_VAL tmotive vmotive)
                    (TY_VAL tbase vbase)
                    (TY_VAL tstep vstep)) = do
    etarget <- readbackNeutral ctx target
    emotive <- readbackVal ctx tmotive vmotive
    ebase <- readbackVal ctx tbase vbase
    estep <- readbackVal ctx tstep vstep
    return $ Eindnat etarget emotive ebase estep
readbackNeutral ctx (Nreplace target
                    (TY_VAL tmotive vmotive)
                    (TY_VAL tbase vbase)) = do
    etarget <- readbackNeutral ctx target
    emotive <- readbackVal ctx tmotive vmotive
    ebase <- readbackVal ctx tbase vbase
    return $ Ereplace etarget emotive ebase
readbackNeutral ctx (Nindabsurd target
                    (TY_VAL tmotive vmotive)) = do
    etarget <- readbackNeutral ctx target
    emotive <- readbackVal ctx tmotive vmotive
    return $ Eindabsurd etarget emotive


-- 7.4: type checking.

-- | having NBE is vital during type checking, since we want to
-- normalize type-level terms to type check!
nbe :: Ctx -> TYPE -> Exp -> Either Error Exp
nbe ctx t e = do
    v <- val (ctxEnv ctx) e
    readbackVal ctx t v


-- When examining types, looking for specific type constructors, the type
-- checker matches against their values. This ensures that the type checker
-- never forgets to normalize before checking, which could lead to types
-- that contain unrealized computation not being properly matche

-- | FML, do I need a monad transformer here.
-- | will always return an annotated expression
-- elaborated expr = expr + annotation.
-- I believe we need to return this as just Exp, where we are guaranteed
-- that Exp will be Eannotate. We can't return a tuple (TYPE, Exp)
-- since check will call synth and synth will call check compositionally to
-- build new annotated ASTs.
synth :: Ctx -> Exp -> Either Error Exp
-- recall that TYPE = Val
synth ctx (Eannotate ty e) = do
    ty' <- check ctx ty UNIV -- check that ty has type universe (is at the right level)
    tyv <- val (ctxEnv ctx) ty' -- crunch what tout is
    eout <- check ctx e tyv  -- use it to check what eout is, since we can only check AGAINST a normal form.
    -- | why not read back tyv, instead of using un-normalized ty'?
    return $ (Eannotate ty' eout)
-- | why is univ synthesized? shouldn't it be checked, being a constructor? ;)
-- Univ : Univ
synth ctx Euniv = return $ Eannotate Euniv Euniv
-- | What does Esigma eliminate?
synth ctx (Esigma x ta a2tb) = do
    ta' <- check ctx ta UNIV
    tav <- val (ctxEnv ctx) ta'
    a2tb' <- check (ctxExtend ctx x tav) a2tb UNIV
    return $ Eannotate Euniv (Esigma x ta' a2tb')
-- | my implementation.
-- synth ctx (Ecar p) = do
--     tpe <- synth ctx p
--     tpe' <- nbe ctx UNIV tpe
--     tleft <- case tpe' of
--             Esigma x tleft tright -> return tleft
--             _ -> Left $ "expected Ecar to be given value of Σ type." <>
--                         "Value |" <> show p <> "| " <>
--                         "has non-Σ type |" <> show tpe' <> "|"
--     return (Eannotate tleft (Ecar p))
synth ctx (Ecar p) = do
    (Eannotate pty pelab) <- synth ctx p
    ptyv <- val (ctxEnv ctx) pty
    case ptyv of
      SIGMA lv _ -> do
          le <- readbackVal ctx UNIV lv
          return (Eannotate le (Ecar pelab))
      nonSigma -> do
        ptyve <- readbackVal ctx UNIV nonSigma
        Left $ Error dummySpan $ "expected Ecar to be given value of Σ type." <>
                "Value |" <> show pelab <> "| " <>
                        "has non-Σ type |" <> show ptyve <> "|"

-- | Interesting, I need to produce a value from a closure!
synth ctx (Ecdr p) = do
    (Eannotate pty pelab) <- synth ctx p
    ptyv <- val (ctxEnv ctx) pty
    case ptyv of
      SIGMA lt rtclosure -> do
          lv <- val (ctxEnv ctx) (Ecar p)
          rt <- valOfClosure rtclosure lv
          rte <- readbackVal ctx UNIV rt
          return (Eannotate rte (Ecar pelab))
      nonSigma -> do
        ptyve <- readbackVal ctx UNIV nonSigma
        Left $ Error dummySpan $ "expected Ecar to be given value of Σ type." <>
                "Value |" <> show pelab <> "| " <>
                        "has non-Σ type |" <> show ptyve <> "|"

synth ctx (Enat) = return $ Eannotate Euniv Enat
synth ctx (Eindnat etarget emotive ebase estep) = do
    targetout <- check ctx etarget NAT
    motiveout <- check ctx emotive (PI NAT (ClosureShallow "_" $ \_ -> return UNIV))
    motivev <- val (ctxEnv ctx) motiveout
    targetv <- val (ctxEnv ctx) targetout

    baseout <- doAp motivev ZERO >>= check ctx ebase
    stepout <- check ctx estep (indNatStepTYPE motivev)

    motivetargetve <- doAp motivev targetv >>= readbackVal ctx UNIV
    return (Eannotate motivetargetve
                      (Eindnat targetout motiveout baseout stepout))

-- | introduction for equality. Why is this in synthesis mode?
synth ctx (Eeq te frome toe) = do
    tout <- check ctx te UNIV
    toutv <- val (ctxEnv ctx) tout
    fromout <- check ctx frome toutv
    toout <- check ctx toe toutv
    return $ (Eannotate Euniv (Eeq tout fromout toout))

-- | elimination  for equality
--   replace :: {X: U} ->
--      {from: X} ->
--      {to: X} ->
--      (target: = X from to) ->
--      (mot: X -> U)
--      (base: mot from) -> mot to
synth ctx (Ereplace etarget emotive ebase) = do
    (Eannotate ttarget etargetout) <- synth ctx etarget
    check ctx ttarget UNIV -- check that lives in UNIV
    -- | pattern match the equality object to learn types of motive and base
    etargetoutv <- val (ctxEnv ctx) etargetout
    (x, from, to) <- case etargetoutv of
        EQ x from to -> return (x, from, to)
        _ -> Left $ Error dummySpan $ "expected (replace  to destructure an EQ value; " <>
                  "Found | " <> show etarget <> "|"
    -- motive :: X -> UNIV
    motiveout <- check ctx emotive
                  (PI x $ ClosureShallow "_" $ \_ -> return UNIV)
    motivev <- val (ctxEnv ctx) motiveout
    baseout <- doAp motivev from >>= check ctx ebase

    toout <- doAp motivev to >>= readbackVal ctx UNIV
    return (Eannotate toout (Ereplace etargetout motiveout baseout))


-- PI = -> (DOM: UNIV) -> (x: DOM) -> (CODOM: DOM -> UNIV) -> PI (x: DOM) CODOM
-- | My incorrect implementation that almost surely looops.
-- synth ctx (Epi x edom ecodom) = do
--     domout@(Eannotate domt _) <- check ctx edom UNIV
--     domtv <- val ctx domt
--     codomout <- check ctx ecodom
--                 (PI domtv $ ClosureShallow "_" $ \_ -> return UNIV)
--     return (Eannotate Euniv (Epi x domout codomout))

synth ctx (Epi x edom ecodom) = do
    domout <- check ctx edom UNIV
    domtv <- val (ctxEnv ctx) domout
    codomout <- check (ctxExtend ctx x domtv) ecodom UNIV
    return (Eannotate Euniv (Epi x domout codomout))


synth ctx Etrivial = return (Eannotate Euniv Etrivial)
synth ctx Eabsurd = return (Eannotate Euniv Eabsurd)

-- | convert a witness of Absurd into a witness of motive.
-- Eindabsurd :: (target: Absurd) -> (motive: Univ) -> (out: motive)
synth ctx (Eindabsurd etarget emotive) = do
    targetout <- check ctx etarget ABSURD
    motiveout <- check ctx emotive UNIV
    return $ Eannotate motiveout (Eindabsurd targetout motiveout)

synth ctx Eatom = return (Eannotate Euniv Eatom)
synth ctx (Eap ef ex) = do
    (Eannotate ft fe) <- synth ctx ef
    ftv <- val (ctxEnv ctx) ft
    (tin, toutclosure) <- case ftv of
        PI tin tout -> return (tin, tout)
        notPi -> Left $ Error dummySpan $ "expected function type to be PI type at" <>
                  "|" <> show fe <> "|, found type" <>
                  "|" <> show notPi <> "|"
    xout <- check ctx ex tin
    xv <- val (ctxEnv ctx) xout
    tout <- valOfClosure toutclosure xv >>= readbackVal ctx UNIV
    return $ Eannotate tout (Eap fe xout)

synth ctx (Eident name) =
    case ctxLookupTYPE ctx name of
      Just t -> do
          te <- readbackVal ctx UNIV t
          return $ Eannotate te (Eident name)
      Nothing -> Left $ Error dummySpan $ "unknown variable |" <> name <> "|"

synth ctx e =
    Left $ Error dummySpan $  "cannot synthesize a type for expression |" <> show e <> "|"


-- | check pattern matches on the value
-- cons is checked because it is an introduction rule.
check :: Ctx -> Exp -> TYPE -> Either Error Exp
check ctx  (Econs ea ed) t = do
    (ta, tdclosure) <- case t of
      SIGMA ta tdclosure -> return (ta, tdclosure)
      notSigma -> Left $ Error dummySpan $ "expected cons to have Σ type. " <>
                   "Found |" <> show (Econs ea ed) <> "|" <>
                   "to have type |" <> show notSigma <> "|"
    aout <- check ctx ea ta
    td <- val (ctxEnv ctx) ea >>= valOfClosure tdclosure
    dout <- check ctx ed td
    return $ (Econs aout dout)
check ctx E0 t =
    case t of
     NAT -> return E0
     notNat -> Left $ Error dummySpan $ "expected zero to have type nat. " <>
                      "Found |" <> show notNat <> "|"
check ctx (Eadd1 en) t = do
    en' <- check ctx en NAT
    case t of
     NAT -> return (Eadd1 en')
     notNat -> Left $ Error dummySpan $ "expected zero to have type nat. " <>
                      "Found |" <> show notNat <> "|"

-- | same is constructor of EQ
-- | to be honest, I find this dubious. why should these be α equivalent?
-- i guess the idea is that the only inhabitant of eq is `refl`,
-- and thus their normal forms must be equal!
check ctx Esame t = do
  case t of
   (EQ t vfrom vto) -> do
      convert ctx t vfrom vto -- check that vfrom = vto
      return Esame
   noteq -> Left $ Error dummySpan $ "exected same to have type eq." <>
                    "found |" <> show noteq <> "|"

check ctx Esole t =
  case t of
    TRIVIAL -> return Esole
    notTrivial ->
      Left $ Error dummySpan $ "expected sole to have type trivial, but found type " <>
             "|" <> show notTrivial <> "|"

check ctx (Elam x body) t =
  case t of
    PI ta tbclosure -> do
        let vx = NEU ta (Nvar x)
        tb <- valOfClosure tbclosure vx
        outbody <- check (ctxExtend ctx x ta) body tb
        return $ (Elam x outbody)
    notPi ->
      Left $ Error dummySpan $ "expected lambda to have type PI, but found type " <>
             "|" <> show notPi <> "|"

-- quote constructs atom
check ctx (Equote x) t =
  case t of
    ATOM -> return $ (Equote x)
    notAtom ->
      Left $ Error dummySpan $ "expected quote to have type Atom, but found type " <>
             "|" <> show notAtom <> "|"


-- | generic check fallback
check ctx e texpectedv = do
    eout@(Eannotate te _) <- synth ctx e
    tev <- val (ctxEnv ctx) te
    -- | check that the types are equal.
    case convert ctx UNIV tev texpectedv of
      Right () -> pure ()
      Left err -> do
        Left $ Error (errSpan err) $ "check |" <> show  eout <> "| : " <>
                "|" <> show tev <> "|" <> " =? " <>
                "|" <> show texpectedv  <> " [expected]|" <>
                " failed: " <> errString err
    return $ eout

-- convert t v1 v2 = ...
convert :: Ctx -> Val -> Val -> Val -> Either Error ()
convert ctx t v1 v2 = do
    e1 <- readbackVal ctx t v1
    e2 <- readbackVal ctx t v2
    case alphaEquiv e1 e2 of
      True -> return ()
      False -> Left $ Error dummySpan $ "expected α equivalence between " <>
                      "|" <> show e1 <> "| and " <>
                      "|" <> show e2 <> "|."
-- === AST ===
-- === AST ===
-- === AST ===

data Error = Error {
  errSpan :: Span
  , errString :: String
}

dummyLoc :: Loc
dummyLoc = Loc 0 1 0

dummySpan :: Span
dummySpan = Span dummyLoc dummyLoc


showLoc :: Loc -> String
showLoc (Loc ix line col) = show line <> ":" <> show col

showSpan :: Span -> String
showSpan (Span l r) = showLoc l <> "-" <> showLoc r

showError :: Error -> String -> String
showError (Error span str) file =
  showSpan span <> "\n" <> show str


data Loc =
  Loc { locix :: Int, locline :: Int, loccol :: Int } deriving(Eq)

instance Show Loc where
  show (Loc ix line col) = "Loc(" ++ show line ++ ":" ++ show col ++ " " ++ show ix ++ ")"

errAtLoc :: Loc -> String  -> Error
errAtLoc l err = Error (Span l l) err

errAtSpan :: Span -> String  -> Error
errAtSpan s err = Error s err

data Span = Span { spanl :: Loc, spanr :: Loc } deriving(Eq)

instance Show Span where
  show (Span l r) = "Span(" ++ show l ++ " " ++ show r ++ ")"


data Delimiter = Round | Square | Flower deriving(Eq, Show)

data Token = Open Span Delimiter | Close Span Delimiter | Str Span String deriving(Show)

-- The Char of a tuple carries what the open bracket looks like.
data AST =
    Tuple {
      astspan :: Span,
      tupledelimiter :: Delimiter,
      unTuple :: [AST]
    } |
    Atom {
      astspan :: Span,
      atomget :: String
    } deriving (Show)

delimOpen :: Delimiter -> String
delimOpen Round = "("
delimOpen Square = "["
delimOpen Flower = "{"

delimClose Round = ")"
delimClose Square = "]"
delimClose Flower = "}"


astPretty :: AST -> String
astPretty (Atom _ l) = l
astPretty (Tuple _ delim ls) =
  delimOpen delim ++ L.intercalate " " (map astPretty ls) ++ delimClose delim

astSpan :: AST -> Span
astSpan (Tuple span _ _) = span
astSpan (Atom span _) = span

spanExtend :: Span -> Span -> Span
spanExtend (Span l r) (Span l' r') = Span l r'


locNextCol :: Loc -> Loc
locNextCol (Loc ix line col) = Loc (ix+1) line (col+1)

locNextCols :: Int -> Loc -> Loc
locNextCols n (Loc ix line col) = Loc (ix+n) line (col+n)

locNextLine :: Loc -> Loc
locNextLine (Loc ix line col) = Loc (ix+1) (line+1) 1

isSigil :: Char -> Bool
isSigil '(' = True
isSigil ')' = True
isSigil '[' = True
isSigil ']' = True
isSigil '{' = True
isSigil '}' = True
isSigil ' ' = True
isSigil '\n' = True
isSigil '\t' = True
isSigil _ = False

tokenize :: Loc -> String -> [Token]
tokenize l [] = []
tokenize l ('\n':cs) = tokenize (locNextLine l) cs
tokenize l ('\t':cs) = tokenize (locNextCol l) cs
tokenize l (' ':cs) = tokenize (locNextCol l) cs

tokenize l ('(':cs) =
    let l' =  locNextCol l; span = Span l l'
    in (Open span Round):tokenize l' cs
tokenize l (')':cs) =
    let l' = locNextCol l; span = Span l l'
    in (Close span Round):tokenize l' cs

tokenize l ('[':cs) =
    let l' =  locNextCol l; span = Span l l'
    in (Open span Square):tokenize l' cs
tokenize l (']':cs) =
    let l' = locNextCol l; span = Span l l'
    in (Close span Square):tokenize l' cs

tokenize l ('{':cs) =
    let l' =  locNextCol l; span = Span l l'
    in (Open span Flower):tokenize l' cs
tokenize l ('}':cs) =
    let l' = locNextCol l; span = Span l l'
    in (Close span Flower):tokenize l' cs


tokenize l cs =
    let (lex, cs') = L.span (not . isSigil) cs
        l' = locNextCols (length lex) l
        span = Span l l'
    in (Str span lex):tokenize l' cs'

tupleAppend :: AST -> AST -> AST
tupleAppend (Atom _ _) s = error $ "cannot push into atom"
tupleAppend (Tuple span delim ss) s = Tuple (spanExtend span (astSpan s)) delim (ss ++ [s])

-- | invariant: stack, top only contain `Tuple`s.
doparse :: [Token] -- ^ stream of tokens
  -> AST -- ^ currently building AST
  ->  [AST] -- ^ stack of AST
  -> Either Error AST  -- final AST
doparse [] cur [] = Right cur
doparse [] cur (top:stack') =
  Left $ Error (astSpan top) "unclosed open bracket."
doparse ((Open span delim):ts) cur stack =
  doparse ts (Tuple span delim [])  (cur:stack) -- open new tuple
doparse ((Close span delim):ts) cur stack =
  if tupledelimiter cur == delim -- we close the current thing correctly
  then case stack of  -- pop stack, and append cur into top, make top cur
            (top:stack') -> doparse ts (tupleAppend top cur) stack'
            [] -> Left $ Error span "too many close parens."
  else Left $ Error (astSpan cur) $ "mismatched bracket (open) " ++
              "'" ++ (delimOpen (tupledelimiter cur)) ++ "'" ++
              "; " ++ "mismatched bracket (close) " ++
              "'" ++ (delimClose delim) ++ "'"

doparse ((Str span str):ts) cur stack =
  doparse ts (tupleAppend cur (Atom span str)) stack -- append into tuple

-- | parse a string
parse :: String -> Either Error AST
parse s =
  let locBegin = Loc 0 1 1
      spanBegin = Span locBegin locBegin
  in doparse (tokenize locBegin s) (Tuple spanBegin Flower []) []


astDrop :: Int -> AST -> Either Error AST
astDrop len (Atom span _) =
 Left $ errAtSpan span $ "expected to tuple, found atom"
astDrop len (Tuple span delim xs) =
  return $ Tuple (Span locLeft locRight) delim (drop len xs)
  where
   xs' = drop len xs
   locRight = spanr span
   locLeft = case xs' of
              [] -> locRight
              (x : _) -> spanl $ astSpan x

at :: Int -> AST -> Either Error AST
at ix (Atom span _) =
 Left $ Error span $
   "expected tuple index " ++ show ix ++
   ". Found atom. "
at ix (Tuple span _ xs) =
  if length xs < ix
  then Left $ Error span $
    "expected tuple index " ++ show ix ++
    ". Found tuple of smaller length: "  ++ show (length xs)
  else return (xs !! ix)

atom :: AST -> Either Error String
atom t@(Tuple span _ xs) =
  Left $ Error span $
    "expected atom, found tuple.\n" ++ astPretty t
atom (Atom span a) = return a

tuple :: Int -> AST -> Either Error [AST]
tuple n (Atom span atom) =
  Left $ Error span $ "expected tuple of length " ++ show n ++
         ". found atom " ++ show atom
tuple n ast@(Tuple span _ xs) =
 if length xs /= n
 then Left $ Error span $
    "expected tuple of length " ++ show n ++
    ". found tuple of length " ++ show (length xs)  ++
    " |" ++ astPretty ast ++ "|."
 else Right xs

tuple4 :: AST -> Either Error (AST, AST, AST, AST)
tuple4 ast = do
    xs <- tuple 4 ast
    return (xs !! 0, xs !! 1, xs !! 2, xs !! 3)

-- | functional version of tuple 2
tuple2f :: (AST -> Either Error a0)
    -> (AST -> Either Error a1)
    -> AST -> Either Error (a0, a1)
tuple2f f0 f1 ast = do
    xs <- tuple 2 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    return (a0, a1)

-- | functional version of tuple 3
tuple3f :: (AST -> Either Error a0)
    -> (AST -> Either Error a1)
    -> (AST -> Either Error a2)
    -> AST -> Either Error (a0, a1, a2)
tuple3f f0 f1 f2 ast = do
    xs <- tuple 3 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    a2 <- f2 (xs !! 2)
    return (a0, a1, a2)

-- | functional version of tuple 4
tuple4f :: (AST -> Either Error a0)
    -> (AST -> Either Error a1)
    -> (AST -> Either Error a2)
    -> (AST -> Either Error a3)
    -> AST -> Either Error (a0, a1, a2, a3)
tuple4f f0 f1 f2 f3 ast = do
    xs <- tuple 4 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    a2 <- f2 (xs !! 2)
    a3 <- f3 (xs !! 3)
    return (a0, a1, a2, a3)

tuple5f :: (AST -> Either Error a0)
    -> (AST -> Either Error a1)
    -> (AST -> Either Error a2)
    -> (AST -> Either Error a3)
    -> (AST -> Either Error a4)
    -> AST -> Either Error (a0, a1, a2, a3, a4)
tuple5f f0 f1 f2 f3 f4 ast = do
    xs <- tuple 5 ast
    a0 <- f0 (xs !! 0)
    a1 <- f1 (xs !! 1)
    a2 <- f2 (xs !! 2)
    a3 <- f3 (xs !! 3)
    a4 <- f4 (xs !! 4)
    return (a0, a1, a2, a3, a4)

astignore :: AST -> Either Error ()
astignore _ = return ()

aststr :: String -> AST -> Either Error ()
aststr s (Atom span x) =
    case s == x of
      True -> return ()
      False -> Left $ Error span $
        "expected string |" ++ s ++ "|. found |" ++ x ++ "|"

-- | create a list of tuple values
tupleFoldMap :: Monoid a => (AST -> Either Error a) -> AST -> Either Error a
tupleFoldMap f (Atom span _) =
  Left $ Error span $
    "expected tuple, found atom."
tupleFoldMap f (Tuple span _ xs) = mconcat <$> traverse f xs

atomOneOf :: [String] -> AST -> Either Error String
atomOneOf _ (Tuple span _ xs) =
  Left $ Error span $
    "expected atom, found tuple."
atomOneOf expected (Atom span atom) =
  case L.findIndex (== atom) expected of
    Just _ -> return atom
    Nothing -> Left $ Error span $
                 "expected one of |" ++
                 L.intercalate ", " expected ++
                 "|. Found |" ++ show atom ++ "|"


tuplehd:: (AST -> Either Error a) -> AST -> Either Error a
tuplehd f atom@(Atom span _) =
  Left $ Error span $ "expected tuple, found atom." ++
            "|" ++ astPretty atom ++ "|"
tuplehd f (Tuple span delim (x:xs)) = f x

tupletail:: (AST -> Either Error a) -> AST -> Either Error [a]
tupletail _ atom@(Atom span _) =
  Left $ Error span $ "expected tuple, found atom." ++
            "|" ++ astPretty atom ++ "|"
tupletail f (Tuple span delim (x:xs)) = do
  M.forM xs f
