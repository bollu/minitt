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

-- data Type = Tnat | Tarrow Type Type deriving(Eq, Ord) 

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
  | Etrivial
  | Esole
  | Eabsurd
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

-- | WTF is cons
alphaEquivGo (Econs x xs) (Econs x' xs') = error $ "unimplement α for cons"


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
    t <- case synth tenv exp of
           Left failure -> putStrLn failure >> exitFailure
           Right t -> pure t
    putStrLn $ "\t+type: " <> show t
    v <- case val venv exp of
             Left failure -> putStrLn failure >> exitFailure 
             Right v -> pure v
    putStrLn $ "\t+evaluated. reading back..."
    exp' <- case  readback [] t v of
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

check :: [(Name, Type)] -> Exp -> Type -> Either String ()
check = undefined

synth :: [(Name, Type)] -> Exp -> Either String Type
synth = undefined

--- 6: NBE
data Val = 
    PI Val Closure | 
    LAM Closure |
    SIGMA Val Closure |
    PAIR Val Val |
    NAT |
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
    NEU Val Neutral -- NEU type neutral data
    deriving(Show)

type Type = Val

-- | the embedding is shallow because it's used by shallow people in a hurry
-- who don't want to deal with binders!
data Closure = 
    ClosureShallow Name (Val -> Val) | 
    ClosureDeep [(Name, Val)] Name Exp 

instance Show Closure where
  show (ClosureShallow arg _) = "ClosureShallow(" <> show arg <> " " <> "<<code>>)"
  show (ClosureDeep env arg body) = 
    "ClosureDeep(" <> show env <> " " <> show arg <> " " <> show body <> ")"

   
data ValAndTy = ValAndTy Val Type deriving(Show)
--- | The thing at the "to be reduced" position is stuck
data Neutral = Nvar Name 
  | Nap Neutral ValAndTy
  | Ncar Neutral
  | Ncdr Neutral
  | Nindnat Neutral ValAndTy ValAndTy ValAndTy -- target motive base step
  | Nreplace Neutral ValAndTy -- target motive base 
  | Nindabsurd Neutral ValAndTy -- target motive 
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
valOfClosure (ClosureShallow x f) v = return $ f v
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
doAp fun arg = error "unimplemented"

doCar:: Val -> Either String Val
doCar v = error "unimplemented"

doCdr :: Val -> Either String Val
doCdr v = error "unimplemented"

doIndAbsurd :: Val -> Val -> Either String Val
doIndAbsurd target motive = error "unimplemented"

doReplace :: Val -> Val -> Val -> Either String Val
doReplace target motive base = error "unimplemented"

doIndNat :: Val -> Val -> Val -> Val -> Either String Val
doIndNat target motive base step = error "unimplemented"

fresh :: [Name] -> Name -> Name
fresh used x = 
  case find (== x) used of
    Just _ -> fresh used (x <> "*")
    Nothing -> x

readback :: [String] -> Type -> Val -> Either String Exp
readback = undefined
