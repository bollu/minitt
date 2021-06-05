import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

-- Sum types into STLC + naturals
-- Bidirectional type checking for STLC from
-- http://davidchristiansen.dk/tutorials/nbe/
-- Continuations for normalizing sum types: https://boxbase.org/entries/2020/may/25/cps-nbe/

type Name = String

-- 1.2 The Evaluator 
-- STLC
data Type = 
    Tnat
 | Tarrow Type Type
 | Tprod Type Type
 | Tsum Type Type
 deriving(Eq, Ord) 

data Exp = 
    Elam Name Exp 
  | Eident String
  | E0
  | Eadd1 Exp
  | Eap Exp Exp
  | Erec Type Exp Exp Exp -- naturals eliminator
  | Eleft Exp -- sum type constructor
  | Eright Exp -- sum type constructor
  | Ecase Type Exp Exp Exp -- sum type eliminator
  | Epair Exp Exp
  | Ecar Exp
  | Ecdr Exp
  -- | Elamcase [(Name, Exp)] -- eliminator
  | Eannotate Type Exp
  deriving(Eq, Ord)


instance Show Exp where
  show (Elam name exp) = "(λ " <> name <> " " <> show exp <> ")"
  show (Eident name) = name
  show (Eap f x) = "($ " <> show f <> " " <> show x <> ")"
  show (E0) = "0"
  show (Eadd1 x) = "(+1 " <> show x <> ")"
  show (Eannotate e t) = "(∈ " <> show e <> " " <> show t <> ")"
  show (Erec t target base step) = "(rec " <> show target <> " " <> show base <> " " <> show step <> ")"
type Choice = (String, Exp)

instance Show Type where
  show Tnat = "nat"
  show (Tarrow l r) = "[→ " <> show l <> " " <> show r <> "]"

toType :: AST -> Either Error Type
toType (Atom span "nat") = Right $ Tnat
toType (Atom span ident) = 
  Left $ show span <> " unknown atomic type |" <> show ident <> "|"
toType tuple = do
  head  <- tuplehd atom tuple
  case head of 
      "→" -> do 
        ((), l, r) <- tuple3f astignore toType toType tuple
        return $ Tarrow l r
      _ -> Left $ "unknown type former |" ++ head ++ "| " ++
             "in |" ++ "|" ++ astPretty tuple ++ "|"
        
  

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
      ((), t, e) <- tuple3f astignore toType toExp tuple
      return $ Eannotate t e
    "+1" -> do 
      ((), e) <- tuple2f astignore toExp tuple
      return $ Eadd1 e
    "rec" -> do 
      ((), ty, target, base, step) <- 
        tuple5f astignore toType toExp toExp toExp tuple
      return $ Erec ty target base step
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
-- | → constructor
check gamma e@(Elam x b) t = 
  case t of 
    Tarrow tl tr -> check ((x,tl):gamma) b tr
    _ -> Left $ "Need non-arrow type for lambda |" <> show e <> "|." <>
          "Found type |" <> show t <> "|"

-- | nat constructors: +1, 0
check gamma e@(Eadd1 x) t = do
    case t of 
        Tnat -> check gamma x Tnat
        _ -> Left $ "Expression |" <> show e <> 
                    " is being checked as non-natural |" <> show t <> "|."

check gamma E0 t = do
    case t of 
        Tnat -> return ()
        _ -> Left $ "0 is being checked as non-natural |" <> show t <> "|."
-- | Checking -> synthesis mediation
check gamma eother t = do
  t2 <- synth gamma eother
  case t2 == t of
    True -> pure ()
    False ->  Left $ "Expression |" <> show eother <> "|" <> 
                "expected |" <> show t <> "|, " <>
                "but type-inference synthesized |" <> show t2 <> "|"

synth :: [(Name, Type)] -> Exp -> Either String Type
-- | Annotation -> Checking mediation
synth gamma (Eannotate t e) = 
  do check gamma e t; return t
-- | Identifiers [projection of the _environment_]
synth gamma (Eident x) = do
  case lookup x gamma of
    Just t -> return t
    Nothing -> Left $ "unknown variable: |" <> show x <> "|"
-- | rec [elimination of nat]
synth gamma erec@(Erec ty target base step) = do
    check gamma target Tnat
    check gamma base ty
    check gamma step  (Tarrow Tnat (Tarrow ty ty))
    return ty
-- | ap [elimination of →]
synth gamma eap@(Eap f x) = do
  tf <- synth gamma f
  case tf of
    Tarrow ti to -> do 
       check gamma x ti
       return to
    _ -> Left $ "rator expected to have arrow type. " <> 
           "Found type |" <> show tf <> "|, in: " <> show eap

-- | I feel like I CAN write type synthesis for |0| and |add1|. I don't know why this is NOT DONE.
synth gamma E0 = return Tnat
synth gamma (Eadd1 x) = do
  check gamma x Tnat
  return Tnat

synth gamma e = 
  Left $ "cannot synthesize type for |" <> show e <> "|"


--- 6: NBE
data Val  = ZERO 
  | ADD1 Val
  | CLOS [(Name, Val)] Name Exp
  | SUM Bool Val
  | PAIR Val Val 
  | NEU Type Neutral

data ValAndTy = ValAndTy Val Type
--- | The thing at the "to be reduced" position is stuck
data Neutral = Nvar Name 
  | Nap Neutral ValAndTy
  | Ncar Neutral
  | Ncdr Neutral
  | Nrec Type Neutral ValAndTy ValAndTy
  | Ncase Type Neutral ValAndTy ValAndTy

val :: [(Name, Val)] -> Exp -> Either String Val
val env (Eannotate t e) = val env e
val env E0 = return ZERO
val env (Eadd1 n) = do 
  vn <- val env n
  return $ ADD1 vn
val env (Eident x) = 
   case lookup x env of
      Just x -> return x
      Nothing -> Left $ "ERR val: unknown identifier |" <> show x <> "|"
val env (Elam x body) = return $ CLOS env x body
val env (Erec ty target base step) = do 
  vtarget <- val env target
  vbase <- val env base
  vstep <- val env step
  valRec ty vtarget vbase vstep
val env (Eap f x) = do
  vf <- val env f
  vx <- val env x
  valAp vf vx
val env (Eleft e) = do
    ve <- val env e
    return $ SUM False e
val env (Eright e) = do
    ve <- val env e
    return $ SUM True e
val env (Ecase ty scrut l r) = do
    vscrut <- val env scrut
    vl <- val env l
    vr <- val env r
    valCase ty vscrut vl vr

val env (Epair l r) = do
    vl <- val env l
    vr <- val env r
    return $ PAIR vl vr

val env (Ecar p) = val env p >>= valCar
val env (Ecdr p) = val env p >>= valCdr

valCar :: Val -> Either String Val
valCar (PAIR l r) = return l
valCar (NEU (Tprod tl tr) n) = return $ NEU tl $ Ncar n

valCdr :: Val -> Either String Val
valCdr (PAIR l r) = return r
valCdr (NEU (Tprod tl tr) n) = return $ NEU tr $ Ncdr n


-- | can't give type??
valCase :: Type -> Val -> Val -> Val -> Either String Val
valCase _ (SUM False v) vl _ = valAp vl v
valCase _ (SUM True v) vr _ = valAp vr v
-- | can't get type x( 
valCase tout (NEU tn n) vl vr = do
    let vtl = ValAndTy vl (Tarrow tn tout)
    let vtr = ValAndTy vr (Tarrow tn tout)
    NEU tout $ Ncase tn n vtl vtr

valAp :: Val -> Val -> Either String Val
valAp (CLOS env name body) x = 
  val ((name,x):env) body
valAp (NEU (Tarrow ti to) nf) x = 
  return $ NEU to $ Nap nf (ValAndTy x ti)

-- | type, target, base, step
valRec :: Type -> Val -> Val -> Val -> Either String Val
valRec ty ZERO base _ = return base
valRec ty (ADD1 n) base step = do 
   stepn <- (valAp step n) 
   recn <- (valRec ty n base step)
   out <- valAp stepn recn
   return $ out
valRec ty (NEU Tnat n) base step =  do
   let vtbase = ValAndTy base ty
   let vtstep = ValAndTy step (Tarrow Tnat (Tarrow ty ty))
   return $ NEU ty $ Nrec ty n vtbase vtstep

fresh :: [Name] -> Name -> Name
fresh used x = 
  case find (== x) used of
    Just _ -> fresh used (x <> "*")
    Nothing -> x

readback :: [String] -> Type -> Val -> Either String Exp
-- | Tnat
readback names Tnat ZERO = return $ E0
readback names Tnat (ADD1 v) = do
  ev <- readback names Tnat v
  return $ Eadd1 ev
readback names Tnat (NEU _ ne) = 
  readbackNeutral names ne
-- Tarr
readback names (Tarrow ti to) lam = do
  let x = fresh names "x"
  let xv = NEU ti (Nvar x)
  lamEval <- valAp lam xv
  lamExpr <- readback (x:names) to lamEval
  return $ Elam x lamExpr


-- | doesn't need type? interessting. 
-- I suppose not, because it has access to types in ValAndTy
readbackNeutral :: [String] -> Neutral -> Either String Exp
readbackNeutral names (Nvar x) = return $ Eident x
readbackNeutral names (Nap neutf (ValAndTy x tx)) = do
    ef <- readbackNeutral names neutf 
    ex <- readback names tx x
    return $ Eap ef ex
readbackNeutral names 
  (Nrec ty neutn (ValAndTy vbase tbase) (ValAndTy vstep tstep)) = do
    en <- readbackNeutral names neutn
    ebase <- readback names tbase vbase
    estep <- readback names tstep vstep
    return $ Erec ty en ebase estep
