-- STLC + bidirectional typing
-- runhaskell Christiansen5.hs examples/christiansen5.rkt

import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

-- Bidirectional type checking for STLC from
-- http://davidchristiansen.dk/tutorials/nbe/

type Name = String

-- 1.2 The Evaluator 
-- STLC
data Type = Tnat | Tarrow Type Type deriving(Eq, Ord) 

data Exp = 
    Elam Name Exp 
  | Eident String
  | E0
  | Eadd1 Exp
  | Eap Exp Exp
  | Erec Type Exp Exp Exp
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
      _ -> Left $ "unknown type former |" ++ head ++ "| in |" ++ "|" ++ astPretty tuple ++ "|"
        
  

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
        ((), ty, target, base, step) <- tuple5f astignore toType toExp toExp toExp tuple
        return $ Erec ty target base step
      _ -> Left $ "unknown special form |" ++ head ++ "| in " ++ "|" ++ astPretty tuple ++ "|"


toDecl :: AST -> Either Error (Name, Exp)
toDecl = tuple2f atom toExp


foldM' :: (Semigroup s, Monad m, Traversable t) => s -> t a -> (s -> a -> m s) -> m s
foldM' s t f = foldM f s t

foldM1' :: (Monoid s, Monad m, Traversable t) => t a -> (s -> a -> m s) -> m s
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

  putStrLn $ "type checking..."
  -- let initenv = [("add1", Tarrow Tnat Tnat)]
  foldM1' decls $ \env (name,exp) -> do
     t <- case synth env exp of
            Left failure -> putStrLn failure >> exitFailure
            Right t -> pure t
     putStrLn $ "- " <> name <> ":\t"  <> show t
     return ((name, t):env)
  return ()


errTyMismatch :: (Exp, Type) -> Type -> String
errTyMismatch (e, ety) expectedty = 
  "Found expression |" <> show e <> "| to have type " <> show ety <> "|. Expected type |" <> show expectedty <> "|."

check :: [(Name, Type)] -> Exp -> Type -> Either String ()
-- | → constructor
check gamma e@(Elam x b) t = 
  case t of 
    Tarrow tl tr -> check ((x,tl):gamma) b tr -- check the body by binding `x` to `tl`.
    _ -> Left $ "Need non-arrow type for lambda |" <> show e <> "|. Found type |" <> show t <> "|"

-- | nat constructors: +1, 0
check gamma e@(Eadd1 x) t = do
    case t of 
        Tnat -> check gamma x Tnat
        _ -> Left $ "Expression |" <> show e <> " is being checked as non-natural |" <> show t <> "|."

check gamma E0 t = do
    case t of 
        Tnat -> return ()
        _ -> Left $ "0 is being checked as non-natural |" <> show t <> "|."
-- | Checking -> synthesis mediation
check gamma eother t = do
  t2 <- synth gamma eother
  case t2 == t of
    True -> pure ()
    False ->  Left $ "Expression |" <> show eother <> "| expected |" <> show t <> "|, but type-inference synthesized |" <> show t2 <> "|"

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
    -- ttarget <- synth gamma target
    -- case ttarget of
    --     Tnat ->  Right ()
    --     _ -> Left $ "expected target of recursion |" <> show target <> "| to have type nat found type " <> show ttarget <> 
    --                 ". Error occured at |" <> show erec <> "|."
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
    _ -> Left $ "rator expected to have arrow type. found type |" <> show tf <> "|, in: " <> show eap

-- | I feel like I CAN write type synthesis for |0| and |add1|. I don't know why this is NOT DONE.
-- We don't do this because we generally synthesize for eliminators, and check for constructors.
synth gamma E0 = return Tnat
synth gamma (Eadd1 x) = do
  check gamma x Tnat
  return Tnat

synth gamma e = 
  Left $ "cannot synthesize type for |" <> show e <> "|"
