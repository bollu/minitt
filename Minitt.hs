{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
import Control.Applicative
import Data.List
import Data.Maybe
import Data.Map (Map,(!),filterWithKey,elems)
import qualified Data.Map as Map
import Text.PrettyPrint as PP
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding ((<>))
import Control.Monad.Except
import Control.Monad.Reader

import Data.List
import Data.Maybe (fromMaybe)
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey
                ,elems,intersectionWith,intersection,keys
                ,member,notMember,empty)
import qualified Data.Map as Map
import qualified Data.Set as Set
import AST
-- CTT / IR --
-- CTT / IR --
-- CTT / IR --
-- CTT / IR --
-- CTT / IR --

type Ident  = String
-- | TODO: Identifier of Telescopes. Are of two types, Object and path based.
type LIdent = String

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Ident,Ter)]

data Label = OLabel LIdent Tele -- Object label
  deriving (Eq,Show)

-- | OBranch of the form: c x1 .. xn -> e
data Branch = OBranch LIdent [Ident] Ter
  deriving (Eq,Show)

-- Declarations: x : A = e
-- A group of mutual declarations is identified by its location. It is used to
-- speed up the Eq instance for Ctxt.
type Decl  = (Ident,(Ter,Ter))
data Decls = MutualDecls Loc [Decl]
           | OpaqueDecl Ident
           | TransparentDecl Ident
           | TransparentAllDecl
           deriving Eq

declIdents :: [Decl] -> [Ident]
declIdents decls = [ x | (x,_) <- decls ]

declTers :: [Decl] -> [Ter]
declTers decls = [ d | (_,(_,d)) <- decls ]

-- | convert a sequence of declarations into a sequence of (ident: type)
declTele :: [Decl] -> Tele
declTele decls = [ (x,t) | (x,(t,_)) <- decls ]

declDefs :: [Decl] -> [(Ident,Ter)]
declDefs decls = [ (x,d) | (x,(_,d)) <- decls ]

labelTele :: Label -> (LIdent,Tele)
labelTele (OLabel c ts) = (c,ts)
-- labelTele (PLabel c ts _ _) = (c,ts)

labelName :: Label -> LIdent
labelName = fst . labelTele

labelTeles :: [Label] -> [(LIdent,Tele)]
labelTeles = map labelTele

lookupLabel :: LIdent -> [Label] -> Maybe Tele
lookupLabel x xs = lookup x (labelTeles xs)

-- lookupPLabel :: LIdent -> [Label] -> Maybe (Tele,[C.Name],C.System Ter)
-- lookupPLabel x xs = listToMaybe [ (ts,is,es) | PLabel y ts is es <- xs, x == y ]

branchName :: Branch -> LIdent
branchName (OBranch c _ _) = c
-- branchName (PBranch c _ _ _) = c

lookupBranch :: LIdent -> [Branch] -> Maybe Branch
lookupBranch _ []      = Nothing
lookupBranch x (b:brs) = case b of
  OBranch c _ _   | x == c    -> Just b
                  | otherwise -> lookupBranch x brs

-- TODO: Term v/s Value?
-- Terms
data Ter = Pi Ter -- TODO: ?
         | App Ter Ter -- f x
         | Lam Ident Ter Ter -- \x: T. e
         | Where Ter Decls -- TODO: ?
         | Var Ident -- x
         | U -- Unit
           -- Sigma types:
         | Sigma Ter -- TODO: ?
         | Pair Ter Ter -- (a, b)
         | Fst Ter -- fst t
         | Snd Ter -- snd t
           -- constructor c Ms
         | Con LIdent [Ter]
           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Ident Loc Ter [Branch]
           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Loc Ident [Label] -- TODO: should only contain OLabels
         | Undef Loc Ter -- Location and type
         | Hole Loc
         | Id Ter Ter Ter
         -- | IdPair Ter (C.System Ter)
         -- | IdJ Ter Ter Ter Ter Ter Ter
  deriving Eq

-- For an expression t, returns (u,ts) where u is no application and t = u ts
unApps :: Ter -> (Ter,[Ter])
unApps = aux []
  where aux :: [Ter] -> Ter -> (Ter,[Ter])
        aux acc (App r s) = aux (s:acc) r
        aux acc t         = (t,acc)

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VSigma Val Val
         | VPair Val Val
         | VCon LIdent [Val]
         | VId Val Val Val
           -- TODO: Neutral => normalization by evaluation?
           -- Neutral values:
         | VVar Ident Val
         | VOpaque Ident Val
         | VFst Val
         | VSnd Val
         | VSplit Val Val
         | VApp Val Val
         | VLam Ident Val Val
         | VIdJ Val Val Val Val Val Val
  deriving Eq

isNeutral :: Val -> Bool
isNeutral v = case v of
  Ter Undef{} _  -> True
  Ter Hole{} _   -> True
  VVar{}         -> True
  VOpaque{}      -> True
  -- VComp{}        -> True
  VFst{}         -> True
  VSnd{}         -> True
  VSplit{}       -> True
  VApp{}         -> True
  VIdJ{}         -> True
  _              -> False
mkVar :: Int -> String -> Val -> Val
mkVar k x = VVar (x ++ show k)

mkVarNice :: [String] -> String -> Val -> Val
mkVarNice xs x = VVar (head (ys \\ xs))
  where ys = x:map (\n -> x ++ show n) [0..]

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show v

isCon :: Val -> Bool
isCon VCon{} = True
isCon _      = False


--------------------------------------------------------------------------------
-- | Environments

data Ctxt = Empty
          | Upd Ident Ctxt
          -- | Sub C.Name Ctxt
          | Def Loc [Decl] Ctxt
  deriving (Show)

instance Eq Ctxt where
    c == d = case (c, d) of
        (Empty, Empty)              -> True
        (Upd x c', Upd y d')        -> x == y && c' == d'
        -- (Sub i c', Sub j d')        -> i == j && c' == d'
        (Def m xs c', Def n ys d')  -> (m == n || xs == ys) && c' == d'
            -- Invariant: if two declaration groups come from the same
            -- location, they are equal and their contents are not compared.
        _                           -> False

-- The Idents and Names in the Ctxt refer to the elements in the two
-- lists. This is more efficient because acting on an environment now
-- only need to affect the lists and not the whole context.
-- The last list is the list of opaque names
-- | C.Nameless comes from Connections.hs
newtype Env = Env (Ctxt,[Val])
  deriving (Eq)

emptyEnv :: Env
emptyEnv = Env (Empty,[])

def :: Decls -> Env -> Env
def (MutualDecls m ds) (Env (rho,vs)) = Env (Def m ds rho,vs)
def (OpaqueDecl n) (Env (rho,vs)) = Env (rho,vs)
def (TransparentDecl n) (Env (rho,vs)) = Env (rho,vs)
def TransparentAllDecl (Env (rho,vs)) = Env (rho,vs)

defWhere :: Decls -> Env -> Env
defWhere (MutualDecls m ds) (Env (rho,vs)) = Env (Def m ds rho, vs)
defWhere (OpaqueDecl _) rho = rho
defWhere (TransparentDecl _) rho = rho
defWhere TransparentAllDecl rho = rho

upd :: (Ident,Val) -> Env -> Env
upd (x,v) (Env (rho,vs)) = Env (Upd x rho,v:vs)

upds :: [(Ident,Val)] -> Env -> Env
upds xus rho = foldl (flip upd) rho xus

updsTele :: Tele -> [Val] -> Env -> Env
updsTele tele vs = upds (zip (map fst tele) vs)

-- subs :: [(C.Name,C.Formula)] -> Env -> Env
-- subs iphis rho = foldl (flip sub) rho iphis

mapEnv :: (Val -> Val) -> Env -> Env
mapEnv f (Env (rho,vs)) = Env (rho,map f vs)

valOfEnv :: Env -> [Val]
valOfEnv (Env (_,vs)) = vs


-- | Extract the context from the environment, used when printing holes
contextOfEnv :: Env -> [String]
contextOfEnv rho = case rho of
  Env (Empty,_)               -> []
  Env (Upd x e,VVar n t:vs) -> (n ++ " : " ++ show t) : contextOfEnv (Env (e,vs))
  Env (Upd x e,v:vs)        -> (x ++ " = " ++ show v) : contextOfEnv (Env (e,vs))
  Env (Def _ _ e,vs)        -> contextOfEnv (Env (e,vs))
  -- Env (Sub i e,vs,phi:fs,os)      -> (show i ++ " = " ++ show phi) : contextOfEnv (Env (e,vs,fs,os))

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Env where
  show = render . showEnv True

showEnv :: Bool -> Env -> Doc
showEnv b e =
  let -- This decides if we should print "x = " or not
      names x = if b then text x <+> equals else PP.empty
      par   x = if b then parens x else x
      com     = if b then comma else PP.empty
      showEnv1 e = case e of
        Env (Upd x env,u:us)   ->
          showEnv1 (Env (env,us)) <+> names x <+> showVal1 u <> com
        -- Env (Sub i env,us,phi:fs,os) ->
        --   showEnv1 (Env (env,us,fs,os)) <+> names (show i) <+> text (show phi) <> com
        Env (Def _ _ env,vs)   -> showEnv1 (Env (env,vs))
        _                            -> showEnv b e
  in case e of
    Env (Empty,_)            -> PP.empty
    Env (Def _ _ env,vs)   -> showEnv b (Env (env,vs))
    Env (Upd x env,u:us)   ->
      par $ showEnv1 (Env (env,us)) <+> names x <+> showVal1 u
    -- Env (Sub i env,us,phi:fs,os) ->
    --   par $ showEnv1 (Env (env,us,fs,os)) <+> names (show i) <+> text (show phi)


showLoc :: Loc -> Doc
showLoc (Loc  _ i j ) = text (show  (i, j))


instance Show Ter where
  show = render . showTer

showTer :: Ter -> Doc
showTer v = case v of
  U                  -> char 'U'
  App e0 e1          -> showTer e0 <+> showTer1 e1
  Pi e0              -> text "Pi" <+> showTer e0
  Lam x t e          -> char '\\' <> parens (text x <+> colon <+> showTer t) <+>
                          text "->" <+> showTer e
  Fst e              -> showTer1 e <> text ".1"
  Snd e              -> showTer1 e <> text ".2"
  Sigma e0           -> text "Sigma" <+> showTer1 e0
  Pair e0 e1         -> parens (showTer e0 <> comma <> showTer e1)
  Where e d          -> showTer e <+> text "where" <+> showDecls d
  Var x              -> text x
  Con c es           -> text c <+> showTers es
  -- PCon c a es phis   -> text c <+> braces (showTer a) <+> showTers es
  --                       <+> hsep (map ((char '@' <+>) . showFormula) phis)
  Split f _ _ _      -> text f
  Sum _ n _          -> text n
  -- HSum _ n _         -> text n
  Undef{}            -> text "undefined"
  Hole{}             -> text "?"
  Id a u v           -> text "Id" <+> showTers [a,u,v]

showTers :: [Ter] -> Doc
showTers = hsep . map showTer1

showTer1 :: Ter -> Doc
showTer1 t = case t of
  U        -> char 'U'
  Con c [] -> text c
  Var{}    -> showTer t
  Undef{}  -> showTer t
  Hole{}   -> showTer t
  Split{}  -> showTer t
  Sum{}    -> showTer t
  -- HSum{}   -> showTer t
  Fst{}    -> showTer t
  Snd{}    -> showTer t
  _        -> parens (showTer t)

showDecls :: Decls -> Doc
showDecls (MutualDecls _ defs) =
  hsep $ punctuate comma
  [ text x <+> equals <+> showTer d | (x,(_,d)) <- defs ]
showDecls (OpaqueDecl i) = text "opaque" <+> text i
showDecls (TransparentDecl i) = text "transparent" <+> text i
showDecls TransparentAllDecl = text "transparent_all"

instance Show Val where
  show = render . showVal

showVal :: Val -> Doc
showVal v = case v of
  VU                -> char 'U'
  Ter t@Sum{} rho   -> showTer t <+> showEnv False rho
  Ter t@Split{} rho -> showTer t <+> showEnv False rho
  Ter t rho         -> showTer1 t <+> showEnv True rho
  VCon c us         -> text c <+> showVals us
  VPi a l@(VLam x t b)
    | "_" `isPrefixOf` x -> showVal1 a <+> text "->" <+> showVal1 b
    | otherwise          -> char '(' <> showLam v
  VPi a b           -> text "Pi" <+> showVals [a,b]
  VPair u v         -> parens (showVal u <> comma <> showVal v)
  VSigma u v        -> text "Sigma" <+> showVals [u,v]
  VApp u v          -> showVal u <+> showVal1 v
  VLam{}            -> text "\\(" <> showLam v
  -- VPLam{}           -> char '<' <> showPLam v
  VSplit u v        -> showVal u <+> showVal1 v
  VVar x _          -> text x
  VOpaque x _       -> text ('#':x)
  VFst u            -> showVal1 u <> text ".1"
  VSnd u            -> showVal1 u <> text ".2"
  VId a u v           -> text "Id" <+> showVals [a,u,v]

-- Merge lambdas of the same type
showLam :: Val -> Doc
showLam e = case e of
  VLam x t a@(VLam _ t' _)
    | t == t'   -> text x <+> showLam a
    | otherwise ->
      text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal a
  VPi _ (VLam x t a@(VPi _ (VLam _ t' _)))
    | t == t'   -> text x <+> showLam a
    | otherwise ->
      text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal a
  VLam x t e         ->
    text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal e
  VPi _ (VLam x t e) ->
    text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal e
  _ -> showVal e

showVal1 :: Val -> Doc
showVal1 v = case v of
  VU                -> showVal v
  VCon c []         -> showVal v
  VVar{}            -> showVal v
  VFst{}            -> showVal v
  VSnd{}            -> showVal v
  Ter t rho | isEmpty (showEnv False rho) -> showTer1 t
  _                 -> parens (showVal v)

showVals :: [Val] -> Doc
showVals = hsep . map showVal1


-- Eval --
-- Eval --
-- Eval --
-- Eval --
-- Eval --

look :: String -> Env -> Val
look x (Env (Upd y rho,v:vs)) | x == y = v
                                    | otherwise = look x (Env (rho,vs))
look x r@(Env (Def _ decls rho,vs)) = case lookup x decls of
  Just (_,t) -> eval r t
  Nothing    -> look x (Env (rho,vs))
-- look x (Env (Sub _ rho,vs)) = look x (Env (rho,vs))
look x (Env (Empty,_)) = error $ "look: not found " ++ show x

lookType :: String -> Env -> Val
lookType x (Env (Upd y rho,v:vs))
  | x /= y        = lookType x (Env (rho,vs))
  | VVar _ a <- v = a
  | otherwise     = error ""
lookType x r@(Env (Def _ decls rho,vs)) = case lookup x decls of
  Just (a,_) -> eval r a
  Nothing -> lookType x (Env (rho,vs))
-- lookType x (Env (Sub _ rho,vs,_:fs,os)) = lookType x (Env (rho,vs,fs,os))
lookType x (Env (Empty,_))          = error $ "lookType: not found " ++ show x

-----------------------------------------------------------------------
-- The evaluator

eval :: Env -> Ter -> Val
eval rho@(Env (_,_)) v = case v of
  U                   -> VU
  App r s             -> app (eval rho r) (eval rho s)
  Var i
    -- | TODO: do we need VOpaque anymore?
    -- | i `Set.member` os -> VOpaque i (lookType i rho)
    | otherwise       -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval rho a) (eval rho t)
  Sigma t@(Lam _ a _) -> VSigma (eval rho a) (eval rho t)
  Pair a b            -> VPair (eval rho a) (eval rho b)
  Fst a               -> fstVal (eval rho a)
  Snd a               -> sndVal (eval rho a)
  Where t decls       -> eval (defWhere decls rho) t
  Con name ts         -> VCon name (map (eval rho) ts)
  Lam{}               -> Ter v rho
  Split{}             -> Ter v rho
  Sum{}               -> Ter v rho
  Undef{}             -> Ter v rho
  Hole{}              -> Ter v rho
  Id a r s            -> VId (eval rho a) (eval rho r) (eval rho s)
  _                   -> error $ "Cannot evaluate " ++ show v

evals :: Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]
app :: Val -> Val -> Val
app u v = case (u,v) of
  (Ter (Lam x _ t) e,_)               -> eval (upd (x,v) e) t
  (Ter (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  (Ter Split{} _,_) | isNeutral v         -> VSplit u v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
fstVal u | isNeutral u = VFst u
fstVal u               = error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
sndVal u | isNeutral u = VSnd u
sndVal u               = error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: Val -> Val
inferType v = case v of
  VVar _ t -> t
  VOpaque _ t -> t
  Ter (Undef _ t) rho -> eval rho t
  VFst t -> case inferType t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType t of
    VSigma _ f -> app f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> case eval rho t of
    VPi _ f -> app f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> case inferType t0 of
    VPi _ f -> app f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  _ -> error $ "inferType: not neutral " ++ show v

-- Extraction functions for getting a, f, s and t:
equivDom :: Val -> Val
equivDom = fstVal

equivFun :: Val -> Val
equivFun = fstVal . sndVal

equivContr :: Val -> Val
equivContr =  sndVal . sndVal


-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv :: [String] -> a -> a -> Bool

instance Convertible Env where
  conv ns (Env (rho1,vs1)) (Env (rho2,vs2)) =
      conv ns (rho1,vs1) (rho2,vs2)

instance Convertible Val where
  conv ns u v | u == v    = True
              | otherwise =
    -- let j = C.fresh (u,v)
    let xx = error "xx" -- j = C.fresh (u,v)
    in case (u,v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (eval (upd (x',v) e') u')
      (Ter (Lam x a u) e,u') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (app u' v)
      (u',Ter (Lam x a u) e) ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (app u' v) (eval (upd (x,v) e) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> (p == p') && conv ns e e'
      -- (Ter (HSum p _ _) e,Ter (HSum p' _ _) e')       -> (p == p') && conv ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e') -> p == p' && conv ns e e'
      (Ter (Hole p) e,Ter (Hole p') e') -> p == p' && conv ns e e'
      -- (Ter Hole{} e,_) -> True
      -- (_,Ter Hole{} e') -> True
      (VPi u v,VPi u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VSigma u v,VSigma u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VCon c us,VCon c' us')   -> (c == c') && conv ns us us'
      -- (VPCon c v us phis,VPCon c' v' us' phis') ->
      --   (c == c') && conv ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')    -> conv ns u u' && conv ns v v'
      (VPair u v,w)              -> conv ns u (fstVal w) && conv ns v (sndVal w)
      (w,VPair u v)              -> conv ns (fstVal w) u && conv ns (sndVal w) v
      (VFst u,VFst u')           -> conv ns u u'
      (VSnd u,VSnd u')           -> conv ns u u'
      (VApp u v,VApp u' v')      -> conv ns u u' && conv ns v v'
      (VSplit u v,VSplit u' v')  -> conv ns u u' && conv ns v v'
      (VOpaque x _, VOpaque x' _) -> x == x'
      (VVar x _, VVar x' _)       -> x == x'
      (VId a u v,VId a' u' v')               -> conv ns (a,u,v) (a',u',v')
      (VIdJ a u c d x p,VIdJ a' u' c' d' x' p') ->
        conv ns [a,u,c,d,x,p] [a',u',c',d',x',p']
      _                                      -> False
instance Convertible Ctxt where
  conv _ _ _ = True

instance Convertible () where
  conv _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv ns (u, v) (u', v') = conv ns u u' && conv ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv ns (u, v, w) (u', v', w') = conv ns (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv ns (u,v,w,x) (u',v',w',x') = conv ns (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv ns us us' = length us == length us' &&
                  and [conv ns u u' | (u,u') <- zip us us']

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [String] -> a -> a

instance Normal Env where
  normal ns (Env (rho,vs)) = Env (normal ns (rho,vs))

instance Normal Val where
  normal ns v = case v of
    VU                  -> VU
    Ter (Lam x t u) e   ->
      let w = eval e t
          v@(VVar n _) = mkVarNice ns x w
      in VLam n (normal ns w) $ normal (n:ns) (eval (upd (x,v) e) u)
    Ter t e             -> Ter t (normal ns e)
    VPi u v             -> VPi (normal ns u) (normal ns v)
    VSigma u v          -> VSigma (normal ns u) (normal ns v)
    VPair u v           -> VPair (normal ns u) (normal ns v)
    VCon n us           -> VCon n (normal ns us)
    VVar x t            -> VVar x (normal ns t)
    VFst t              -> VFst (normal ns t)
    VSnd t              -> VSnd (normal ns t)
    VSplit u t          -> VSplit (normal ns u) (normal ns t)
    VApp u v            -> VApp (normal ns u) (normal ns v)
    -- VAppFormula u phi   -> VAppFormula (normal ns u) (normal ns phi)
    VId a u v           -> VId (normal ns a) (normal ns u) (normal ns v)
    -- VIdPair u us        -> VIdPair (normal ns u) (normal ns us)
    -- VIdJ a u c d x p    -> VIdJ (normal ns a) (normal ns u) (normal ns c)
    --                             (normal ns d) (normal ns x) (normal ns p)
    _                   -> v

instance Normal Ctxt where
  normal _ = id

instance Normal a => Normal (Map k a) where
  normal ns = Map.map (normal ns)

instance (Normal a,Normal b) => Normal (a,b) where
  normal ns (u,v) = (normal ns u,normal ns v)
-- 
instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal ns (u,v,w) = (normal ns u,normal ns v,normal ns w)
-- 
instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal ns (u,v,w,x) =
    (normal ns u,normal ns v,normal ns w, normal ns x)

instance Normal a => Normal [a] where
  normal ns = map (normal ns)

-- TypeCheck --
-- TypeCheck --
-- TypeCheck --
-- TypeCheck --
-- TypeCheck --

-- | Type checking monad
type Typing a = ReaderT TEnv (ExceptT String IO) a
--
-- | Environment for type checker
data TEnv =
  TEnv { names   :: [String] -- generated names
       , indent  :: Int
       , env     :: Env
       , verbose :: Bool  -- Should it be verbose and print what it typechecks?
       } deriving (Eq)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv [] 0 emptyEnv True
silentEnv  = TEnv [] 0 emptyEnv False

-- Trace function that depends on the verbosity flag
trace :: String -> Typing ()
trace s = do
  b <- asks verbose
  when b $ liftIO (putStrLn s)

-------------------------------------------------------------------------------
-- | Functions for running computations in the type checker monad

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runExceptT $ runReaderT t env

runDecls :: TEnv -> Decls -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  return $ addDecls d tenv

runDeclss :: TEnv -> [Decls] -> IO (Maybe String,TEnv)
runDeclss tenv []     = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (infer e)

-------------------------------------------------------------------------------
-- | Modifiers for the environment

addTypeVal :: (Ident,Val) -> TEnv -> TEnv
addTypeVal (x,a) (TEnv ns ind rho v) =
  let w@(VVar n _) = mkVarNice ns x a
  in TEnv (n:ns) ind (upd (x,w) rho) v

addType :: (Ident,Ter) -> TEnv -> TEnv
addType (x,a) tenv@(TEnv _ _ rho _) = addTypeVal (x,eval rho a) tenv

addBranch :: [(Ident,Val)] -> Env -> TEnv -> TEnv
addBranch nvs env (TEnv ns ind rho v) =
  TEnv ([n | (_,VVar n _) <- nvs] ++ ns) ind (upds nvs rho) v

addDecls :: Decls -> TEnv -> TEnv
addDecls d (TEnv ns ind rho v) = TEnv ns ind (def d rho) v

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

-- faceEnv :: C.Face -> TEnv -> TEnv
-- faceEnv alpha tenv = tenv{env=env tenv `C.face` alpha}

-------------------------------------------------------------------------------
-- | Various useful functions

-- Extract the type of a label as a closure
getLblType :: LIdent -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ _ cas) r) = case lookupLabel c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c ++ " in " ++ show cas)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Monadic version of unless
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb x = mb >>= flip unless x

mkVars :: [String] -> Tele -> Env -> [(Ident,Val)]
mkVars _ [] _           = []
mkVars ns ((x,a):xas) nu =
  let w@(VVar n _) = mkVarNice ns x (eval nu a)
  in (x,w) : mkVars (n:ns) xas (upd (x,w) nu)

-- Test if two values are convertible
(===) :: Convertible a => a -> a -> Typing Bool
u === v = conv <$> asks names <*> pure u <*> pure v

-- eval in the typing monad
evalTyping :: Ter -> Typing Val
evalTyping t = eval <$> asks env <*> pure t

-------------------------------------------------------------------------------
-- | The bidirectional type checker

-- Check that t has type a
check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Undef{}) -> return ()
  (_,Hole l)  -> do
      rho <- asks env
      let e = unlines (reverse (contextOfEnv rho))
      ns <- asks names
      trace $ "\nHole at " ++ show l ++ ":\n\n" ++
              e ++ replicate 80 '-' ++ "\n" ++ show (normal ns a)  ++ "\n"
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi f)       -> checkFam f
  (VU,Sigma f)    -> checkFam f
  (VU,Sum _ _ bs) -> forM_ bs $ \lbl -> case lbl of
    OLabel _ tele -> checkTele tele
  (VPi va@(Ter (Sum _ _ cas) nu) f,Split _ _ ty ces) -> do
    check VU ty
    rho <- asks env
    unlessM (a === eval rho ty) $ throwError "check: split annotations"
    if map labelName cas == map branchName ces
       then sequence_ [ checkBranch (lbl,nu) f brc (Ter t rho) va
                      | (brc, lbl) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x a' t)  -> do
    check VU a'
    ns <- asks names
    rho <- asks env
    unlessM (a === eval rho a') $
      throwError $ "check: lam types don't match"
        ++ "\nlambda type annotation: " ++ show a'
        ++ "\ndomain of Pi: " ++ show a
        ++ "\nnormal form of type: " ++ show (normal ns a)
    let var = mkVarNice ns x a

    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, Pair t1 t2) -> do
    check a t1
    v <- evalTyping t1
    check (app f v) t2
  (_,Where e d) -> do
    local (\tenv@TEnv{indent=i} -> tenv{indent=i + 2}) $ checkDecls d
    local (addDecls d) $ check a e
  (VU,Id a a0 a1) -> do
    check VU a
    va <- evalTyping a
    check va a0
    check va a1
  _ -> do
    v <- infer t
    unlessM (v === a) $
      throwError $ "check conv:\n" ++ show v ++ "\n/=\n" ++ show a

-- Check a list of declarations
checkDecls :: Decls -> Typing ()
checkDecls (MutualDecls _ []) = return ()
checkDecls (MutualDecls l d)  = do
  a <- asks env
  let (idents,tele,ters) = (declIdents d,declTele d,declTers d)
  ind <- asks indent
  trace (replicate ind ' ' ++ "Checking: " ++ unwords idents)
  checkTele tele
  local (addDecls (MutualDecls l d)) $ do
    rho <- asks env
    checks (tele,rho) ters
checkDecls (OpaqueDecl _)      = return ()
checkDecls (TransparentDecl _) = return ()
checkDecls TransparentAllDecl  = return ()

-- Check a telescope
checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  local (addType (x,a)) $ checkTele xas

-- Check a family
checkFam :: Ter -> Typing ()
checkFam (Lam x a b) = do
  check VU a
  local (addType (x,a)) $ check VU b
checkFam x = throwError $ "checkFam: " ++ show x


checkBranch :: (Label,Env) -> Val -> Branch -> Val -> Val -> Typing ()
checkBranch (OLabel _ tele,nu) f (OBranch c ns e) _ _ = do
  ns' <- asks names
  let us = map snd $ mkVars ns' tele nu
  local (addBranch (zip ns us) nu) $ check (app f (VCon c us)) e

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks ([],_)         []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  v' <- evalTyping e
  checks (xas,upd (x,v') nu) es
checks _              _      =
  throwError "checks: incorrect number of arguments"

-- | infer the type of e
infer :: Ter -> Typing Val
infer e = case e of
  U           -> return VU  -- U : U
  Var n       -> lookType n <$> asks env
  App t u -> do
    c <- infer t
    case c of
      VPi a f -> do
        check a u
        v <- evalTyping u
        return $ app f v
      _       -> throwError $ show c ++ " is not a product"
  Fst t -> do
    c <- infer t
    case c of
      VSigma a f -> return a
      _          -> throwError $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- infer t
    case c of
      VSigma a f -> do
        v <- evalTyping t
        return $ app f (fstVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    local (addDecls d) $ infer t
  _ -> throwError ("infer " ++ show e)

