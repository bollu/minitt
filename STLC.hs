{-# LANGUAGE OverloadedStrings #-}

import Language.LSP.Server
import Language.LSP.Types
import Control.Monad.IO.Class
import qualified Data.Text as T


-- Simply typed lambda calculus with
-- normalization by evaluation.
-- https://en.wikipedia.org/wiki/Normalisation_by_evaluation
-- bidirectional type system: https://www.youtube.com/watch?v=utyBNDj7s2w
-- https://github.com/bollu/koans/blob/master/nbe.hs
-- ^ looks different from my implementation
import System.Environment
import System.Exit
import AST
import Data.Maybe (fromJust)
import Data.Monoid (All, getAll)
import Control.Monad(forM_)

type Name = String

-- | syntax
data Stx = 
    Stxlam Name Stx 
  | Stxident Name
  | Stxap Stx Stx
  | Stxmkpair Stx Stx
  | Stxfst Stx
  | Stxsnd Stx
  | Stxdiamond -- Lozenge symbol (C-k lz); inhabitant of ()
  deriving(Eq, Ord)

instance Show Stx where
  show (Stxlam name body) = "(λ " ++ name  ++ "  " ++ show body ++ ")"
  show (Stxident x) = x
  show (Stxap f x) = "($ " ++ show f ++ " " ++ show x  ++ ")"
  show (Stxmkpair l r) = "(, " ++ show l ++ " " ++ show r  ++ ")"
  show (Stxfst p) = "(fst " ++ show p ++ ")"
  show (Stxsnd p) = "(snd " ++ show p ++ ")"
  show Stxdiamond = "◊"

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
    head <- tuplehd atom tuple
    case head of 
        "λ" -> do 
          ((), x, body) <- tuple3f astignore atom toStx tuple
          return $ Stxlam x body
        "$" -> do 
          ((), f, x) <- tuple3f astignore toStx toStx tuple
          return $ Stxap f x
        "," -> do
            ((), l, r) <- tuple3f astignore toStx toStx tuple
            return $ Stxmkpair l r
        "fst" -> do 
            ((), x) <- tuple2f astignore toStx tuple
            return $ Stxfst x
        "snd" -> do 
            ((), x) <- tuple2f astignore toStx tuple
            return $ Stxsnd x
        _ -> Left $ "unknown head: " ++ "|" ++ astPretty tuple ++ "|"

toType :: AST -> Either Error Type
toType (Atom span "1") = Right Tyunit
toType tuple = do
    head <- tuplehd atom tuple
    case head of
        "*" -> do
            ((), l, r) <- tuple3f astignore toType toType tuple
            return $ Typair l r
        "→" -> do
            ((), l, r) <- tuple3f astignore toType toType tuple
            return $ Tyfn l r
        _ -> Left $ "unknown type head: " ++ "|" ++ astPretty tuple ++ "|"


-- (foo <type> <body>)
toDecl :: AST -> Either Error Decl
toDecl tuple = do
    (name, ty, body) <- tuple3f atom toType toStx tuple
    return $ Decl name ty body

toToplevel :: AST -> Either Error [Decl]
toToplevel ast = tuplefor toDecl ast

mainFile :: String -> IO ()
mainFile path = do
  file <- readFile path
  putStrLn $"file contents:"
  putStrLn $ file
  putStrLn $ "parsing..."
  ast <- case AST.parse file of
           Left failure -> print failure >> exitFailure
           Right success -> pure success
  putStrLn $ astPretty ast

  putStrLn $ "\nconvering to intermediate repr..."
  decls <- case toToplevel ast of
            Left failure -> print failure >> exitFailure
            Right d -> pure d
  putStrLn $ show decls
  forM_ decls  $ \(Decl name ty stx) -> do
        putStrLn $ "\ntype checking |" ++ name  ++ "|..."
        let ctx = []
        case tycheck ctx stx ty of
          Left err -> do putStrLn $ "  error ✗ " ++ err;
          Right () -> do 
            putStrLn $ "  success ✓";
            let outstx = nbe ty stx 
            putStr $ "  output: "
            putStrLn $ show outstx
  return ()

lspHandlers :: Handlers (LspM ())
lspHandlers = mconcat
  [ notificationHandler SInitialized $ \_not -> do
      let params = ShowMessageRequestParams MtInfo "Turn on code lenses?"
            (Just [MessageActionItem "Turn on", MessageActionItem "Don't"])
      _ <- sendRequest SWindowShowMessageRequest params $ \res ->
        case res of
          Right (Just (MessageActionItem "Turn on")) -> do
            let regOpts = CodeLensRegistrationOptions Nothing Nothing (Just False)
              
            _ <- registerCapability STextDocumentCodeLens regOpts $ \_req responder -> do
              let cmd = Command "Say hello" "lsp-hello-command" Nothing
                  rsp = List [CodeLens (mkRange 0 0 0 100) (Just cmd) Nothing]
              responder (Right rsp)
            pure ()
          Right _ ->
            sendNotification SWindowShowMessage (ShowMessageParams MtInfo "Not turning on code lenses")
          Left err ->
            sendNotification SWindowShowMessage (ShowMessageParams MtError $ "Something went wrong!\n" <> T.pack (show err))
      pure ()
  , requestHandler STextDocumentHover $ \req responder -> do
      let RequestMessage _ _ _ (HoverParams _doc pos _workDone) = req
          Position _l _c' = pos
          rsp = Hover ms (Just range)
          ms = HoverContents $ markedUpContent "lsp-demo-simple-server" "Hello world"
          range = Range pos pos
      responder (Right $ Just rsp)
  ]


mainLSP :: IO ()
mainLSP = do
  putStrLn $ "launching LSP server..."
  runServer $ ServerDefinition
    { onConfigurationChange = const $ pure $ Right ()
    , doInitialize = \env _req -> pure $ Right env
    , staticHandlers = lspHandlers
    , interpretHandler = \env -> Iso (runLspT env) liftIO
    , options = defaultOptions
    }
  return ()

main :: IO ()
main = do
  args <- getArgs
  case args of
   [] -> mainLSP
   ["lsp"] -> mainLSP
   [path] -> mainFile path
   _ -> (putStrLn "ERROR: expected single file path to parse, or 'lsp' to launch server") >> exitFailure


-- | type directed semantic lifting
stx2sem :: Type -> Stx -> Value
stx2sem Tyunit _ =  Vdiamond
stx2sem (Tyfn i o) f =  
  Vlam (\x -> stx2sem o (Stxap f (sem2stx i x)))
stx2sem (Typair l r) p = Vpair (stx2sem l $ Stxfst p) (stx2sem r $ Stxsnd p)

-- | type directed reification into syntax
sem2stx :: Type -> Value -> Stx
sem2stx Tyunit _ = Stxdiamond
sem2stx (Typair tl tr) (Vpair l r) = 
  Stxmkpair (sem2stx tl l) (sem2stx tr r)
-- | TODO: need fresh names
sem2stx (Tyfn i o) (Vlam f) = 
    let fresh = "fresh_x"
    in Stxlam fresh (sem2stx o $ f (stx2sem i (Stxident fresh)))
sem2stx _ (Vstx stx) = stx -- how do stuck terms make progress?
sem2stx _ stx = error $ "unhandled term in sem2stx: |" ++ show stx ++ "|."


-- | context used when building program denotation prior to NBE.
type ValCtx = [(Name, Value)]

-- | initial lifting into semantic domain.
denote :: ValCtx -> Stx -> Value
denote ctx (Stxident x) = fromJust $ lookup x ctx
denote ctx (Stxlam x body) = 
  Vlam $ \xv -> denote ((x, xv):ctx) body
denote ctx (Stxap f x) = 
  let (Vlam vf) = denote ctx f; vx = denote ctx x
  in vf vx
denote ctx (Stxmkpair l r) = 
 Vpair (denote ctx l) (denote ctx r)
denote ctx (Stxfst pair) = 
  let Vpair l r = denote  ctx pair in l
denote ctx (Stxsnd pair) = 
  let Vpair l r = denote  ctx pair in r
denote ctx (Stxdiamond) = Vdiamond

type TyCtx = [(Name, Type)]

-- | type infer
-- A judgement is something we know.
-- elimnation forms are inferred.
tyinfer :: TyCtx -> Stx -> Either Error Type
tyinfer ctx (Stxdiamond) = return Tyunit
tyinfer ctx (Stxident x) = 
  case lookup x ctx of
    Just ty -> return ty
    Nothing -> Left $ "unknown symbol: " ++ x
tyinfer ctx ap@(Stxap f x) = do 
  tf <- tyinfer ctx f
  case tf of
    Tyfn ti to -> do
        tycheck ctx x ti
        return to
    _ -> Left $ "invalid type for function |" ++ show f ++ "| in |" ++ show ap ++ "|." ++ 
                "expected function type, found |" ++ show tf  ++ "|."
tyinfer ctx (Stxfst pair) = do
  tpair <- tyinfer ctx pair
  case tpair of
    Typair tl tr -> return tl
    _ -> Left $ "invalid type for |" ++ show pair ++ "|" ++
                "found |" ++ show tpair ++ "|, expected tuple type."
tyinfer ctx (Stxsnd pair) = do
  tpair <- tyinfer ctx pair
  case tpair of
    Typair tl tr -> return tr
    _ -> Left $ "invalid type for |" ++ show pair ++ "|" ++
                "found |" ++ show tpair ++ "|, expected tuple type"
tyinfer ctx stx = Left $ "unimplemented tyinfer for |" ++ show stx ++ "|."
    

-- | type check
-- introduction forms are checked
tycheck :: TyCtx -> Stx -> Type -> Either Error ()
-- tycheck _ Stxdiamond t = 
--   if t == Tyunit
--   then Right ()
--   else Left $ "◊ has type unit, wanted it to have type " ++ show t
tycheck ctx (Stxlam x f) (Tyfn ti to) =  do
  -- tycheck ctx (Stxident x) ti
  tycheck ((x,ti):ctx) f to
  return ()
tycheck _ lam@(Stxlam _ _) t = 
  Left $ "ERR: lambda (" ++ show lam ++ ") " ++ 
         "must be demanded a function type, not " ++ show t
tycheck ctx (Stxmkpair l r) (Typair tl tr) = do
  tycheck ctx l tl
  tycheck ctx r tr
  return ()
tycheck _ pair@(Stxmkpair _ _) t = 
  Left $ "ERR: pair (" ++ show pair ++ ") " ++ 
          "must be demanded a pair type, not " ++ show t
tycheck ctx stx ty = do
   tyinfer <- tyinfer ctx stx
   if ty == tyinfer
   then return ()
   else Left $ "ERR: " ++ show stx ++ " demanded type |" ++ show ty ++ "|, but inferred |" ++ show tyinfer ++ "|."


nbe :: Type -> Stx -> Stx
nbe ty stx =  sem2stx ty (denote [] stx)

