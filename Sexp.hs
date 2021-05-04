module Sexp where
import qualified Data.List as L

data Loc = Loc { locix :: Int, locline :: Int, loccol :: Int } deriving(Eq)

instance Show Loc where
  show (Loc ix line col) = "Loc(" ++ show line ++ ":" ++ show col ++ " " ++ show ix ++ ")"

errAtLoc :: Loc -> String  -> String
errAtLoc (Loc _ line col) err =
  show line ++ ":" ++ show col ++ " " ++ err

data Span = Span { spanl :: Loc, spanr :: Loc } deriving(Eq)

instance Show Span where
  show (Span l r) = "Span(" ++ show l ++ " " ++ show r ++ ")"

errAtSpan :: Span -> String  -> String
errAtSpan (Span (Loc _ lline lcol) (Loc _ rline rcol)) err = 
    show lline  ++ ":" ++ show lcol ++ " - " ++ 
    show rline ++ ":" ++ show rcol ++ " " ++
    show err

data SExp = Tuple Span [SExp] | Lexeme Span String deriving (Show)

prettySExp :: SExp -> String
prettySExp (Lexeme _ l) = l
prettySExp (Tuple _ ls) = "(" ++ L.intercalate " " (map prettySExp ls) ++ ")"

sexpSpan :: SExp -> Span
sexpSpan (Tuple span _) = span
sexpSpan (Lexeme span _) = span

spanExtend :: Span -> Span -> Span
spanExtend (Span l r) (Span l' r') = Span l r'


data Token = Open Span | Close Span | TokLexeme Span String deriving(Show)

locNextCol :: Loc -> Loc
locNextCol (Loc ix line col) = Loc (ix+1) line (col+1)

locNextCols :: Int -> Loc -> Loc
locNextCols n (Loc ix line col) = Loc (ix+n) line (col+n)

locNextLine :: Loc -> Loc
locNextLine (Loc ix line col) = Loc (ix+1) (line+1) 1

isSigil :: Char -> Bool
isSigil '(' = True
isSigil ')' = True
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
    in (Open span):tokenize l' cs
tokenize l (')':cs) = 
    let l' = locNextCol l; span = Span l l'
    in (Close span):tokenize l' cs
tokenize l cs = 
    let (lex, cs') = L.span (not . isSigil) cs
        l' = locNextCols (length lex) l
        span = Span l l'
    in (TokLexeme span lex):tokenize l' cs'

tupleAppend :: SExp -> SExp -> SExp
tupleAppend (Lexeme _ _) s = error $ "cannot push into lexeme"
tupleAppend (Tuple span ss) s = Tuple (spanExtend span (sexpSpan s)) (ss ++ [s])

-- | invariant: stack, top only contain `Tuple`s.
doparse :: [Token] -- ^ stream of tokens
  -> SExp -- ^ currently building Sexp
  ->  [SExp] -- ^ stack of Sexp 
  -> Either String SExp -- final Sexp
doparse [] cur [] = Right cur
doparse [] cur (top:stack') =
  Left $ errAtLoc (spanl (sexpSpan top)) "unclosed open bracket."
doparse ((Open span):ts) cur stack = 
  doparse ts (Tuple span [])  (cur:stack) -- open new tuple
doparse ((Close span):ts) cur stack = 
    case stack of  -- pop stack, and append cur into top, make top cur
        (top:stack') -> doparse ts (tupleAppend top cur) stack'
        [] -> Left $ errAtSpan span "too many close parens." 
doparse ((TokLexeme span str):ts) cur stack = 
  doparse ts (tupleAppend cur (Lexeme span str)) stack -- append into tuple

-- | parse a string
parse :: String -> Either String SExp
parse s =
  let locBegin = Loc 0 1 1
      spanBegin = Span locBegin locBegin
  in doparse (tokenize locBegin s) (Tuple spanBegin []) []
