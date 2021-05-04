module AST where
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

data Delimiter = Round | Square | Flower deriving(Eq, Show)

data Token = Open Span Delimiter | Close Span Delimiter | Str Span String deriving(Show)

-- The Char of a tuple carries what the open bracket looks like.
data AST a = 
    Tuple { tuplespan :: Span, tupledelimiter :: Delimiter, tuplevals :: [AST a] } 
    | Atom { atomspan :: Span, atomval :: a } deriving (Show)

delimOpen :: Delimiter -> String
delimOpen Round = "("
delimOpen Square = "["
delimOpen Flower = "{"

delimClose Round = ")"
delimClose Square = "]"
delimClose Flower = "}"


astPretty :: AST String -> String
astPretty (Atom _ l) = l
astPretty (Tuple _ delim ls) = 
  delimOpen delim ++ L.intercalate " " (map astPretty ls) ++ delimClose delim

astSpan :: AST a -> Span
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
tokenize l cs = 
    let (lex, cs') = L.span (not . isSigil) cs
        l' = locNextCols (length lex) l
        span = Span l l'
    in (Str span lex):tokenize l' cs'

tupleAppend :: AST a -> AST a -> AST a
tupleAppend (Atom _ _) s = error $ "cannot push into atom"
tupleAppend (Tuple span delim ss) s = Tuple (spanExtend span (astSpan s)) delim (ss ++ [s])

-- | invariant: stack, top only contain `Tuple`s.
doparse :: [Token] -- ^ stream of tokens
  -> AST String -- ^ currently building AST
  ->  [AST String] -- ^ stack of AST 
  -> Either String (AST String) -- final AST
doparse [] cur [] = Right cur
doparse [] cur (top:stack') =
  Left $ errAtLoc (spanl (astSpan top)) "unclosed open bracket."
doparse ((Open span delim):ts) cur stack = 
  doparse ts (Tuple span delim [])  (cur:stack) -- open new tuple
doparse ((Close span delim):ts) cur stack = 
  if tupledelimiter cur == delim -- we close the current thing correctly
  then case stack of  -- pop stack, and append cur into top, make top cur
            (top:stack') -> doparse ts (tupleAppend top cur) stack'
            [] -> Left $ errAtSpan span "too many close parens." 
  else Left $ errAtLoc (spanl . tuplespan $ cur) "mismatched bracket (open) " ++ 
              "'" ++ (delimOpen (tupledelimiter cur)) ++ "'" ++ 
              "; " ++ 
              errAtLoc (spanl span) "mismatched bracket (close) " ++
              "'" ++ (delimClose delim) ++ "'"

doparse ((Str span str):ts) cur stack = 
  doparse ts (tupleAppend cur (Atom span str)) stack -- append into tuple

-- | parse a string
parse :: String -> Either String (AST String)
parse s =
  let locBegin = Loc 0 1 1
      spanBegin = Span locBegin locBegin
  in doparse (tokenize locBegin s) (Tuple spanBegin Flower []) []
