{
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE OverloadedStrings  #-}
module Language.Bang.Lexer (lexer, Token(..)) where

import Control.Monad.Except
import Control.Monad.State

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as T
import qualified Data.Text.Unsafe as T

import Data.Char
import Data.Maybe
import Data.Word

import Text.PrettyPrint.HughesPJClass

import Language.Bang.Types.Error
import Language.Bang.Types.SrcPos

-- we may not define anything but imports here. alex adds
-- additional imports after this block
}

----------------------------------------------
-- Define some macros for commonly used things
----------------------------------------------

-- as Alex does not handle Unicode, we emit (like GHC) bytes encoding the general
-- category of the input character to Alex and later extract the text of the character
-- from our own monad
$unilarge   = \x01
$unismall   = \x02
$unidigit   = \x03
$unisymbol  = \x04
$unispace   = \x05
$unigraphic = \x06
$uniidchar  = \x07

-- Whitespace characters
-- We convert \r\n and \n\r to \n, but otherwise leave newlines unchanged,
-- so we better match on all "normal" newlines. We do not match on Unicode
-- newlines right now
$nl    = [\n\r\f]
$nonl  = [^\n\r\f]
-- any character which is a valid space character
$spaces = [\v\ $unispace]

-- digits
$bindigit = 0-1
$octdigit = 0-7
$decdigit = 0-9
$hexdigit = [$decdigit A-F a-f]
$digit = [$decdigit $unidigit]

-- symbolic characters
$special   = [\(\)\,\;\[\]\`\{\}]
$ascsymbol = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~\:]
$symbol    = [$ascsymbol $unisymbol] # [$special \_\"\']

-- alphabetic characters
$large = [A-Z $unilarge]
$small = [a-z $unismall \_]

$graphic = [$small $large $symbol $digit $special $unigraphic \" \']
$idchar  = [$small $large $digit $uniidchar \']

-- string escape sequences
$backslash  = [\\]
$quote      = [\"]
$escapeChar = [abtnvfr $backslash $quote]

-- -----------------------------------------------------------------------------
-- Alex "Regular expression macros"

-- all known escape codes consisting of multiple characters
@escapeCode = "NUL"|"SOH"|"STX"|"ETX"|"EOT"|"ENQ"|"ACK"|"SO"|"SI"|"DLE"|"DC1"|"DC2"
    |"DC3"|"DC4"|"NAK"|"SYN"|"ETB"|"CAN"|"EM"|"SUB"|"ESC"|"FS"|"GS"|"RS"|"US"|"DEL"
-- a character escaped by some non-numeric escape code
@escapedChar = $backslash (@escapeCode|$escapeChar)
-- a character escaped by its Unicode code point
@escapedUnicode = $backslash $decdigit+

@varid     = $small $idchar*          -- variable identifiers
@conid     = $large $idchar*          -- constructor identifiers

@varsym    = ($symbol # \:) $symbol*  -- variable (operator) symbol
@consym    = \: $symbol*              -- constructor (operator) symbol

@decimal     = $decdigit+
@binary      = $bindigit+
@octal       = $octdigit+
@hexadecimal = $hexdigit+
@exponent    = [eE] [\-\+]? @decimal
@floatingPoint = @decimal \. @decimal @exponent? | @decimal @exponent

-- normal signed numerical literals can only be explicitly negative,
-- not explicitly positive (contrast @exponent)
@negative = \-
@signed = @negative ?

--- qualified stuff is not supported for now, but we leave this in here for a future implementation
--@qual = (@conid \.)+
--@qvarid = @qual @varid
--@qconid = @qual @conid
--@qvarsym = @qual @varsym
--@qconsym = @qual @consym

------------------------
-- Now define our tokens
------------------------

tokens :-
    -- tabs are always an error (except in string literals)
    <0, onLine> "\t"                          { lexerError "Tab character not allowed here" }
    -- if we find an empty line, we skip it. The longest prefix rule ensures we match this rule in this case
    <0> $spaces* $nl                          { skip }
    -- if we are on a line start, we consume as many spaces as possible. If there are no spaces, this does not matter
    <0> $spaces*                              { continueWith onLine $ emit $ ITSpaces . T.length }
    -- if we are on a line and find a newline, we finish the line and continue at the start of the next, consuming whitespace again
    <onLine> $nl                              { begin 0 }
    -- skip whitespace after the start of the line
    <onLine> $spaces+                         { skip }
    -- skip comments until the end of the line (and the newline rule transitions from there to the next state)
    <onLine> "--" $nonl*                      { skip }
    -- we need all special names first, so the lexer matches them as tokens instead of names/symbols
    <onLine> "("                               { emit $ const ITLParen }
    <onLine> ")"                               { emit $ const ITRParen }
    <onLine> ":"                               { emit $ const ITColon }
    <onLine> ";"                               { emit $ const ITSemicolon }
    <onLine> ","                               { emit $ const ITComma }
    <onLine> "->"                              { emit $ const ITArrow }
    <onLine> "="                               { emit $ const ITEqual }
    <onLine> "."                               { emit $ const ITDot }
    <onLine> "`"                               { emit $ const ITBacktick }
    <onLine> "{"                               { emit $ const ITLBrace }
    <onLine> "}"                               { emit $ const ITRBrace }
    <onLine> "["                               { emit $ const ITLBracket }
    <onLine> "]"                               { emit $ const ITRBracket }
    <onLine> "|"                               { emit $ const ITPipe }
    <onLine> "_"                               { emit $ const ITWild }
    <onLine> "module"                          { emit $ const ITModule }
    <onLine> "forall"                          { emit $ const ITForall }
    <onLine> "function"                        { emit $ const ITFunction }
    <onLine> "let"                             { emit $ const ITLet }
    <onLine> "return"                          { emit $ const ITReturn }
    <onLine> "if"                              { emit $ const ITIf }
    <onLine> "then"                            { emit $ const ITThen }
    <onLine> "else"                            { emit $ const ITElse }
    <onLine> "type"                            { emit $ const ITType }
    <onLine> "case"                            { emit $ const ITCase }
    <onLine> "of"                              { emit $ const ITOf }
    <onLine> "do"                              { emit $ const ITDo }
    <onLine> @signed @decimal                  { emit $ ITDecimal . textDecimal }
    <onLine> @signed "0b" @binary              { emit $ ITDecimal . textBinary }
    <onLine> @signed "0o" @octal               { emit $ ITDecimal . textOctal }
    <onLine> @signed "0x" @hexadecimal         { emit $ ITDecimal . textHexadecimal }
    <onLine> @floatingPoint                    { emit $ ITRational . textRational }
    -- if we find names or operators, we make sure that we do only retain the necessary characters in memory
    <onLine> @varid                            { emit $ ITVarName . T.copy }
    <onLine> @varsym                           { emit $ ITVarSym . T.copy }
    <onLine> @conid                            { emit $ ITConName . T.copy }
    <onLine> @consym                           { emit $ ITConSym . T.copy }
    -- if we find a quote character, we start a string literal, parse it into some chunks and concatenate them later
    <onLine> \"                                { begin string }
    -- if we find a closing quote, continue on a line
    <string> $quote                            { begin onLine }
    <string> [^ $quote $backslash]+            { emit ITLitPart }
    <string> @escapedChar                      { emit (ITLitPart . fromEscapeCode . T.drop 1) }
    <string> @escapedUnicode                   { emit (ITLitPart . T.singleton . chr . textDecimal . T.drop 1) }

----------------------------------------------------------------------------
-- A final code block to conclude the parser definition and expose it to the
-- outside world
----------------------------------------------------------------------------

{

---------------------
-- * Lexing utilities
---------------------

-------------
-- ** Numbers
-------------

runTextReader :: String -> T.Reader a -> Text -> a
runTextReader name rdr ts = case rdr ts of
    Left err       -> panic $ name ++ ": " ++ err
    Right (rs, "") -> rs
    Right (_, rst) -> panic $ name ++ ": non-exhaustive input: " ++ show rst ++ " on " ++ show ts

textBinary :: Integral a => Text -> a
textBinary = runTextReader "textBinary" $ T.signed binaryReader
    where
        binaryReader t = baseReader 2 $ fromMaybe t $ T.stripPrefix "0b" t

textOctal :: Integral a => Text -> a
textOctal = runTextReader "textOctal" $ T.signed octalReader
    where
        octalReader t = baseReader 8 $ fromMaybe t $ T.stripPrefix "0o" t

-- | Internal helper for binary and octal parsing. Base has to be <= 10!
baseReader :: Integral a => Int -> T.Reader a
baseReader base
    | base > 10 || base < 2
    = panic $ "Invalid base: " ++ show base
    | otherwise
    = go 0 False
    where
        go acc firstChar t = case T.uncons t of
            Nothing
                | firstChar -> Left "empty input"
                | otherwise -> Right (acc, T.empty)
            Just (c, t')
                | c >= '0'
                , c < chr (ord '0' + base)
                -> go (acc * fromIntegral base + fromIntegral (ord c - ord '0')) False t'
                | otherwise
                -> Left $ "invalid character: " ++ show c

textDecimal :: Integral a => Text -> a
textDecimal = runTextReader "textDecimal" $ T.signed T.decimal

textHexadecimal :: Integral a => Text -> a
textHexadecimal = runTextReader "textHexadecimal" $ T.signed T.hexadecimal

textRational :: Text -> Rational
textRational = runTextReader "textRational" T.rational

------------------
-- ** Escape codes
------------------

fromEscapeCode :: Text -> Text
fromEscapeCode code = T.singleton $ case code of
    "\""  -> '"'
    "\\"  -> '\\'
    "a"   -> '\a'
    "b"   -> '\b'
    "t"   -> '\t'
    "n"   -> '\n'
    "v"   -> '\v'
    "f"   -> '\f'
    "r"   -> '\r'
    "NUL" -> '\NUL'
    "SOH" -> '\SOH'
    "STX" -> '\STX'
    "ETX" -> '\ETX'
    "EOT" -> '\EOT'
    "ENQ" -> '\ENQ'
    "ACK" -> '\ACK'
    "SO"  -> '\SO'
    "SI"  -> '\SI'
    "DLE" -> '\DLE'
    "DC1" -> '\DC1'
    "DC2" -> '\DC2'
    "DC3" -> '\DC3'
    "DC4" -> '\DC4'
    "NAK" -> '\NAK'
    "SYN" -> '\SYN'
    "ETB" -> '\ETB'
    "CAN" -> '\CAN'
    "EM"  -> '\EM'
    "SUB" -> '\SUB'
    "ESC" -> '\ESC'
    "FS"  -> '\FS'
    "GS"  -> '\GS'
    "RS"  -> '\RS'
    "US"  -> '\US'
    "DEL" -> '\DEL'
    _ -> panic $ "fromEscapeCode: bad input: " ++ show code

---------------
-- * Data types
---------------

-- | Intermediate token before laying out code
data IToken = ITVarName !Text      -- ^ An identifier for a variable, starting with lower case letters
            | ITVarSym !Text       -- ^ An identifier for an operator in an expression
            | ITConName !Text      -- ^ An identifier for a constructor or type, starting with uppercase letters
            | ITConSym !Text       -- ^ An identifier for an operator in a type or expression
            | ITLitPart !Text      -- ^ Part of a string literal, has to be fused later to a literal
            | ITDecimal !Integer   -- ^ A number in decimal format
            | ITRational !Rational -- ^ A number in rational format (or scientific notation)
            | ITSpaces !Int        -- ^ A number of spaces
            | ITLParen             -- ^ '('
            | ITRParen             -- ^ ')'
            | ITColon              -- ^ ':'
            | ITSemicolon          -- ^ ';'
            | ITComma              -- ^ ','
            | ITArrow              -- ^ '->'
            | ITEqual              -- ^ '='
            | ITDot                -- ^ '.'
            | ITBacktick           -- ^ '`'
            | ITLBrace             -- ^ '{'
            | ITRBrace             -- ^ '}'
            | ITLBracket           -- ^ '['
            | ITRBracket           -- ^ ']'
            | ITPipe               -- ^ '|'
            | ITWild               -- ^ '_'
            | ITModule             -- ^ "module"
            | ITForall             -- ^ "forall"
            | ITFunction           -- ^ "function"
            | ITLet                -- ^ "let"
            | ITReturn             -- ^ "return"
            | ITIf                 -- ^ "if"
            | ITThen               -- ^ "then"
            | ITElse               -- ^ "else"
            | ITType               -- ^ "type"
            | ITCase               -- ^ "case"
            | ITOf                 -- ^ "of"
            | ITDo                 -- ^ "do"
            | ITLineIndent !Int    -- ^ Emitted during layout resolution
            | ITIndentStart !Int   -- ^ Emitted during layout resolution
            | ITLImplicitBrace     -- ^ Emitted during layout resolution
            | ITRImplicitBrace     -- ^ Emitted during layout resolution
            deriving Eq

-- | Token type passed on to the parser.
data Token l = TVarName !(Text, l)      -- ^ An identifier for a variable, starting with lower case letters
             | TVarSym !(Text, l)       -- ^ An identifier for an operator in an expression
             | TConName !(Text, l)      -- ^ An identifier for a constructor or type, starting with uppercase letters
             | TConSym !(Text, l)       -- ^ An identifier for an operator in a type or expression
             | TLitString !(Text, l)    -- ^ A string literal
             | TDecimal !(Integer, l)   -- ^ A number in decimal format
             | TRational !(Rational, l) -- ^ A number in rational format (or scientific notation)
             | TLParen l                -- ^ '('
             | TRParen l                -- ^ ')'
             | TColon l                 -- ^ ':'
             | TSemicolon l             -- ^ ';'
             | TComma l                 -- ^ ','
             | TArrow l                 -- ^ '->'
             | TEqual l                 -- ^ '='
             | TDot l                   -- ^ '.'
             | TBacktick l              -- ^ '`'
             | TLBrace l                -- ^ '{'
             | TRBrace l                -- ^ '}'
             | TLBracket l              -- ^ '['
             | TRBracket l              -- ^ ']'
             | TPipe l                  -- ^ '|'
             | TWild l                  -- ^ '_'
             | TModule l                -- ^ "module"
             | TForall l                -- ^ "forall"
             | TFunction l              -- ^ "function"
             | TLet l                   -- ^ "let"
             | TReturn l                -- ^ "return"
             | TIf l                    -- ^ "if"
             | TThen l                  -- ^ "then"
             | TElse l                  -- ^ "else"
             | TType l                  -- ^ "type"
             | TCase l                  -- ^ "case"
             | TOf l                    -- ^ "of"
             | TDo l                    -- ^ "do"
           deriving (Show, Functor) -- TODO remove show. can we also remove functor?

instance Pretty (Token l) where
    pPrint t = case t of
        TVarName (txt, _)   -> text $ T.unpack txt
        TVarSym (txt, _)    -> text $ T.unpack txt
        TConName (txt, _)   -> text $ T.unpack txt
        TConSym (txt, _)    -> text $ T.unpack txt
        TLitString (txt, _) -> text $ show txt
        TDecimal (n, _)     -> integer n
        TRational (r, _)    -> rational r
        TLParen _           -> char '('
        TRParen _           -> char ')'
        TColon _            -> char ':'
        TSemicolon _        -> char ';'
        TComma _            -> char ','
        TArrow _            -> text "->"
        TEqual _            -> char '='
        TDot _              -> char '.'
        TBacktick _         -> char '`'
        TLBrace _           -> char '{'
        TRBrace _           -> char '}'
        TLBracket _         -> char '['
        TRBracket _         -> char ']'
        TPipe _             -> char '|'
        TWild _             -> char '_'
        TModule _           -> text "module"
        TForall _           -> text "forall"
        TFunction _         -> text "function"
        TLet _              -> text "let"
        TReturn _           -> text "return"
        TIf _               -> text "if"
        TThen _             -> text "then"
        TElse _             -> text "else"
        TType _             -> text "type"
        TCase _             -> text "case"
        TOf _               -> text "of"
        TDo _               -> text "do"

-- | Convert an intermediate token to a token
convertITLit :: IToken -> l -> Token l
convertITLit i l = case i of
    ITVarName name     -> TVarName (name, l)
    ITVarSym name      -> TVarSym (name, l)
    ITConName name     -> TConName (name, l)
    ITConSym name      -> TConSym (name, l)
    ITLitPart str      -> TLitString (str, l)
    ITDecimal n        -> TDecimal (n, l)
    ITRational r       -> TRational (r, l)
    ITSpaces{}         -> panic "convertITLit: spaces"
    ITLParen           -> TLParen l
    ITRParen           -> TRParen l
    ITColon            -> TColon l
    ITSemicolon        -> TSemicolon l
    ITComma            -> TComma l
    ITArrow            -> TArrow l
    ITEqual            -> TEqual l
    ITDot              -> TDot l
    ITBacktick         -> TBacktick l
    ITLBrace           -> TLBrace l
    ITRBrace           -> TRBrace l
    ITLBracket         -> TLBracket l
    ITRBracket         -> TRBracket l
    ITPipe             -> TPipe l
    ITWild             -> TWild l
    ITModule           -> TModule l
    ITForall           -> TForall l
    ITFunction         -> TFunction l
    ITLet              -> TLet l
    ITReturn           -> TReturn l
    ITIf               -> TIf l
    ITThen             -> TThen l
    ITElse             -> TElse l
    ITType             -> TType l
    ITCase             -> TCase l
    ITOf               -> TOf l
    ITDo               -> TDo l
    ITLineIndent{}     -> panic "convertITLit: line indent"
    ITIndentStart{}    -> panic "convertITLit: indent start"
    ITLImplicitBrace   -> TLBrace l
    ITRImplicitBrace   -> TRBrace l

-- | Convert intermediate tokens to real tokens and fuse adjacent string
--   literals into a single string.
fuseStrings :: [Located IToken] -> [Token SrcSpan]
fuseStrings [] = []
fuseStrings (L loc x:xs) = case x of
    ITLitPart t -> case span (isLitPart . locatedWhat) xs of
        (litParts, ys) -> TLitString (copyConcat $ t : map (geItLitPart . locatedWhat) litParts, loc) : fuseStrings ys
    _ -> convertITLit x loc : fuseStrings xs
    where
        geItLitPart (ITLitPart t) = t
        geItLitPart _             = panic "geItLitPart: wrong constructor"
        isLitPart ITLitPart{}     = True
        isLitPart _               = False
        -- if we find exactly one text element, we copy it to avoid retaining references to the file we are parsing
        -- otherwise we have non-empty text literals and will copy them anyway
        copyConcat [t] = T.copy t
        copyConcat ts  = T.concat ts

-- | Run the lexer on the given input string.
lexer :: Text -> Either ParseError [Token SrcSpan]
lexer t = fuseStrings <$> (lexerLoop t >>= resolveLayout)

------------------
-- ** Lexing monad
------------------

type Lexer = StateT Int (Except ParseError)

runLexer :: Lexer a -> Int -> Either ParseError (a, Int)
runLexer m sc = runExcept (runStateT m sc)

lexerError :: String -> Lexer a
lexerError = throwError . LexerError

skip :: Lexer (Maybe a)
skip = pure Nothing

setStartCode :: Int -> Lexer ()
setStartCode = put

continueWith :: Int -> Lexer a -> Lexer a
continueWith n l = do
    setStartCode n
    l

begin :: Int -> Lexer (Maybe a)
begin n = continueWith n skip

emit :: (Text -> a) -> Lexer (Maybe (Text -> a))
emit = pure . Just

lexerLoop :: Text -> Either ParseError [Located IToken]
lexerLoop = go 0 . mkAlexInput
    where
        go sc i = case alexScan i sc of
            AlexEOF
                | sc == string
                -> Left $ LexerError "Unterminated string literal"
                | otherwise
                -> Right []
            AlexError rmng     -> Left $ LexerError $ mkLexError rmng sc
            AlexSkip  i' _     -> go sc i'
            AlexToken i' _ act -> do
                let (srcSpan, txt, i'') = getNextAlexInput i'
                (mf, sc') <- runLexer act sc
                xs <- go sc' i''
                pure $ maybe id ((:) . L srcSpan . ($ txt)) mf $ xs

mkLexError :: AlexInput -> Int -> String
mkLexError input sc = errLoc ++ "lexical error " ++ errPos ++ cStr
    where
        cStr = case T.uncons $ inputText input of
            Just (c, _) -> "at character " ++ show c
            Nothing     -> "at the end of input"
        errPos
            | sc == string
            = "in string/character literal "
            | otherwise
            = ""
        errLoc = show $ inputPosition input

data AlexInput = AlexInput {
     inputTokenStart :: !SrcPos -- ^ Start of the token, updated every time we emit a token
    ,inputTokenEnd   :: !SrcPos -- ^ Current end of the token, updated every time we emit a token and on every character
    ,inputPosition   :: !SrcPos -- ^ Current position, updated on every character
    ,inputTokenText  :: !Text   -- ^ Text at the start of the token
    ,inputTokenChars :: !Int    -- ^ Number of 16 bit words of the current token (to quickly slice the text buffer)
    ,inputText       :: !Text   -- ^ Current text, updated on every character
}

mkAlexInput :: Text -> AlexInput
mkAlexInput t = AlexInput {
     inputTokenStart = SrcPos 1 1
    ,inputTokenEnd   = SrcPos 1 0
    ,inputPosition   = SrcPos 1 1
    ,inputTokenText  = t
    ,inputTokenChars = 0
    ,inputText       = t
}

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte input = do
    (c, t) <- T.uncons $ inputText input
    case c of
        -- check if we find a '\r\n' or '\n\r' and handle it as a single newline
        '\n' | Just ('\r', t') <- T.uncons t -> step '\n' t' 2
        '\r' | Just ('\n', t') <- T.uncons t -> step '\n' t' 2
        -- otherwise we have a plain character (well, maybe something we must handle with Unicode...)
        _ -> step c t $ T.iter_ (inputText input) 0
    where
        step :: Char -> Text -> Int -> Maybe (Word8, AlexInput)
        step c t word16s = do
            let b = charToWord8 c
                newInput = input {
                     inputTokenEnd   = inputPosition input
                    ,inputPosition   = moveSrcPos (inputPosition input) c
                    ,inputTokenChars = inputTokenChars input + word16s
                    ,inputText       = t
                }
            b `seq` newInput `seq` pure (b, newInput)
        nonGraphic, upper, lower, digit, symbol, space', otherGraphic, uniIdChar :: Word8
        nonGraphic   = 0x00
        upper        = 0x01
        lower        = 0x02
        digit        = 0x03
        symbol       = 0x04
        space'       = 0x05
        otherGraphic = 0x06
        uniIdChar    = 0x07
        charToWord8 :: Char -> Word8
        charToWord8 c
            | ord c <= 0x07 = nonGraphic
            | ord c <= 0x7f = fromIntegral $ ord c
          -- alex does not handle Unicode, so we just output a replacement code
          -- for these characters and retrieve them later via 'getNextAlexInput'
            | otherwise     = classifyCharacter c
        classifyCharacter :: Char -> Word8
        classifyCharacter c = case generalCategory c of
            UppercaseLetter       -> upper
            LowercaseLetter       -> lower
            TitlecaseLetter       -> upper
            ModifierLetter        -> uniIdChar
            OtherLetter           -> lower
            NonSpacingMark        -> uniIdChar
            SpacingCombiningMark  -> otherGraphic
            EnclosingMark         -> otherGraphic
            DecimalNumber         -> digit
            LetterNumber          -> otherGraphic
            OtherNumber           -> digit
            ConnectorPunctuation  -> symbol
            DashPunctuation       -> symbol
            OpenPunctuation       -> otherGraphic
            ClosePunctuation      -> otherGraphic
            InitialQuote          -> otherGraphic
            FinalQuote            -> otherGraphic
            OtherPunctuation      -> symbol
            MathSymbol            -> symbol
            CurrencySymbol        -> symbol
            ModifierSymbol        -> symbol
            OtherSymbol           -> symbol
            Space                 -> space'
            _other                -> nonGraphic

-- | Get the input for the next token, retrieve the source span of the last one,
--   its content and the new input
getNextAlexInput :: AlexInput -> (SrcSpan, Text, AlexInput)
getNextAlexInput input = (SrcSpan start end, T.takeWord16 words16 $ inputTokenText input, newInput)
    where
        start    = inputTokenStart input
        end      = inputTokenEnd input
        words16  = inputTokenChars input
        newInput = input {
             inputTokenStart = inputPosition input
            ,inputTokenEnd   = (\ x -> x { srcPosColumn = srcPosColumn x - 1 }) $ inputPosition input
            ,inputTokenText  = inputText input
            ,inputTokenChars = 0
        }

-- Unused:

--alexInputPrevChar :: AlexInput -> Char

---------------------------------------------------------------------------
-- * Layout algorithm taken and modified from the the Haskell report (2010)
---------------------------------------------------------------------------

type Context = Int
type ContextStack = [Context]

-- {n} = ITIndentStart n = indent by n after something starting indention
-- <n> = ITLineIndent n = denotes a start of a line with n white space

setIndents :: [Located IToken] -> [Located IToken]
-- If a let, where, do, or of keyword is not followed by an left brace, the token {n}
-- is inserted after the keyword, where n is the indentation of the next lexeme if there is one, or 0 if the end of file has been reached.
setIndents (L l1 t:L _ ITSpaces{}:xs)
    | isIndentStarter t
    = setIndents (L l1 t:xs)
setIndents (L l1 t:L l2 x:xs)
    | isIndentStarter t
    , x /= ITLBrace
    = L l1 t : L noSrcSpan (ITIndentStart n) : setIndents (L l2 x:xs)
    where
        n = srcPosColumn (spanStart l2) - 1 -- starts at column 1 for no indention
setIndents [L l t]
    | isIndentStarter t
    = [L l t, L noSrcSpan (ITIndentStart 0)]
-- Where the start of a lexeme is preceded only by white space on the same line, this lexeme is preceded
-- by <n> where n is the indentation of the lexeme, provided that it is not, as a consequence of the first two rules, preceded by {n}.
setIndents (L _ (ITSpaces n):xs) = case xs of
    L _ ITIndentStart{} : _ -> setIndents xs
    _ -> L noSrcSpan (ITLineIndent n) : setIndents xs
-- skip the rest
setIndents (x:xs) = x : setIndents xs
setIndents []     = []

isIndentStarter :: IToken -> Bool
isIndentStarter ITDo = True
isIndentStarter ITOf = True
isIndentStarter _    = False

layout :: [Located IToken] -> ContextStack -> Either ParseError [Located IToken]
layout (L l (ITLineIndent n): ts) (m : ms)
    | n == m
    = (L noSrcSpan ITSemicolon :) <$> layout ts (m : ms)
    | n < m
    = (L noSrcSpan ITRImplicitBrace :) <$> layout (L l (ITLineIndent n): ts) ms
layout (L _ ITLineIndent{}: ts) ms = layout ts ms
layout (L _ (ITIndentStart n) : ts) (m : ms)
    | n > m
    = (L noSrcSpan ITLImplicitBrace :) <$> layout ts (n : m : ms)
layout (L _ (ITIndentStart n) : ts) []
    | n > 0
    = (L noSrcSpan ITLImplicitBrace :) <$> layout ts [n]
layout (L _ (ITIndentStart n) : ts) ms
    = (L noSrcSpan ITLImplicitBrace :)
    . (L noSrcSpan ITRImplicitBrace :)
    <$> layout (L noSrcSpan (ITLineIndent n): ts) ms
layout (L l ITRBrace : ts) (0 : ms) = (L l ITRBrace :) <$> layout ts ms
layout (L l ITRBrace : _) _ = Left $ LexerError $ shows (spanStart l) ": Encountered } without preceding {"
layout (L l ITLBrace : ts) ms = (L l ITLBrace :) <$> layout ts (0 : ms)
layout (t : ts) ms = (t :) <$> layout ts ms
layout [] [] = Right []
layout [] (m : ms)
    | m /= 0
    = (L noSrcSpan ITRImplicitBrace :) <$> layout [] ms
    | otherwise
    = Left $ LexerError "Missing closing right brace at end of input"

resolveLayout :: [Located IToken] -> Either ParseError [Located IToken]
resolveLayout xs = layout (setIndents xs) []
}
