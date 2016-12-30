{
{-# LANGUAGE OverloadedStrings #-}
module Language.Bang.Parser where

import Control.Monad.Except
import Control.Monad.Reader

import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NE

import Data.Text (Text)

import Data.Maybe

import Text.PrettyPrint.HughesPJClass

import Language.Bang.Lexer
import Language.Bang.Types.Error
import Language.Bang.Types.SrcPos

import Debug.Trace

}

%name parseModulesP
%partial parseStmtP Stmt
%tokentype { Token SrcSpan }
%error { parseError }
%monad { Either ParseError }
-- %expect 8

%token
    varName     { TVarName $$ }
    varSym      { TVarSym $$ }
    conName     { TConName $$ }
    conSym      { TConSym $$ }
    string      { TLitString $$ }
    decimal     { TDecimal $$ }
    rational    { TRational $$ }
    '('         { TLParen $$ }
    ')'         { TRParen $$ }
    '{'         { TLBrace $$ }
    '}'         { TRBrace $$ }
    '['         { TLBracket $$ }
    ']'         { TRBracket $$ }
    ':'         { TColon $$ }
    ';'         { TSemicolon $$ }
    ','         { TComma $$ }
    '.'         { TDot $$ }
    '`'         { TBacktick $$ }
    '->'        { TArrow $$ }
    '='         { TEqual $$ }
    '|'         { TPipe $$ }
    '_'         { TWild $$ }
    '-'         { TVarSym ("-", $$) }
    module      { TModule $$ }
    forall      { TForall $$ }
    function    { TFunction $$ }
    let         { TLet $$ }
    return      { TReturn $$ }
    if          { TIf $$ }
    then        { TThen $$ }
    else        { TElse $$ }
    type        { TType $$ }
    case        { TCase $$ }
    of          { TOf $$ }
    do          { TDo $$ }

%%

Modules :: { [LPModule] }
        : List1(Module)                     { $1 }

Module :: { LPModule }
       : module QualName Defs               { mkSpanLocs [[$1], [locatedAt $2], map locatedAt $3] $ PModule $2 $3 }

QualName :: { LPQualName }
         : List1SepBy(QualConName, '.')     { mkSpanLoc (map locatedAt $1) $ foldr1App PQualName PPlainName $1 }

QualConName :: { Located Text }
            : conName                       { L (snd $1) $ fst $1 }

Defs :: { [LPDef] }
     : List(Def)                            { $1 }

Def :: { LPDef }
    : type conName OptTyVarList '=' ConList
        { mkSpanLocs [[$1], [snd $2], maybe [] (map locatedAt) $3, [$4], map locatedAt $5] $ PTypeDef (fst $2) (fromMaybe [] $3) $5 }
    | function varName '(' ArgList ')' OptTypeSig '=' Stmt
        { mkSpanLocs [[$1], [snd $2], [$3], map locatedAt $4, [$5], map locatedAt $ maybeToList $6, [$7], [locatedAt $8]] $ PFunDef (fst $2) $4 (undefined $6) $8 }

OptTypeSig :: { Maybe LPType }
           : ':' Type                   { Just $2 }
           | Empty                      { Nothing }

ConList :: { [LPDataCon] }
        : List1SepBy(Con, '|')          { $1 }

Con :: { LPDataCon }
    : conName                           { L (snd $1) $ PDataCon (fst $1) [] }
    | conName '{' ArgList '}'           { mkSpanLocs [[snd $1], [$2], map locatedAt $3, [$4]] $ PDataCon (fst $1) $3 }

ArgList :: { [LPArg] }
        : ListSepBy(Arg, ',')           { $1 }

Arg :: { LPArg }
    : varName ':' Type                  { mkSpanLoc [snd $1, $2, locatedAt $3] $ PArg (fst $1) $ Just $3 }
    | varName                           { L (snd $1) $ PArg (fst $1) Nothing }

Type :: { LPType }
     : Type '->' Type1                  { mkSpanLoc [locatedAt $1, $2, locatedAt $3] $ PTyApp (mkSpanLoc [locatedAt $1, $2] $ PTyApp (L $2 PTyArr) $1) $3 }
     | forall TyVarList '.' Type        { mkSpanLocs [[$1], map locatedAt $2, [$3], [locatedAt $4]] $ PTyForall $2 $4 }
     | Type1                            { $1 }

Type1 :: { LPType }
      : conName                          { L (snd $1) $ PTyCon (fst $1) }
      | '(' Type ')'                     { mkSpanLoc [$1, locatedAt $2, $3] $ PTyParen $2 }
      | TyVar                            { L (locatedAt $1) $ PTyTyVar $1 }
      | Type1 Type1                      { mkSpanLoc [locatedAt $1, locatedAt $2] $ PTyApp $1 $2 }
      | '[' Type ']'                     { mkSpanLoc [$1, locatedAt $2, $3] $ PTyApp (mkSpanLoc [$1, $3] PTyList) $2 }
      | '[' ']'                          { mkSpanLoc [$1, $2] PTyList }

TyVar :: { LPTyVar }
      : varName                         { L (snd $1) $ PTyVar (fst $1) }

OptTyVarList :: { Maybe [LPTyVar] }
             : Optional(TyVarList)      { $1 }

TyVarList :: { [LPTyVar] }
          : List1(TyVar)                { $1 }

Stmts :: { [LPStmt] }
      : List1SepBy(Stmt, ';')           { $1 }

Stmt :: { LPStmt }
     : let varName '=' Expr             { mkSpanLoc [$1, snd $2, $3, locatedAt $4] $ SLet (L (snd $2) $ PVarName $ fst $2) $4 }
     | return Expr                      { mkSpanLoc [$1, locatedAt $2] $ SRet $2 }
     | Expr                             { L (locatedAt $1) $ SExpr $1 }

Expr :: { LPExpr }
     : do '{' Stmts '}'                 { mkSpanLocs [[$1], [$2], map locatedAt $3, [$4]] $ EBlock $3 }
     | if Expr then Stmt                { mkSpanLoc [$1, locatedAt $2, $3, locatedAt $4] $ EIf $2 $4 $ L noSrcSpan $ SExpr $ L noSrcSpan $ EBlock [] }
     | if Expr then Stmt else Stmt      { mkSpanLoc [$1, locatedAt $2, $3, locatedAt $4, $5, locatedAt $6] $ EIf $2 $4 $6 }
     | Expr1 Operator Expr1             { mkSpanLoc [locatedAt $1, locatedAt $2, locatedAt $3] $ EBinOp $1 $2 $3 }
     | case Expr of AltList             { mkSpanLoc [$1, locatedAt $2, $3, locatedAt $4] $ ECase $2 (locatedWhat $4) }
     | Expr1                            { $1 }

Expr1 :: { LPExpr }
      : Expr2 Operator Expr1            { mkSpanLoc [locatedAt $1, locatedAt $2, locatedAt $3] $ EBinOp $1 $2 $3 }
      | Expr2                           { $1 }

Expr2 :: { LPExpr }
      : '-' Expr3                       { mkSpanLoc [$1, locatedAt $2] $ ENeg $2 }
      | Expr3                           { $1 }

Expr3 :: { LPExpr }
      : Lit                             { L (locatedAt $1) $ ELit $1 }
      | varName                         { L (snd $1) $ EVar $ L (snd $1) $ PVarName $ fst $1 }
      | conName                         { L (snd $1) $ ECon $ L (snd $1) $ PConName $ fst $1 }
      | '(' varSym ')'                  { mkSpanLoc [$1, snd $2, $3] $ EVar $ L (snd $2) $ PVarSym $ fst $2 }
      | '(' conSym ')'                  { mkSpanLoc [$1, snd $2, $3] $ ECon $ L (snd $2) $ PConSym $ fst $2 }
      | '(' Expr ')'                    { mkSpanLoc [$1, locatedAt $2, $3] $ EParen $2 }
      | Expr3 Expr3                     { mkSpanLoc [locatedAt $1, locatedAt $2] $ EApp $1 $2 }

AltList :: { Located [LPAlt] }
        : Alt                           { L (locatedAt $1) [$1] }
        | '{' ListSepBy(Alt, ';') '}'   { mkSpanLocs [[$1], map locatedAt $2, [$3]] $2}

Alt :: { LPAlt }
    : Pat '->' Stmt                     { mkSpanLoc [locatedAt $1, $2, locatedAt $3] $ PAlt $1 $3 }

Pat :: { LPPat }
    : Pat1 conSym Pat1                  { mkSpanLoc [locatedAt $1, snd $2, locatedAt $3] $ PBinOpPat $1 (fst $2) $3 }
    | Pat1                              { $1 }

Pat1 :: { LPPat }
    : varName                           { L (snd $1) $ PVarPat (fst $1) }
    | conName List(Pat1)                { mkSpanLocs [[snd $1], map locatedAt $2] $ PConPat (fst $1) $2 }
    | '_'                               { L $1 PWildPat }
    | '(' Pat ')'                       { mkSpanLoc [$1, locatedAt $2, $3] $ PParenPat $2 }

Lit :: { LPLit }
    : decimal                           { L (snd $1) $ PDecimalLit (fst $1) }
    | rational                          { L (snd $1) $ PRationalLit (fst $1) }
    | string                            { L (snd $1) $ PStringLit (fst $1) }

Operator :: { LPExpr }
         : '`' varName '`'              { mkSpanLoc [$1, snd $2, $3] $ EVar $ L (snd $2) $ PVarName $ fst $2 }
         | '`' conName '`'              { mkSpanLoc [$1, snd $2, $3] $ ECon $ L (snd $2) $ PConName $ fst $2 }
         | varSym                       { L (snd $1) $ EVar $ L (snd $1) $ PVarSym $ fst $1 }
         | conSym                       { L (snd $1) $ ECon $ L (snd $1) $ PConSym $ fst $1 }

List(p) : RevList(p)                            { reverse $1 }

RevList(p) : RevList(p) p                       { $2 : $1 }
           | Empty                              { [] }

List1(p) : RevList1(p)                          { reverse $1 }

RevList1(p) : RevList1(p) p                     { $2 : $1 }
            | p                                 { [$1] }

List1SepBy(p,s) : RevList1SepBy(p,s)            { reverse $1 }

ListSepBy(p,s) : List1SepBy(p,s)                { $1 }
               | Empty                          { [] }

RevList1SepBy(p,s) : RevList1SepBy(p,s) s p     { $3 : $1 }
                   | p                          { [$1] }

Optional(p) : p                                 { Just $1 }
            | Empty                             { Nothing }

Empty :: { () }
      : {- empty -}                             { () }

{

--------------
-- * Utilities
--------------

foldr1App :: (a -> b -> b) -> (a -> b) -> [a] -> b
foldr1App f g = go
    where
        go [x]    = g x
        go (x:xs) = f x (go xs)
        go []     = panic "foldr1App: empty list"

mkSpan :: [SrcSpan] -> SrcSpan
mkSpan = mkSpan' . filter (/= noSrcSpan)

mkSpan' :: [SrcSpan] -> SrcSpan
mkSpan' [] = noSrcSpan
mkSpan' xs = SrcSpan (minimum $ map spanStart xs) (maximum $ map spanEnd xs)

mkSpanLoc :: [SrcSpan] -> a -> Located a
mkSpanLoc = L . mkSpan

mkSpanLocs :: [[SrcSpan]] -> a -> Located a
mkSpanLocs = mkSpanLoc . concat

parseError :: [Token SrcSpan] -> Either ParseError a
parseError []    = Left $ ParserError "Parse error at end of input"
parseError (t:_) = Left $ ParserError $ "Parse error on " ++ show t

----------------------
-- * Module definition
----------------------

type LPModule = Located PModule

data PModule = PModule !LPQualName ![LPDef]
    deriving Show

instance Pretty PModule where
    pPrint _ = mempty

type LPDef = Located PDef

data PDef = PFunDef !Text ![LPArg] !(Maybe LPType) !LPStmt
          | PTypeDef !Text ![LPTyVar] ![LPDataCon]
          deriving Show

type LPQualName = Located PQualName

data PQualName = PQualName !(Located Text) !PQualName
               | PPlainName !(Located Text)
               deriving Show

type LPStmt = Located PStmt

data PStmt = SLet !LPVar !LPExpr
           | SRet !LPExpr
           | SExpr !LPExpr
           deriving Show

type LPDataCon = Located PDataCon

data PDataCon = PDataCon !Text ![LPArg] deriving Show

type LPArg = Located PArg

data PArg = PArg !Text !(Maybe LPType) deriving Show

type LPType = Located PType

data PType = PTyCon !Text
           | PTyApp !LPType !LPType
           | PTyParen !LPType
           | PTyTyVar !LPTyVar
           | PTyList
           | PTyArr
           | PTyForall [LPTyVar] !LPType
           deriving Show

type LPTyVar = Located PTyVar

newtype PTyVar = PTyVar Text deriving Show

type LPExpr = Located PExpr

data PExpr = EBinOp !LPExpr !LPExpr !LPExpr -- a op b
           | ENeg !LPExpr
           | EParen !LPExpr
           | EBlock ![LPStmt]
           | EIf !LPExpr !LPStmt !LPStmt
           | ECase !LPExpr ![LPAlt]
           | ELit !LPLit
           | EVar !LPVar
           | ECon !LPCon
           | EApp !LPExpr !LPExpr
           deriving Show

type LPAlt = Located PAlt

data PAlt = PAlt !LPPat !LPStmt deriving Show

type LPPat = Located PPat

data PPat = PVarPat !Text
          | PConPat !Text ![LPPat]
          | PBinOpPat !LPPat !Text !LPPat
          | PWildPat
          | PParenPat !LPPat
          deriving Show

type LPVar = Located PVar

data PVar = PVarName !Text
          | PVarSym !Text
          deriving Show

type LPCon = Located PCon

data PCon = PConName !Text
          | PConSym !Text
          deriving Show

type LPLit = Located PLit

data PLit = PDecimalLit !Integer
          | PRationalLit !Rational
          | PStringLit !Text
          deriving Show

-----------------
-- * Entry points
-----------------

-- | Parse a source file into a list of modules
parseModules :: Text -> Either ParseError [LPModule]
parseModules t = lexer t >>= parseModulesP . traceShowId

-- | Parse a line (or multiple lines) into a single statement to execute
parseStmt :: Text -> Either ParseError LPStmt
parseStmt t = lexer t >>= parseStmtP
}
