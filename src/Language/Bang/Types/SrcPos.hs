{-# LANGUAGE DeriveFunctor      #-}
module Language.Bang.Types.SrcPos where

import Text.PrettyPrint.HughesPJClass

data SrcPos = SrcPos {
     srcPosLine   :: !Int -- ^ Line number, starts from 1
    ,srcPosColumn :: !Int -- ^ Column number, starts from 1
} deriving (Eq, Ord) -- do not change the order as the derived Ord instance depends on it.

instance Show SrcPos where
    showsPrec p (SrcPos ln col) = showsPrec p ln . (':' :) . showsPrec p col

instance Pretty SrcPos where
    pPrint (SrcPos line column) = pPrint line <> colon <> pPrint column

data SrcSpan = SrcSpan {
     spanStart :: !SrcPos -- ^ Position of the first character, i.e. line 1, column 1
    ,spanEnd   :: !SrcPos -- ^ Position of the last character, i.e. line 1, column 3 (for the word "end" in an empty document)
} deriving Eq

instance Show SrcSpan where
    showsPrec p (SrcSpan start end) = showsPrec p start . ('-':) . showsPrec p end

instance Pretty SrcSpan where
    pPrint (SrcSpan start end) = pPrint start <> char '-' <> pPrint end

data Located a = L {
     locatedAt   :: !SrcSpan
    ,locatedWhat :: !a
} deriving Show

instance Functor Located where
    fmap f (L s a) = L s (f a)

moveSrcPos :: SrcPos -> Char -> SrcPos
moveSrcPos (SrcPos line column) c
    | c == '\n' || c == '\r' || c == '\f'
    = SrcPos (line + 1) 1
    | otherwise
    = SrcPos line (column + 1)

noSrcSpan :: SrcSpan
noSrcSpan = SrcSpan noSrcPos noSrcPos

noSrcPos :: SrcPos
noSrcPos = SrcPos 0 0
