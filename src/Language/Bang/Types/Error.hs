{-# LANGUAGE DeriveDataTypeable #-}
module Language.Bang.Types.Error where

import Control.Exception

import Data.Typeable

data ParseError = LexerError String
                | ParserError String
                deriving (Show, Typeable)

instance Exception ParseError

-- | TODO call stack
panic :: String -> a
panic s = error $ "panic: " ++ s
