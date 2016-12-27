module Main where

import Language.Bang.Compiler

main :: IO ()
main = compile "tests/good/functions.bng"
