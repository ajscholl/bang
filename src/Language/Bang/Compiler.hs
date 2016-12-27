module Language.Bang.Compiler where

import Control.Exception

import Data.Text (Text)
import qualified Data.Text.IO as T

import Text.PrettyPrint.HughesPJClass

import Language.Bang.Parser
import Language.Bang.Types.Error
import Language.Bang.Types.SrcPos

cliMain :: IO ()
cliMain = putStrLn "Implement CLI"

replMain :: IO ()
replMain = putStrLn "Implement REPL"

compile :: FilePath -> IO ()
compile fp = do
    t <- T.readFile fp
    case compileText t of
        Left err -> throwIO err
        Right md -> putStrLn $ render $ pPrint $ map locatedWhat md

compileText :: Text -> Either ParseError [LPModule]
compileText t = parseModules t
