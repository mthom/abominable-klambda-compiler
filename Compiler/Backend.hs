{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Compiler.Backend where

import Interpreter.AST
import Control.Applicative
import Control.Monad.Reader hiding (lift)
import Control.Monad.State hiding (lift)
import Control.Monad.Writer hiding (lift)
import Data.Attoparsec.Text
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Debug.Trace
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Compiler.CodeGenerator
import Compiler.IR
import Compiler.Parser
import Compiler.Patterns
import Compiler.Utils
import System.Environment.FindBin
import System.IO
import Core.Types
import Core.Utils

type FileName = T.Text

hPutModuleLn :: Handle -> Symbol -> [Symbol] -> IO ()
hPutModuleLn h moduleName modules = do      
  T.hPutStrLn h "{-# LANGUAGE BangPatterns #-}"
  T.hPutStrLn h "{-# LANGUAGE OverloadedStrings #-}"
  T.hPutStrLn h "{-# LANGUAGE Strict #-}"
  T.hPutStrLn h "{-# LANGUAGE StrictData #-}"
  T.hPutStrLn h "{-# LANGUAGE ViewPatterns #-}"
  T.hPutStrLn h ""
  T.hPutStrLn h $ "module " <> moduleName <> " where"
  T.hPutStrLn h ""
  T.hPutStrLn h "import Control.Monad.Except"
  T.hPutStrLn h "import Control.Parallel"
  T.hPutStrLn h "import Environment"
  T.hPutStrLn h "import Primitives as Primitives"
  T.hPutStrLn h "import Backend.Utils"
  T.hPutStrLn h "import Types as Types"
  T.hPutStrLn h "import Utils"
  T.hPutStrLn h "import Wrap"
  
  mapM_ (\modName -> T.hPutStrLn h ("import " <> modName)) modules

  T.hPutStrLn h ""
  T.hPutStrLn h "{-"
  T.hPutStrLn h "Copyright (c) 2015, Mark Tarver"
  T.hPutStrLn h "All rights reserved."
  T.hPutStrLn h ""
  T.hPutStrLn h "Redistribution and use in source and binary forms, with or without"
  T.hPutStrLn h "modification, are permitted provided that the following conditions are met:"
  T.hPutStrLn h ""
  T.hPutStrLn h "1. Redistributions of source code must retain the above copyright"
  T.hPutStrLn h "   notice, this list of conditions and the following disclaimer."
  T.hPutStrLn h "2. Redistributions in binary form must reproduce the above copyright"
  T.hPutStrLn h "   notice, this list of conditions and the following disclaimer in the"
  T.hPutStrLn h "   documentation and/or other materials provided with the distribution."
  T.hPutStrLn h "3. The name of Mark Tarver may not be used to endorse or promote products"
  T.hPutStrLn h "   derived from this software without specific prior written permission."
  T.hPutStrLn h ""
  T.hPutStrLn h "THIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY"
  T.hPutStrLn h "EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED"
  T.hPutStrLn h "WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE"
  T.hPutStrLn h "DISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY"
  T.hPutStrLn h "DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES"
  T.hPutStrLn h "(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;"
  T.hPutStrLn h "LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND"
  T.hPutStrLn h "ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT"
  T.hPutStrLn h "(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS"
  T.hPutStrLn h "SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."
  T.hPutStrLn h "-}"
  T.hPutStrLn h ""

insertBackendsCode :: Handle -> Table -> [ExpQ]
insertBackendsCode h tbl = catMaybes $ map insertBackend tbl
    where insertBackend (name, BackendFunc hName args _) = 
            let hName' = "kl_" <> haskName hName in
            if length args > 0 then
                Just (appE (appE (funcExpT "insertFunction") (stringE (T.unpack name)))
                           (appE (appE (funcExpT "wrapNamed") (stringE (T.unpack name)))
                           (varE (mkNameT hName'))))
            else
                Just (appE (appE (funcExpT "insertFunction") (stringE (T.unpack name)))
                           (appE (appE (funcExpT "PL") (stringE (T.unpack name)))
                           (varE (mkNameT hName'))))
          insertBackend _ = Nothing

myPprint :: Ppr a => a -> T.Text
myPprint = T.pack . strip  . pprint
    where strip ('\\' : '\\' : 'n' : (!s)) = '\\' : 'n' : strip s
          strip ('\\' : '"' : (!s)) = strip s
          strip ((!c) : (!s)) = c : strip s
          strip [] = []

writeInsertFunctionCode :: Symbol -> Symbol -> Table -> [Symbol] -> IO ()
writeInsertFunctionCode modPrefix folderName tbl modules = do
  h <- openFile (T.unpack $ folderName <> "/" <> "FunctionTable.hs") WriteMode
  hPutModuleLn h (modPrefix <> ".FunctionTable") modules
               
  let inserts = insertBackendsCode h tbl
  body <- runQ $ doE (map noBindS inserts)
  let decl = FunD (mkName "functions") [Clause [] (NormalB body) []]

  T.hPutStrLn h (myPprint decl)

hPutExprLn :: Handle -> Table -> Symbol -> [Symbol] -> Int -> [SExpr] -> IO ()
hPutExprLn h tbl moduleName mods count es = do
  let es' = map (\e -> TrapError e (Lambda "E" (Lit (Str "E")))) es

  lines <- concat <$>
           mapM (\e -> evalSC (stmts <$> evaluationOrder (toCExpr (bakeFreeVars [] e)))
                              tbl) es'

  body <- runQ $ doE lines
  let decl = FunD (mkName ("expr" ++ show count)) [Clause [] (NormalB body) []]
  sig <- funcType (mkName ("expr" ++ show count)) 0

  T.hPutStrLn h (myPprint sig) 
  T.hPutStrLn h (myPprint decl)

funcType :: Quasi m => Name -> Int -> m Dec
funcType name n = runQ $ sigD name (typeSig n)
    where typeSig 0 = [t| KLContext Env KLValue |]
          typeSig n = [t| KLValue -> $(typeSig (n-1)) |]

preprocess :: [TopLevel] -> Table
preprocess = map addToTable
    where addToTable (Defun name args body) = (name, BackendFunc name args body)
          addToTable (SE e) = ("expr000", Expr e)

buildTable :: Symbol -> Symbol -> (Table, [Symbol], Int) -> FileName -> IO (Table, [Symbol], Int)
buildTable modPrefix folderName (tbl, modNames, count) file = do
  let moduleName = haskName $ T.toTitle
                            $ T.replace "klambda/" ""
                            $ T.replace "minikanren/" ""
                            $ T.replace ".kl" "" file

  progPath <- getProgPath
  contents <- T.readFile (progPath ++ "/" ++ T.unpack file)

  case parseOnly parseTopLevels contents of
    Right tls -> do
      let tbl' = tbl ++ preprocess tls
          hsFile = moduleName <> ".hs"
      newCount <- writeSources tbl' tls modNames
                  (folderName <> "/" <> moduleName <> ".hs")
                  (modPrefix  <> "." <> moduleName) count
      return (tbl',
              modNames ++ [modPrefix <> "." <> moduleName],
              newCount)
                           
writeSources :: Table -> [TopLevel] -> [Symbol] -> FileName -> Symbol ->
                Int -> IO Int
writeSources tbl tls mods file moduleName count = 
  withFile (T.unpack file) WriteMode $ \h -> do
    hPutModuleLn h moduleName mods
    es <- catMaybes <$> mapM (writeSource h) tls

    T.putStrLn $ "Writing " <> moduleName

    hPutExprLn h tbl moduleName mods count es
    return (count+1)
  where
    writeSource h (Defun name args e) = do
      sgn <- funcType (mkHName name) (length args)
      dec <- evalSC (functionDecl name args e) tbl

      T.hPutStrLn h (myPprint sgn)
      T.hPutStrLn h (myPprint dec)
      T.hPutStrLn h ""
      return Nothing
    writeSource _ (SE e) = return (Just e)

klFiles = [ "klambda/toplevel.kl"
          , "klambda/core.kl"
          , "klambda/sys.kl"
          , "klambda/sequent.kl"
          , "klambda/yacc.kl"
          , "klambda/reader.kl"
          , "klambda/prolog.kl"
          , "klambda/track.kl"
          , "klambda/load.kl"
          , "klambda/writer.kl"
          , "klambda/macros.kl"  
          , "klambda/declarations.kl"
          , "klambda/types.kl"
          , "klambda/t-star.kl"]

primDefTuple klName hName arity = (klName, PrimFunc klName hName arity)

primitiveTable :: Table
primitiveTable = [primDefTuple "intern" "intern" 1,
                  primDefTuple "pos" "pos" 2,
                  primDefTuple "tlstr" "tlstr" 1,
                  primDefTuple "cn" "cn" 2,
                  primDefTuple "str" "str" 1,
                  primDefTuple "string?" "stringP" 1,
                  primDefTuple "n->string" "nToString" 1,
                  primDefTuple "string->n" "stringToN" 1,
                  primDefTuple "set" "klSet" 2,
                  primDefTuple "value" "value" 1,
                  primDefTuple "simple-error" "simpleError" 1,
                  primDefTuple "error-to-string" "errorToString" 1,
                  primDefTuple "cons" "klCons" 2,
                  primDefTuple "hd" "hd" 1,
                  primDefTuple "tl" "tl" 1,
                  primDefTuple "cons?" "consP" 1,
                  primDefTuple "=" "eq" 2,
                  primDefTuple "type" "typeA" 2,
                  primDefTuple "absvector" "absvector" 1,
                  primDefTuple "address->" "addressTo" 3,
                  primDefTuple "<-address" "addressFrom" 2,
                  primDefTuple "absvector?" "absvectorP" 1,
                  primDefTuple "write-byte" "writeByte" 2,
                  primDefTuple "read-byte" "readByte" 1,
                  primDefTuple "open" "openStream" 2,
                  primDefTuple "close" "closeStream" 1,
                  primDefTuple "get-time" "getTime" 1,
                  primDefTuple "+" "add" 2,
                  primDefTuple "-" "Primitives.subtract" 2,
                  primDefTuple "*" "multiply" 2,
                  primDefTuple "/" "divide" 2,
                  primDefTuple ">" "greaterThan" 2,
                  primDefTuple "<" "lessThan" 2,
                  primDefTuple ">=" "greaterThanOrEqualTo" 2,
                  primDefTuple "<=" "lessThanOrEqualTo" 2,
                  primDefTuple "number?" "numberP" 1,
                  primDefTuple "eval-kl" "evalKL" 1,
                  primDefTuple "Excep" "Excep" 1]
              
functionDecl :: (MonadIO m, Quasi m) => Symbol -> ParamList -> SExpr -> SourceContext m Dec
functionDecl name args e = do
  let !haskFunName = mkHName name
      !vars        = map (BangP . VarP . mkHName) args
  !body <- funcBody (toCExpr (bakeFreeVars args e))
  return $! FunD haskFunName [Clause vars (NormalB body) []]

getTable :: Symbol -> Symbol -> [FileName] -> IO (Table, [Symbol], Int)
getTable modPrefix folderName = 
    foldM (buildTable modPrefix folderName) (primitiveTable, [], 0)

fromFiles :: [FileName] -> Symbol -> Symbol -> IO ()
fromFiles files modPrefix folderName = do
  (tbl, moduleNames, numModules) <- getTable modPrefix folderName files
  writeInsertFunctionCode modPrefix folderName tbl moduleNames

  h <- openFile (T.unpack $ folderName <> "/Bootstrap.hs") WriteMode  
  hPutModuleLn h (modPrefix <> ".Bootstrap") (modPrefix <> ".FunctionTable" : moduleNames)
  body <- runQ $ doE (noBindS (appsE [funcExpT "functions"]) :
                      map (\count -> noBindS (appsE [funcExpT (T.pack ("expr" ++ show count))]))
                              [0..numModules-1])
          
  let decl = FunD (mkName "bootstrap") [Clause [] (NormalB body) []]
  T.hPutStrLn h (myPprint decl)

writeShenSource = fromFiles klFiles "Backend" "Shentong/Backend"
