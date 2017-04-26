{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module Compiler.CodeGenerator where

import Interpreter.AST
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad
import Debug.Trace
import Data.Attoparsec.Text
import Data.Data
import Data.Generics.Uniplate.Operations
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Traversable hiding (mapM, mapM')
import qualified Data.Text as T hiding (foldl')
import Compiler.IR
import Language.Haskell.TH as TH
import Language.Haskell.TH.Ppr
import qualified Language.Haskell.TH.Syntax as TH
import Compiler.Parser
import Compiler.Patterns
import Compiler.Utils
import Core.Types

alternatives :: Atom -> [LAtom]
alternatives (UnboundSym "true")  = [ LLit (UnboundSym "true"), LLit (B True)]
alternatives (UnboundSym "false") = [ LLit (UnboundSym "false"), LLit (B False)]
alternatives (B True)  = [ LLit (UnboundSym "true"), LLit (B True)]
alternatives (B False) = [ LLit (UnboundSym "false"), LLit (B False)]
alternatives (UnboundSym n) = [ LLit (UnboundSym n)
                              , LBoundF n (mkHName n) 0
                              , LBoundF n (mkHName n) 1] -- capture functions of all arities.
alternatives (N (KI i)) = [LLit (N (KI i))] -- , LLit (N (KD (realToFrac i)))]
alternatives (N (KD d)) = LLit (N (KD d)) : [] -- alt
    where alt | d == fromInteger (round d) = [LLit (N (KI (round d)))]
              | otherwise                  = []
alternatives a = [LLit a]

instance TH.Lift Atom where
    lift Nil = [| Atom Nil |]
    lift (UnboundSym sym) = [| Atom (UnboundSym $(stringE (T.unpack sym))) |]
    lift (B True) =
        appE (funcExpT "Atom") (appE (funcExpT "B") (funcExpT "True"))
    lift (B False) =
        appE (funcExpT "Atom") (appE (funcExpT "B") (funcExpT "False"))
    lift (N (KD d)) = [| Atom (N (KD $(litE (rationalL $ toRational d)))) |]
    lift (N (KI i)) = [| Atom (N (KI $(litE (integerL i)))) |]
    lift (Str t) = [| Atom (Str $(stringE (show t))) |]

instance TH.Lift LAtom where
    lift (LLit l) = TH.lift l
    lift (LNam n) = varE n
    lift (LBoundF _ hn _) = varE hn

funcExp :: Name -> Q Exp
funcExp = varE

funcExpT :: T.Text -> Q Exp
funcExpT = varE . mkName . T.unpack

partialApp = funcExpT "PartialApp"

context = funcExpT "Context"

funcBody :: (MonadIO m, TH.Quasi m) => CExpr -> SourceContext m Exp
funcBody e = do
  les <- evaluationOrder e  
  lift (runQ (doE (stmts les)))

bindLet var exp = letS [valD (bangP (varP var)) (normalB (expr exp)) []]
bindArr var exp = bindS (bangP (varP var)) (expr exp)

returnExp e = noBindS $ appE (funcExpT "return") (expr e)

varFromT = mkName . T.unpack

wrapOrLift :: LAtom -> ExpQ
wrapOrLift (LBoundF n hn 0) =
    appE (funcExpT "ApplC")
         (appE (appE (funcExpT "PL") (stringE (T.unpack n)))
               (varE hn))
wrapOrLift (LBoundF n hn ar) =
    appE (funcExpT "ApplC")
         (appE (appE (funcExpT "wrapNamed") (stringE (T.unpack n))) (varE hn))
wrapOrLift a = TH.lift a

appFold :: ExpQ -> [LAtom] -> ExpQ
appFold coreApp args = foldr seqFold coreApp args
    where seqFold (LNam n) acc = infixE (Just (varE n))
                                        (funcExpT "pseq")
                                        (Just acc)
          seqFold _ acc = acc

litToPat :: LAtom -> PatQ
litToPat (LLit (UnboundSym s)) =
    conP (mkName "Atom") [conP (mkName "UnboundSym")
                               [litP (stringL (T.unpack s))]]
litToPat (LLit (Str s)) =
    conP (mkName "Atom") [conP (mkName "Str") [litP (stringL (T.unpack s))]]
litToPat (LLit (B b))  =
    conP (mkName "Atom") [conP (mkName "B") [conP (mkName (show b)) []]]
litToPat (LLit (N (KI i))) =
    conP (mkName "Atom") [conP (mkName "N")
                               [conP (mkName "KI") [litP (integerL i)]]]
litToPat (LLit (N (KD d))) = 
    conP (mkName "Atom") [conP (mkName "N")
                               [conP (mkName "KD")
                                     [viewP (funcExpT "toRational") $
                                            litP (rationalL $ toRational d)]]]
litToPat (LLit Nil) = conP (mkName "Atom") [conP (mkName "Nil") []]
litToPat (LNam _)   = wildP
litToPat (LBoundF n _ 0) = conP (mkName "ApplC")
                                [conP (mkName "PL")
                                      [ litP (stringL (T.unpack n))
                                      , wildP ]]
litToPat (LBoundF n _ _) = conP (mkName "ApplC")
                                [conP (mkName "Func")
                                      [ litP (stringL (T.unpack n))
                                      , wildP ]]                                

toGuard :: [(Alias, Symbol)] -> Maybe GuardQ
toGuard [] = Nothing
toGuard gs =
    Just (normalG (foldr1 (\g1 g2 -> infixE (Just g1) (funcExpT "&&") (Just g2))
                  (map toEqCore gs)))
    where toEqCore (a, s) = appsE [funcExpT "eqCore", varE $ mkHName a, varE $ mkHName s]          

toPatGuard :: KLPat LAtom -> (PatQ, Maybe GuardQ)
toPatGuard (PWildCard gs) = (wildP, toGuard gs)
toPatGuard (PEq a l)      = (asP (mkHName a) (litToPat l) , toGuard [])
toPatGuard (PCons p gs)   = (toConsPat p, toGuard gs)
    where toConsPat (ConsP a p1 p2) =
              bangP (asP (mkHName a) (conP (mkName "Cons")
                                     [toConsPat p1, toConsPat p2]))
          toConsPat (ConsV a) = bangP (varP (mkHName a))
          toConsPat (ConsL l) = litToPat l

toMatch :: ExpQ -> (PatQ, Maybe GuardQ) -> MatchQ
toMatch e (p, Just g)  = TH.match p (guardedB [(,) <$> g <*> e]) []
toMatch e (p, Nothing) = TH.match p (normalB e) []

casesT :: Name -> [(KLPat Atom, [LExpr])] -> ExpQ
casesT a ms = do
  (matches, letClauses) <- runWriterT $ concat <$> mapM buildExpression ms
  return $ LetE (map (\(n, as, e) -> funcDecl n as e) letClauses)
                (CaseE (VarE a) matches) 
    where 
      funcCall :: Name -> [Alias] -> ExpQ
      funcCall fn as = appsE (varE fn : map (varE . mkHName) as)

      funcDecl :: Name -> [Alias] -> Exp -> Dec
      funcDecl fn as e = FunD fn [Clause (map (VarP . mkHName) as)
                                         (NormalB e) []]

      getAllAliases :: KLPat Atom -> [Alias]
      getAllAliases (PCons p _) =
          catMaybes [getAliasFromConsPat p' | p' <- universe p]
      getAllAliases _ = []

      buildExpression :: (KLPat Atom, [LExpr]) -> WriterT [(Name, [Alias], Exp)] Q [Match]
      buildExpression (p, es) = do
            let altPats = map toPatGuard (traverse alternatives p)
                aliases = getAllAliases p

            eName <- lift $ gensym "pat_cond"
            exprs <- lift $ doE $ stmts es
            tell [(eName, aliases, exprs)]

            lift $ mapM (toMatch (funcCall eName aliases)) altPats -- was: varE eName

expr :: LExpr -> Q Exp
expr (EIf (LLit (B True)) !q _) = doE (stmts q)
expr (ECase !a !qs) = casesT a qs
expr (EApplP _ name args) = appFold coreApp args
    where coreApp = foldl' AppE <$> varE name <*> mapM wrapOrLift args
expr (EApplF name args) = appFold coreApp args
    where coreApp = foldl' AppE <$> varE name <*> mapM wrapOrLift args
expr (EApplAL name args) = appFold coreApp args
    where coreApp = appE (appE (funcExpT "applyWrapper") (varE name))
                         (listE $ map wrapOrLift args)
expr (EAtom a) = TH.lift a
expr (EFreeze es) = appE (funcExpT "ApplC")
                    (appE (appE (funcExpT "PL") (stringE "thunk"))
                          (doE (stmts es)))
expr (ELambda s es) =
    appE (funcExpT "ApplC") (appE (appE (funcExpT "Func") (stringE "lambda"))
                                  lambdaExpr)
    where
      lambdaExpr 
          | [el@(ELambda _ _)] <- es =
                                  appE partialApp
                                       (lamE [bangP (varP s)] (expr el))
          | otherwise = appE context (lamE [bangP (varP s)] (doE (stmts es)))
expr (EIf a tc fc) = 
    caseE (TH.lift a) [TH.match (litToPat (LLit (B True))) (normalB (doE (stmts tc))) [],
                       TH.match (litToPat (LLit (B False))) (normalB (doE (stmts fc))) [],
                       TH.match wildP (normalB (appE (funcExpT "throwError")
                                               (stringE "if: expected boolean"))) []]
expr EEmptyList = appE (funcExpT "Atom") (varE (mkName "Nil"))
expr (ETrapError test handler)
    | [ELambda e hcode] <- handler =                           
                           infixE (Just (doE (stmts test))) (funcExpT "catchError")
                                  (Just (lamE [bangP (varP e)] (doE (stmts hcode))))
    | otherwise = error "trap-error: type violation."
expr (EBind _ _) = error "expr: this shouldn't happen."

stmt :: LExpr -> Q Stmt
stmt (EBind var exp) 
    | ECase _ _   <- exp = bindArr var exp
    | EApplF _ _  <- exp = bindArr var exp
    | EApplAL _ _ <- exp = bindArr var exp
    | EIf _ _ _   <- exp = bindArr var exp
    | ETrapError _ _ <- exp = bindArr var exp
    | EApplP 0 _ _ <- exp =
        letS [valD (bangP (varP var)) (normalB (appE (funcExpT "ApplC")
                                             (appE (appE (funcExpT "PL")
                                                   (stringE "thunk"))
                                              (expr exp)))) []]
    | EApplP _ name _ <- exp =
        letS [valD (bangP (varP var)) (normalB (appE (funcExpT "ApplC") 
                                                         (appE (appE (funcExpT "wrapNamed")
                                                                (stringE (show name)))
                                                         (expr exp)))) []]
    | otherwise = bindLet var exp
stmt e@(ELambda _ _) = returnExp e
stmt e@(EAtom (LBoundF n hn _)) =
    noBindS $ appE (funcExpT "return")
                   (appE (funcExpT "ApplC")
                         (appE (appE (funcExpT "wrapNamed") (stringE (T.unpack n)))
                               (expr e)))
stmt e@(EAtom _) = returnExp e
stmt e@(EApplP 0 _ _) =
    noBindS $ appE (funcExpT "return")
                   (appE (funcExpT "ApplC") (appE (appE (funcExpT "PL")
                                                        (stringE "thunk"))
                                                  (expr e)))
stmt e@(EApplP _ name _) =
    noBindS $ appE (funcExpT "return") (appE (funcExpT "ApplC") 
                                                 (appE (appE (funcExpT "wrapNamed")
                                                                 (stringE (show name)))
                                                  (expr e)))
stmt e@(EEmptyList) = returnExp e
stmt e = do
  !e <- expr e
  return $ NoBindS e

stmts :: [LExpr] -> [Q Stmt]
stmts = map stmt
