{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module Compiler.IR where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad
import Data.Attoparsec.Text
import Data.Data
import Data.Generics.Uniplate.Operations
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T hiding (foldl')
import Data.Traversable (traverse)
import Language.Haskell.TH as TH
import Language.Haskell.TH.Ppr
import qualified Language.Haskell.TH.Syntax as TH
import Interpreter.AST
import Compiler.Parser
import Compiler.Patterns
import Compiler.Utils
import Core.Types

data FuncDef = BackendFunc !Symbol !ParamList !SExpr
             | PrimFunc !Symbol !Symbol !Int 
             | Expr !SExpr

type Table = [(Symbol, FuncDef)]

data LAtom = LLit !Atom
           | LNam !Name
           | LBoundF !Symbol !Name !Int -- function name, arity
             deriving (Data, Eq, Show, Typeable)

data LExpr = EApplP !Int !Name ![LAtom] -- add an int parameter, for remaining arity.
           | EApplF !Name ![LAtom]
           | EApplAL !Name ![LAtom] -- symbol in AL should pattern match to Function.
           | EAtom !LAtom           
           | EBind !Name !LExpr
           | EFreeze ![LExpr]
           | ELambda !Name ![LExpr]
           | EIf !LAtom ![LExpr] ![LExpr]
           | EEmptyList
           | ETrapError ![LExpr] ![LExpr]
           | ECase !Name ![(KLPat Atom, [LExpr])] -- new to this module!
             deriving (Data, Typeable)

data LContext = LContext ![LExpr] !LExpr

newtype SourceContext m a = SourceContext { runSC :: ReaderT Table m a }
    deriving (Monad, MonadIO, Functor, Applicative, MonadReader Table, MonadTrans)

data CExpr = CLit !Atom
           | CSym !Symbol
           | CFreeze !CExpr
           | CLet !Symbol !CExpr !CExpr
           | CLambda !Symbol !CExpr
           | CIf CExpr !CExpr !CExpr
           | CAppl ![CExpr]
           | CTrapError !CExpr !CExpr
           | CEmptyList
           | CCase !Symbol ![(KLPat Atom, CExpr)]
             deriving (Data, Typeable)

rewriteCaseByPat :: Alias -> KLPat Atom -> SExpr -> (KLPat Atom, CExpr)
rewriteCaseByPat a (PCons p e) q = (PCons p e, toCExpr $ compress q)
    where aliases = catMaybes [getAliasFromConsPat a | a <- universe p]

          compress e
              | Just s <- consPatternAlias a e =
                          if s `elem` aliases then Sym s
                          else descend compress e
              | otherwise = descend compress e
rewriteCaseByPat _ p q = (p, toCExpr q)

caseFold :: Alias -> [(SExpr, SExpr)] -> [(KLPat Atom, CExpr)]
caseFold a ((c,q) : cs) =
    case klPattern c of
      Just (a', p) ->
          if a' == a then rewriteCaseByPat a p q : caseFold a cs
          else [(PWildCard [], toCExpr (Cond ((c,q) : cs)))]
      Nothing -> [(PWildCard [], CIf (toCExpr c) (toCExpr q) (toCExpr (Cond cs)))]
caseFold _ [] = []
              
toCExpr :: SExpr -> CExpr
toCExpr (And t1 t2) =
    toCExpr (If t1 (If t2 (Lit (B True)) (Lit (B False))) (Lit (B False)))
toCExpr (Or t1 t2)  =
    toCExpr (If t1 (Lit (B True)) (If t2 (Lit (B True)) (Lit (B False))))
toCExpr (If c t f)  =
    toCExpr (Cond [(c, t), (Lit (B True), f)])
toCExpr (Cond []) = CLit Nil
toCExpr (Cond cls@((c, q) : cs)) =
    case klPattern c of
      Just (a,p) -> let cases = caseFold a cls in --(nubBy uPatterns cls) in
                    CCase a cases
          where uPatterns (p1, _) (p2, _) = p1 == p2
      _ -> CIf (toCExpr c) (toCExpr q) (toCExpr (Cond cs))
toCExpr (Sym s) = CSym s
toCExpr (Lit l) = CLit l
toCExpr (Freeze se) = CFreeze (toCExpr se)
toCExpr (Let s b e) = CLet s (toCExpr b) (toCExpr e)
toCExpr (Lambda s e) = CLambda s (toCExpr e)
toCExpr (Appl es) = CAppl (map toCExpr es)
toCExpr (TrapError c h) = CTrapError (toCExpr c) (toCExpr h)

evalSC :: SourceContext m a -> Table -> m a
evalSC (SourceContext sc) = runReaderT sc

evaluationOrder :: TH.Quasi m => CExpr -> SourceContext m [LExpr]
evaluationOrder e = toLExprs <$> para wrapper e
    where wrapper e = trawl e <=< sequence

          trawl (CLit (UnboundSym name)) _ = do
              sym <- functionOrSymbol name
              case sym of
                Left _ -> lcontext [] (EAtom (LLit (UnboundSym name)))
                Right (n, hn, ar) -> lcontext [] (EAtom (LBoundF n hn ar))
          trawl (CLit l) _ = lcontext [] (llit l)           
          trawl (CSym s) _ = lcontext [] (EAtom (LNam (mkHName s)))
          trawl (CFreeze _) [LContext f1 f2] =
              lcontext [] (EFreeze (f1 ++ [f2]))
          trawl (CLet s _ _) [LContext bci bcl, LContext eci ecl] = 
              lcontext (bci ++ [EBind (mkHName s) bcl] ++ eci) ecl
          trawl (CLambda s _) [LContext e b] =
              lcontext [] (ELambda (mkHName s) (e ++ [b]))
          trawl (CIf _ _ _) [c,t,f] = eif c t f
          trawl (CAppl []) _ = lcontext [] EEmptyList
          trawl (CAppl _) ctxt = doAppl ctxt
          trawl (CCase a cqs) ctxt = do
              let clauses = zipWith (\(p, _) e -> (p, e))
                                    cqs
                                    (map toLExprs ctxt)
              lcontext [] (ECase (mkHName a) clauses)                                 
          trawl (CTrapError _ _) [c,h] = 
              lcontext [] (ETrapError (toLExprs c) (toLExprs h))

          toLAtomPat (UnboundSym n) = do
            sym <- functionOrSymbol n
            case sym of
              Left _ -> return (LLit (UnboundSym n)) -- why???? bad idea: (LNam (mkHName n))
              Right (n, hn, ar) -> return (LBoundF n hn ar)
          toLAtomPat l = return (LLit l)     

          functionOrSymbol n = do
            found <- getFuncDef n
            case found of
              Just (PrimFunc name hName ar) ->
                  return (Right (name, mkNameT hName, ar))
              Just (BackendFunc name args _) ->
                  return (Right (name, mkHName name, length args))
              _ -> return (Left n)

          eif (LContext ci cl) (LContext ti tl) (LContext fi fl)
              | EAtom cla <- cl = lcontext ci (EIf cla (ti ++ [tl]) (fi ++ [fl]))
              | otherwise = lift $ do
                   bn <- gensym "kl_if"
                   lcontext (ci ++ [EBind bn cl])
                            (EIf (LNam bn) (ti ++ [tl]) (fi ++ [fl]))

          getFuncDef name = lookup name <$> ask

          doAppl ctxt = do
            (fs, a : as) <- unzip <$> mapM bind ctxt
            let args = concatMap filterAtom fs

            case a of
              LNam n          -> lcontext args (EApplAL n as)
              LBoundF _ hn ar ->
                  if ar > length as then
                      lcontext args (EApplP (ar - length as) hn as)
                  else
                      lcontext args (EApplF hn as)
              a'@(LLit (UnboundSym n)) -> do
                  aw <- lift $ gensym "aw"
                  let applied = EBind aw (EAtom a')
                  lcontext (args ++ [applied]) (EApplAL aw as)
              _ -> error "doAppl: not a proper function in function position"
            where bind lc@(LContext _ (EAtom a)) = return (lc, a)
                  bind (LContext ai al) = lift $ do
                                  name <- gensym "appl"
                                  lcs  <- lcontext ai (EBind name al)
                                  return (lcs, LNam name)

                  filterAtom (LContext [] (EAtom _)) = []
                  filterAtom lc = toLExprs lc
                                                      
          toLExprs (LContext ls l) = ls ++ [l]

          lcontext ls l = return (LContext ls l)
          
          llit = EAtom . LLit
          lnam = EAtom . LNam . mkHName
