{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Compiler.Patterns where

import Control.Applicative
import Control.Monad.Writer
import Data.Data
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Typeable
import qualified Data.Text as T
import Core.Types

type Alias = T.Text

data ConsDir = HD | TL
             deriving Eq

data ConsPat a = ConsP Alias (ConsPat a) (ConsPat a) -- bound alias, decomposed.
               | ConsV Alias -- bound alias, single value.
               | ConsL a
                 deriving (Data, Eq, Foldable, Functor, Traversable, Typeable)

data KLPat a = PCons (ConsPat a) [(Alias, Symbol)]
             | PEq Alias a
             | PWildCard [(Alias, Symbol)]
               deriving (Data, Eq, Functor, Foldable, Traversable, Typeable)

eqPattern :: SExpr -> Maybe (KLPat Atom)
eqPattern (Appl [Lit (UnboundSym "="), Sym a, Lit l]) = Just (PEq a l)
eqPattern (Appl [Lit (UnboundSym "="), Lit l, Sym a]) = Just (PEq a l)
eqPattern (Appl [Lit (UnboundSym "="), Sym a, Sym s]) = Just (PWildCard [(a, s)])
eqPattern _ = Nothing

getConsDirs :: Symbol -> SExpr -> Maybe [ConsDir]
getConsDirs n e = reverse <$> getConsDirs' n e
    where
      getConsDirs' n (Sym n') 
          | n == n'   = Just []
          | otherwise = Nothing
      getConsDirs' n (Appl [Lit (UnboundSym "hd"), h]) =
          (HD :) <$> getConsDirs' n h
      getConsDirs' n (Appl [Lit (UnboundSym "tl"), t]) =
          (TL :) <$> getConsDirs' n t
      getConsDirs' _ _ = Nothing

consPatternAlias :: Symbol -> SExpr -> Maybe Symbol
consPatternAlias n e =
    (n <>) <$> T.concat <$> map toAnnotation <$> getConsDirs n e
    where toAnnotation HD = "h"
          toAnnotation TL = "t"

getAlias :: KLPat a -> Maybe Alias
getAlias (PCons p _) = getAliasFromConsPat p
getAlias (PEq a _) = Just a
getAlias _ = Nothing
             
getAliasFromConsPat :: ConsPat a -> Maybe Alias
getAliasFromConsPat (ConsV a)     = Just a
getAliasFromConsPat (ConsP a _ _) = Just a
getAliasFromConsPat _             = Nothing

splitPat (ConsV a) = pure $ ConsP a (ConsV (a <> "h")) (ConsV (a <> "t"))
splitPat p         = pure p

litPat l _ = pure $ ConsL l

symPat s p = do
  alias <- lift $ getAliasFromConsPat p
  tell [(alias, s)]
  return p

consExpandBy = consExpandBy' (lift Nothing)
  where
    consExpandBy' :: Applicative f =>
                     f (ConsPat a) -> (ConsPat a -> f (ConsPat a)) ->
                     ConsPat a -> [ConsDir] -> f (ConsPat a)
    consExpandBy' fail f p (HD : dirs)
        | ConsP a hp tp <- p = ConsP a <$> consExpandBy' fail f hp dirs
                                       <*> pure tp
        | ConsV a <- p = ConsP a <$> consExpandBy' fail f (ConsV (a <> "h")) dirs
                                 <*> pure (ConsV (a <> "t"))
        | otherwise = fail
    consExpandBy' fail f p (TL : dirs)
        | ConsP a hp tp <- p = ConsP a hp <$> consExpandBy' fail f tp dirs
        | ConsV a <- p = ConsP a (ConsV (a <> "h")) <$>
                     consExpandBy' fail f (ConsV (a <> "t")) dirs
        | otherwise = fail
    consExpandBy' _ f p [] = f p

consEq :: SExpr -> SExpr -> Symbol ->
          ConsPat Atom -> WriterT [(Alias, Symbol)] Maybe (ConsPat Atom)
consEq (Lit l) e n p = consExpandBy (litPat l) p =<< (lift $ getConsDirs n e)
consEq (Sym s) e n p = consExpandBy (symPat s) p =<< (lift $ getConsDirs n e)
consEq _ _ _ _ = lift Nothing

consPattern :: SExpr -> Maybe (KLPat Atom)
consPattern (Appl [Lit (UnboundSym "cons?"), Sym n]) =
    flip PCons [] <$> splitPat (ConsV n)
consPattern (And (Appl [Lit (UnboundSym "cons?"), Sym n]) e) =
    uncurry PCons <$> runWriterT (go e n =<< splitPat (ConsV n))
    where 
      go :: SExpr -> Symbol -> ConsPat Atom ->
            WriterT [(Alias, Symbol)] Maybe (ConsPat Atom)
      go (And (Appl [Lit (UnboundSym "="), a, c]) e) n p =
          (go e n =<< consEq a c n p) <|> (go e n =<< consEq c a n p)
      go (Appl [Lit (UnboundSym "="), a, e]) n p =
          consEq a e n p <|> consEq e a n p
      go (And (Appl [Lit (UnboundSym "cons?"), c]) e) n p =
          go e n =<< consExpandBy splitPat p =<< (lift $ getConsDirs n c)
      go (Appl [Lit (UnboundSym "cons?"), e]) n p =
          consExpandBy splitPat p =<< (lift $ getConsDirs n e)
      go _ _ _ = lift Nothing
consPattern _  = Nothing

klPattern :: SExpr -> Maybe (Alias, KLPat Atom)
klPattern e = do
  p <- consPattern e <|> eqPattern e
  (, p) <$> getAlias p
