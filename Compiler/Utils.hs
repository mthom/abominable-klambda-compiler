{-# LANGUAGE OverloadedStrings #-}

module Compiler.Utils where

import Data.Monoid
import Data.Text as T
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Core.Types

mkNameT = mkName . unpack 
mkHName = mkName . unpack . haskName . ("kl_" <>)

-- try to ensure this function is one-to-one.
haskName :: Symbol -> Symbol
haskName = T.concatMap subst 
    where subst '<' = "LB"
          subst '>' = "RB"
          subst '.' = "_"
          subst '-' = "_"
          subst '?' = "P"
          subst '+' = "Plus"
          subst '@' = "At"
          subst '=' = "Eq"
          subst '*' = "Mult"
          subst '!' = "Excl"
          subst '(' = "SLB"
          subst ')' = "SRB"
          subst '&' = "And"
          subst '/' = "Div"
          subst '$' = "Dollar"
          subst ';' = "Semicolon"
          subst ':' = "Colon"
          subst '{' = "CLB"
          subst '}' = "CRB"
          subst c = T.singleton c

gensym :: Quasi m => String -> m Name
gensym = runQ . qNewName
