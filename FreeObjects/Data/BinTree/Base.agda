{-# OPTIONS --cubical --no-import-sorts  --safe #-}

module FreeObjects.Data.BinTree.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data BinTree (A : Type ℓ) : Type ℓ where
  leaf   : A → BinTree A
  branch : BinTree A → BinTree A → BinTree A
