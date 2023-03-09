{-# OPTIONS --cubical --no-import-sorts  --safe #-}

module FreeObjects.Data.BinTree.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data BinTree (A : Type ℓ) : Type ℓ where
  leaf   : A → BinTree A
  branch : BinTree A → BinTree A → BinTree A

-- if instead we take 2 type parameters, we get something like a magma but with multiple operations:
-- `branch : S → LabeledBinTree S A → LabeledBinTree S A → LabeledBinTree S A`
-- the leaves are the obects of the magma, and the branches labeled by s : S are the
-- s-operations.
data LabeledBinTree (A : Type ℓ) : Type ℓ where
  leaf : A → LabeledBinTree A
  branch : A → LabeledBinTree A → LabeledBinTree A → LabeledBinTree A
