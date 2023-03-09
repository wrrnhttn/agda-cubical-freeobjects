{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.Data.RoseTree.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.List

open import FreeObjects.Data.RoseTree.Base
open import FreeObjects.Data.BinTree.Base

open import FreeObjects.FreeMonoid.Base

-- RoseTree = BinTree

private
   variable
     ℓ : Level
     A : Type ℓ

-- i can restrict n so that it is less
nthChild : RoseTree A → ℕ → A
nthChild (leaf x) = {!!}
nthChild (forest []) = {!!}
nthChild (forest (x ∷ x₁)) = {!!}

-- can i deal with the empty forests without using Unit here?
-- (this is like using Maybe A)
knuthTransform : RoseTree A → LabeledBinTree (A ⊎ Unit)
knuthTransform (leaf x) = leaf (inl x)
knuthTransform (forest []) = leaf (inr tt)
knuthTransform (forest (leaf a ∷ [])) = branch (inl a) (leaf (inr tt)) (leaf (inr tt))
knuthTransform (forest (leaf a ∷ x ∷ xs)) = {!!}
knuthTransform (forest (forest x ∷ xs)) = {!!}
