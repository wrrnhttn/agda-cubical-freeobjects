{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.Data.RoseTree.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.List

open import FreeObjects.FreeMonoid

private
  variable
    ℓ : Level

data RoseTree (A : Type ℓ) : Type ℓ where
  leaf : A → RoseTree A
  forest : List (RoseTree A) → RoseTree A

-- rose tree with only leaves labeled
data RoseTreeL (A : Type ℓ) : Type (ℓ-suc ℓ) where
  leaf : A → RoseTreeL A
  forest : (n : ℕ) → (Fin n → RoseTreeL A) → RoseTreeL A
