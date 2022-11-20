{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.FreeMonoid.Base where

open import Cubical.Foundations.Prelude

open import FreeObjects.FreeMagma

private
   variable
     ℓ : Level

data FreeMonoid (A : Type ℓ) : Type ℓ where
  η : A → FreeMonoid A
  _·_ : FreeMonoid A → FreeMonoid A → FreeMonoid A
  ε : FreeMonoid A
  trunc : isSet (FreeMonoid A)
