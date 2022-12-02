{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.FreeMonoid.Properties where

open import FreeObjects.FreeMonoid.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.List

private
  variable
    ℓ : Level
    A : Type ℓ

module _ (setListA : isSet (List A)) where
  List→FreeMonoid : List A → FreeMonoid A
  List→FreeMonoid [] = ε
  List→FreeMonoid (x ∷ l) = List→FreeMonoid l

  FreeMonoid→List : FreeMonoid A → List A
  FreeMonoid→List (η x) = [ x ]
  FreeMonoid→List (M · N) = FreeMonoid→List M ++ FreeMonoid→List N
  FreeMonoid→List ε = []
  FreeMonoid→List (trunc M N x y i j) = isSet→SquareP (λ i j → setListA)
                                                      (λ j → FreeMonoid→List (x j))
                                                      (λ j → FreeMonoid→List (y j))
                                                      refl refl i j

  
