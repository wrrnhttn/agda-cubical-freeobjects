{-# OPTIONS --cubical --safe  #-}

module FreeObjects.FreeMagma.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data FreeMagma (A : Type ℓ) : Type ℓ where
  η : A → FreeMagma A
  _·_ : FreeMagma A → FreeMagma A → FreeMagma A
  trunc : isSet (FreeMagma A)
