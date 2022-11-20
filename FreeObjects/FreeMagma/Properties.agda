{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.FreeMagma.Properties where

open import FreeObjects.FreeMagma.Base

open import FreeObjects.Algebra.Magma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.BiInvertible

private
  variable
    ℓ : Level
    A : Type ℓ

freeMagmaIsSet : isSet (FreeMagma A)
freeMagmaIsSet = trunc

freeMagmaIsMagma : IsMagma {M = FreeMagma A} _·_
freeMagmaIsMagma = ismagma trunc

freeMagmaMagmaStr : MagmaStr (FreeMagma A)
freeMagmaMagmaStr = magmastr _·_ freeMagmaIsMagma

freeMagmaMagma : Type ℓ → Magma ℓ
freeMagmaMagma A = FreeMagma A , freeMagmaMagmaStr
