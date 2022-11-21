{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.FreeMagma.Properties where

open import FreeObjects.FreeMagma.Base

open import FreeObjects.Algebra.Magma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_)

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

-- operations?


-- isSet→SquareP  approach adapted from https://github.com/agda/cubical/blob/master/Cubical/HITs/GroupoidQuotients/Properties.agda
-- i have no idea what is going on... just fishing to fill the holes.
-- could be wrong. i don't know!
length : FreeMagma A → ℕ
length (η x) = 1
length (x · y) = length x + length y
length (trunc x y p q i j) = isSet→SquareP (λ i j → isSetℕ)
                                           (λ j → length (p j))
                                           (λ j → length (q j))
                                           refl refl i j

-- what do i do with the trunc!!

-- should be in examples
-- not sure about name
open import Cubical.Data.Unit

Dyck : Type
Dyck = FreeMagma Unit

example : Dyck
example = (η tt · η tt) · η tt

exampleLength : length example ≡ 3
exampleLength = refl

-- now, i want to show that the number of elements of
-- the free magma of length n is the nth catalan number

open import Cubical.Core.Primitives

Dyckₙ : ℕ → Type
Dyckₙ n = Σ Dyck λ x → length x ≡ n

-- want to show this is finite
