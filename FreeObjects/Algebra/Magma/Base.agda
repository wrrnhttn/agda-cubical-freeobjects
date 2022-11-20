{-# OPTIONS --cubical --safe #-}

module FreeObjects.Algebra.Magma.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

private
  variable
    ℓ : Level

record IsMagma {M : Type ℓ} (_·_ : M → M → M) : Type ℓ where

  constructor ismagma

  field
    is-set : isSet M


record MagmaStr (M : Type ℓ) : Type ℓ where

  constructor magmastr

  field
    _·_ : M → M → M
    isMagma : IsMagma _·_

  infixr 7 _·_

  open IsMagma isMagma public

Magma : ∀ ℓ → Type (ℓ-suc ℓ)
Magma ℓ = TypeWithStr ℓ MagmaStr

Magma₀ : Type₁
Magma₀ = Magma ℓ-zero

magma : (M : Type ℓ) (_·_ : M → M → M) (h : IsMagma _·_) → Magma ℓ
magma M _·_ h = M , magmastr _·_ h

isSetMagma : (M : Magma ℓ) → isSet ⟨ M ⟩
isSetMagma M = MagmaStr.isMagma (snd M) .IsMagma.is-set
