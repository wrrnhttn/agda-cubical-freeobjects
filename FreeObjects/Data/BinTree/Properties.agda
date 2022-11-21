{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.Data.BinTree.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Prod
open import Cubical.HITs.SetTruncation

open import FreeObjects.Data.BinTree.Base
open import FreeObjects.FreeMagma

private
  variable
    ℓ : Level
    A : Type ℓ

-- module BinTreePath {ℓ} {A : Type ℓ} where

--   Cover : BinTree A → BinTree A → Type ℓ
--   Cover (leaf x) (leaf y) = x ≡ y
--   Cover (leaf _) (branch _ _) = Lift ⊥
--   Cover (branch _ _) (leaf x) = Lift ⊥
--   Cover (branch S T) (branch U V) = Cover S T × Cover U V

--   reflCode : ∀ T → Cover T T
--   reflCode (leaf _) = refl
--   reflCode (branch S T) = {!!} , {!!}

--   encode : ∀ S T → (p : S ≡ T) → Cover S T
--   encode S _ = J (λ T _ → Cover S T) (reflCode S)

--   encodeRefl : ∀ T → encode T T refl ≡ reflCode T
--   encodeRefl T = JRefl (λ S _ → Cover S S) (reflCode T)

--   decode : ∀ S T → Cover S T → S ≡ T
--   decode (leaf x) (leaf y) x≡y = cong₂ {!!} x≡y {!!}
--   decode (leaf x) (branch T T₁) (lift ())
--   decode (branch _ _) (leaf x) (lift ())
--   decode (branch S T) (branch U V) (cST , cUV) = cong₂ branch (decode S U {!!}) {!!}

--

-- isOfHLevelBinTree : (n : HLevel) → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (BinTree A)
-- isOfHLevelBinTree n ofLevel S T =
--   {!isOfHLevelRetract (suc n) ?!}

BinTree→FreeMagma : BinTree A → FreeMagma A
BinTree→FreeMagma (leaf x) = η x
BinTree→FreeMagma (branch S T) = (BinTree→FreeMagma S) · BinTree→FreeMagma T

FreeMagma→BinTree : FreeMagma A → BinTree A
FreeMagma→BinTree (η x) = leaf x
FreeMagma→BinTree (M · N) = branch (FreeMagma→BinTree M) (FreeMagma→BinTree N)
FreeMagma→BinTree (trunc M N p q i j) = isSet→SquareP (λ i j → {!!}) -- we need isSet (BinTree A)
                                                      (λ j → FreeMagma→BinTree (p j))
                                                      (λ j → FreeMagma→BinTree (q j))
                                                      refl refl i j

-- FreeMagma→BinTree : FreeMagma A → ∥ BinTree A ∥₂
-- FreeMagma→BinTree (η x) = ∣ (leaf x) ∣₂
-- --FreeMagma→BinTree (M · N) = ∣ branch (elim (λ x → {!!}) (λ x → x) (FreeMagma→BinTree M)) {!!} ∣₂
-- FreeMagma→BinTree (M · N) = ∣ branch {!!} {!!} ∣₂
-- FreeMagma→BinTree (trunc M N x y i i₁) = {!!}
