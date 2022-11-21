{-# OPTIONS --cubical --no-import-sorts --safe #-}

module FreeObjects.Data.BinTree.Properties where

open import Cubical.Foundations.GroupoidLaws
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

module BinTreePath {ℓ} {A : Type ℓ} where

  Cover : BinTree A → BinTree A → Type ℓ
  Cover (leaf x) (leaf y) = x ≡ y
  Cover (leaf _) (branch _ _) = Lift ⊥
  Cover (branch _ _) (leaf x) = Lift ⊥
  Cover (branch S T) (branch U V) = Cover S T × Cover U V

  reflCode : ∀ T → Cover T T
  reflCode (leaf _) = refl
  reflCode (branch S T) = {!!} , {!!}

  encode : ∀ S T → (p : S ≡ T) → Cover S T
  encode S _ = J (λ T _ → Cover S T) (reflCode S)

  encodeRefl : ∀ T → encode T T refl ≡ reflCode T
  encodeRefl T = JRefl (λ S _ → Cover S S) (reflCode T)

  decode : ∀ S T → Cover S T → S ≡ T
  decode (leaf x) (leaf y) x≡y = cong₂ {!!} x≡y {!!}
  decode (leaf x) (branch T T₁) (lift ())
  decode (branch _ _) (leaf x) (lift ())
  decode (branch S T) (branch U V) (cST , cUV) = cong₂ branch (decode S U {!!}) {!!}

  decodeRefl : ∀ T → decode T T (reflCode T) ≡ refl
  decodeRefl = {!!}

  decodeEncode : ∀ S T →  (p : S ≡ T) → decode S T (encode S T p) ≡ p
  decodeEncode S T = J (λ T p → decode S T (encode S T p) ≡ p) (cong (decode S S) (encodeRefl S) ∙ decodeRefl S)

  isOfHLevelCover : (n : HLevel) (p : isOfHLevel (suc (suc n)) A)(S T : BinTree A) → isOfHLevel (suc n) (Cover S T)
  isOfHLevelCover = {!!}

--

isOfHLevelBinTree : (n : HLevel) → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (BinTree A)
isOfHLevelBinTree n ofLevel S T =
  isOfHLevelRetract (suc n)
    (BinTreePath.encode S T)
    (BinTreePath.decode S T)
    (BinTreePath.decodeEncode S T)
    (BinTreePath.isOfHLevelCover n ofLevel S T)


binTreeSet : isSet A → isSet (BinTree A)
binTreeSet setA = isOfHLevelBinTree 0 setA


-- BinTree A and FreeMagma A are equal when BinTree A is a set
-- NOTE: maybe  better to use isSet (BinTree A) rather that isSet A?
module _ (setBinTreeA : isSet (BinTree A)) where

  BinTree→FreeMagma : BinTree A → FreeMagma A
  BinTree→FreeMagma (leaf x) = η x
  BinTree→FreeMagma (branch S T) = (BinTree→FreeMagma S) · BinTree→FreeMagma T

  -- can i make isSet A an implicit parameter?
  FreeMagma→BinTree : FreeMagma A → BinTree A
  FreeMagma→BinTree (η x) = leaf x
  FreeMagma→BinTree (M · N) = branch (FreeMagma→BinTree M) (FreeMagma→BinTree N)
  FreeMagma→BinTree (trunc M N p q i j) = isSet→SquareP (λ i j → setBinTreeA)
                                                        (λ j → FreeMagma→BinTree (p j))
                                                        (λ j → FreeMagma→BinTree (q j))
                                                        refl refl i j

-- FreeMagma→BinTree : FreeMagma A → ∥ BinTree A ∥₂
-- FreeMagma→BinTree (η x) = ∣ (leaf x) ∣₂
-- --FreeMagma→BinTree (M · N) = ∣ branch (elim (λ x → {!!}) (λ x → x) (FreeMagma→BinTree M)) {!!} ∣₂
-- FreeMagma→BinTree (M · N) = ∣ branch {!!} {!!} ∣₂
-- FreeMagma→BinTree (trunc M N x y i i₁) = {!!}
