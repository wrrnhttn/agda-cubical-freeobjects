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
  Cover (branch S T) (branch U V) = Cover S U × Cover T V

  reflCode : (T : BinTree A) → Cover T T
  reflCode (leaf _) = refl
  reflCode (branch S T) = reflCode S , reflCode T

  encode : ∀ S T → (p : S ≡ T) → Cover S T
  encode S _ = J (λ T _ → Cover S T) (reflCode S)

  encodeRefl : ∀ T → encode T T refl ≡ reflCode T
  encodeRefl T = JRefl (λ S _ → Cover S S) (reflCode T)

  decode : ∀ S T → Cover S T → S ≡ T
  decode (leaf x) (leaf y) x≡y = cong leaf x≡y
  decode (leaf x) (branch T T₁) (lift ())
  decode (branch _ _) (leaf x) (lift ())
  decode (branch S T) (branch U V) (cSU , cTV) = cong₂ branch (decode S U cSU) (decode T V cTV)

  decodeRefl : ∀ T → decode T T (reflCode T) ≡ refl
  decodeRefl (leaf x) = refl
  decodeRefl (branch S T) = {!!}

  decodeEncode : ∀ S T →  (p : S ≡ T) → decode S T (encode S T p) ≡ p
  decodeEncode S T = J (λ T p → decode S T (encode S T p) ≡ p) (cong (decode S S) (encodeRefl S) ∙ decodeRefl S)

  isOfHLevelCover : (n : HLevel) (p : isOfHLevel (suc (suc n)) A)
    (S T : BinTree A) → isOfHLevel (suc n) (Cover S T)
  isOfHLevelCover n p (leaf x) (leaf y) = p x y
  isOfHLevelCover n p (leaf x) (branch S T) = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (branch S T) (leaf x) = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (branch S T) (branch U V) = {!isOfHLevel× ? ?!}

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
-- TODO: (9 march 2023) no, we should use isSet A, and show that BinTree A
--         is a set (as well as FreeMagma A, elsewhere).
--module _ (setBinTreeA : isSet (BinTree A)) where
module _ (setA : isSet A) where

  

  setBinTreeA : isSet (BinTree A)
  setBinTreeA = binTreeSet setA
  
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

  BinTree→FreeMagma→BinTree : ∀ (T : BinTree A) → FreeMagma→BinTree (BinTree→FreeMagma T) ≡ T
  BinTree→FreeMagma→BinTree (leaf x) = refl
  BinTree→FreeMagma→BinTree (branch S T) = cong₂ (λ x y → branch x y) (BinTree→FreeMagma→BinTree S) (BinTree→FreeMagma→BinTree T)

  FreeMagma→BinTree→FreeMagma : ∀ (M : FreeMagma A) → BinTree→FreeMagma (FreeMagma→BinTree M) ≡ M
  FreeMagma→BinTree→FreeMagma (η x) = refl
  FreeMagma→BinTree→FreeMagma (M · N) = cong₂ (λ x y → x · y) (FreeMagma→BinTree→FreeMagma M) (FreeMagma→BinTree→FreeMagma N)
  FreeMagma→BinTree→FreeMagma (trunc M N x y i j) = cong {!!} {!!}
