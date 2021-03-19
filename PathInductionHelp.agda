{-# OPTIONS --cubical --no-import-sorts #-}

module ThesisWork.PathInductionHelp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path


PathInduction : {ℓ : Level} → {A : Type ℓ} → (C : (x : A) → (y : A) → x ≡ y → Type ℓ) → (x : A) →
                C x x refl → ((y : A) → (p :  x ≡ y) → C x y p)
PathInduction C x Cxx y p = J (λ y p → C x y p) Cxx p

PathInductionInv : {ℓ : Level} → {A : Type ℓ} → (C : (x : A) → (y : A) → x ≡ y → Type ℓ) → (x : A) →
                   ((y : A) → (p :  x ≡ y) → C x y p) → C x x refl
PathInductionInv C x f = f x refl

--Todo : Fixing this would look better
--PathInduction : {ℓ : Level} → {A : Type ℓ} → (C : (x : A) → (y : A) → x ≡ y → Type ℓ) → (x : A) →
--                 ((y : A) → (p :  x ≡ y) → C x y p) ≃  C x x refl
--PathInduction {A = A} C x =
--  isoToEquiv (iso (λ f → f x refl)
--             (λ Cxx y p → J (λ y p → C x y p) Cxx p)
--             (λ z → JRefl (λ y p → C x y p) z)
--             λ z → funExt (λ y → funExt (λ p → {!!})))
