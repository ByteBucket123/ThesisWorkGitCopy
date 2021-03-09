{-# OPTIONS --cubical #-}

module ThesisWork.propositionalLogic.BasicPropositionalLogic where

open import Cubical.Data.Empty.Base
open import Cubical.Data.Empty.Properties
open import Cubical.Foundations.Prelude
open import ThesisWork.propositionalLogic.PropositionalLogicBase
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import ThesisWork.HelpFunctions

isProp⊤ : isProp ⊤
isProp⊤ tt tt = refl

isContr→⊤ : {ℓ : Level} → {A : Type ℓ} → isContr A → ⊤
isContr→⊤ contr = tt


⊤→isContr : {ℓ : Level} → {A : Type ℓ} → isContr A → ⊤ → isContr A
⊤→isContr contr tt = contr

isContr≃⊤ : {ℓ : Level} → {A : Type ℓ} → isContr A → isContr A ≃ ⊤
isContr≃⊤ isContrA = isoToEquiv (iso isContr→⊤
                                    (⊤→isContr isContrA)
                                    (λ z → isProp⊤ tt z) λ z → isPropIsContr isContrA z)

isContr≃ : {ℓ : Level} → {A : Type ℓ} → isContr A → A ≃ ⊤
isContr≃ isContrA = isoToEquiv (iso (λ a → tt)
                                    (λ tt → fst isContrA)
                                    (λ z → isProp⊤ tt z)
                                     λ z → snd isContrA z)

Equiv⊤ : {ℓ : Level} → {A B : Type ℓ} → A ≃ ⊤ → B ≃ ⊤ → A ≃ B
Equiv⊤ A⊤ B⊤ = compEquiv A⊤ (invEquiv B⊤)
