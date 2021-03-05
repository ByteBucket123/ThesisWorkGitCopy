{-# OPTIONS --cubical #-}

module ThesisWork.ElementWithProperties where

open import Cubical.Foundations.Prelude
--open import Cubical.Categories.Category
open import Cubical.Core.Glue
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import Cubical.Foundations.Equiv
open import ThesisWork.HelpFunctions
open import ThesisWork.CompatibilityCode

record ElemWithProp {ℓ ℓ' : Level} (A : Type ℓ) (S : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor elemprop
  field
    elem : A
    elemSet : isSet A
    prop : S elem
    propIsProp : (a : A) → isProp (S a)

--****************************************** ElemWithProp Equiv ********************************

ElemWithProp≡ : {ℓ ℓ' : Level} → {A : Type ℓ} → {S : A → Type ℓ'} → {x y : ElemWithProp A S}
                → (p : ElemWithProp.elem x ≡ ElemWithProp.elem y)
                → (ElemWithProp.elemSet x ≡ ElemWithProp.elemSet y )
                → (λ i → S (p i)) [ ElemWithProp.prop x ≡ ElemWithProp.prop y ]
                → (ElemWithProp.propIsProp x ≡ ElemWithProp.propIsProp y )
                → (x ≡ y)
ElemWithProp≡ p q r s = cong elemprop p <*> q <*> r <*> s

--ElemWithPropSet : {ℓ ℓ' : Level} → {A : Type ℓ} → {S : A → Type ℓ'} → {x y : ElemWithProp A S} →
--                → (p q : x ≡ y)
--                → (isSet A)
--                → (isSet  )
--                → (λ i → S (p i)) [ ElemWithProp.prop x ≡ ElemWithProp.prop y ]
--                → (ElemWithProp.propIsProp x ≡ ElemWithProp.propIsProp y )
--                → (x ≡ y)

ElemWithProp→isSet : {ℓ ℓ' : Level} → {A : Type ℓ} → {S : A → Type ℓ'} → isSet (ElemWithProp A S)
ElemWithProp→isSet x y p q i = {!!}
