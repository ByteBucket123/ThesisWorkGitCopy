{-# OPTIONS --cubical #-}

module ThesisWork.AbeleanCategory.Abelean where

--open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.Kernel
open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
open import ThesisWork.HelpFunctions
open import Cubical.HITs.PropositionalTruncation
open import ThesisWork.CompatibilityCode

record Abelean {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor abeleanCat
  field
    AbHasZero : hasZeroObject C
    AbHasProd : hasAllBinaryProducts C
    AbHasCoProd : hasAllBinaryCoProducts C
    AbHasKernel : hasAllKernels C AbHasZero
    AbHasCoKernel : hasAllCoKernels C AbHasZero
    AbMonicsAreKernels : {A B S : Precategory.ob (UnivalentCategory.cat C)} → (k : Precategory.hom (UnivalentCategory.cat C) S A) → isMonic C k →
                         ∥ Σ (Precategory.hom (UnivalentCategory.cat C) A B) (λ f → isKernel C AbHasZero f k) ∥
    AbEpicsAreCoKernels : {A B S : Precategory.ob (UnivalentCategory.cat C)} → (k : Precategory.hom (UnivalentCategory.cat C) B S) → isEpic C k →
                          ∥ Σ (Precategory.hom (UnivalentCategory.cat C) A B) (λ f → isCoKernel C AbHasZero f k) ∥

--******************************************* Help Abelean *******************************************

helpAbeleanMonicsAreKernels : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (hasZero : hasZeroObject C) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
helpAbeleanMonicsAreKernels C hasZero = {A B S : Precategory.ob (UnivalentCategory.cat C)} → (k : Precategory.hom (UnivalentCategory.cat C) S A) →
                                        isMonic C k → ∥ Σ (Precategory.hom (UnivalentCategory.cat C) A B) (λ f → isKernel C hasZero f k) ∥

helpAbeleanEpicsAreCoKernels : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (hasZero : hasZeroObject C) →
                                Type (ℓ-suc (ℓ-max ℓ ℓ'))
helpAbeleanEpicsAreCoKernels C hasZero = {A B S : Precategory.ob (UnivalentCategory.cat C)} → (k : Precategory.hom (UnivalentCategory.cat C) B S) →
                                          isEpic C k → ∥ Σ (Precategory.hom (UnivalentCategory.cat C) A B) (λ f → isCoKernel C hasZero f k) ∥

Abelean≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {x y : Abelean C}
               → (p : Abelean.AbHasZero x ≡ Abelean.AbHasZero y)
               → (q : Abelean.AbHasProd x ≡ Abelean.AbHasProd y)
               → (w : Abelean.AbHasCoProd x ≡ Abelean.AbHasCoProd y)
               → (e : (λ i → (hasAllKernels C) (p i) )[ Abelean.AbHasKernel x ≡ Abelean.AbHasKernel y ] )
               → (r : (λ i → (hasAllCoKernels C) (p i) )[ Abelean.AbHasCoKernel x ≡ Abelean.AbHasCoKernel y ] )
               → (t : (λ i → helpAbeleanMonicsAreKernels C (p i) )[ Abelean.AbMonicsAreKernels x ≡ Abelean.AbMonicsAreKernels y ] )
               → (u : (λ i → helpAbeleanEpicsAreCoKernels C  (p i) )[ Abelean.AbEpicsAreCoKernels x ≡ Abelean.AbEpicsAreCoKernels y ] )
               → x ≡ y
Abelean≡ p q w e r t u = cong abeleanCat p <*> q <*> w <*> e <*> r <*> t <*> u

--******************************************* isProp *************************************************

isAbelean : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type (ℓ-suc (ℓ-max ℓ  ℓ'))
isAbelean C = Abelean C

isAbeleanIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → isProp (isAbelean C)
isAbeleanIsProp C p q = Abelean≡
                        (hasZeroObjectIsProp C (Abelean.AbHasZero p) (Abelean.AbHasZero q))
                        (hasAllBinaryProductsIsProp C (Abelean.AbHasProd p) (Abelean.AbHasProd q))
                        (hasAllBinaryCoProductsIsProp C (Abelean.AbHasCoProd p) (Abelean.AbHasCoProd q))
                        (isProp→PathP (λ i → hasAllKernelsIsProp C (hasZeroObjectIsProp C (Abelean.AbHasZero p)
                        (Abelean.AbHasZero q) i)) (Abelean.AbHasKernel p) (Abelean.AbHasKernel q))
                        (isProp→PathP (λ i → hasAllCoKernelsIsProp C ((hasZeroObjectIsProp C (Abelean.AbHasZero p)
                        (Abelean.AbHasZero q) i))) (Abelean.AbHasCoKernel p) (Abelean.AbHasCoKernel q))
                        (isProp→PathP (λ i → λ r s → implicitFunExt (λ {A} → implicitFunExt (λ {B} → implicitFunExt (λ {S} →
                        funExt (λ k → funExt (λ isMonicCk → propTruncIsProp (r k isMonicCk) (s k isMonicCk)))
                        ))))
                        (Abelean.AbMonicsAreKernels p)
                        (Abelean.AbMonicsAreKernels q))
                        (isProp→PathP (λ i → λ r s → implicitFunExt (λ {A} → implicitFunExt (λ {B} → implicitFunExt (λ {S} →
                        funExt (λ k → funExt (λ isEpicCk → propTruncIsProp (r k isEpicCk) (s k isEpicCk)))
                        ))))
                        (Abelean.AbEpicsAreCoKernels p)
                        (Abelean.AbEpicsAreCoKernels q))
