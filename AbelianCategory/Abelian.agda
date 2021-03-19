{-# OPTIONS --cubical #-}

module ThesisWork.AbelianCategory.Abelian where

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

record Abelian {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
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

--******************************************* Help Abelian *******************************************

helpAbelianMonicsAreKernels : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (hasZero : hasZeroObject C) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
helpAbelianMonicsAreKernels C hasZero = {A B S : Precategory.ob (UnivalentCategory.cat C)} → (k : Precategory.hom (UnivalentCategory.cat C) S A) →
                                        isMonic C k → ∥ Σ (Precategory.hom (UnivalentCategory.cat C) A B) (λ f → isKernel C hasZero f k) ∥

helpAbelianEpicsAreCoKernels : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (hasZero : hasZeroObject C) →
                                Type (ℓ-suc (ℓ-max ℓ ℓ'))
helpAbelianEpicsAreCoKernels C hasZero = {A B S : Precategory.ob (UnivalentCategory.cat C)} → (k : Precategory.hom (UnivalentCategory.cat C) B S) →
                                          isEpic C k → ∥ Σ (Precategory.hom (UnivalentCategory.cat C) A B) (λ f → isCoKernel C hasZero f k) ∥

Abelian≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {x y : Abelian C}
               → (p : Abelian.AbHasZero x ≡ Abelian.AbHasZero y)
               → (q : Abelian.AbHasProd x ≡ Abelian.AbHasProd y)
               → (w : Abelian.AbHasCoProd x ≡ Abelian.AbHasCoProd y)
               → (e : (λ i → (hasAllKernels C) (p i) )[ Abelian.AbHasKernel x ≡ Abelian.AbHasKernel y ] )
               → (r : (λ i → (hasAllCoKernels C) (p i) )[ Abelian.AbHasCoKernel x ≡ Abelian.AbHasCoKernel y ] )
               → (t : (λ i → helpAbelianMonicsAreKernels C (p i) )[ Abelian.AbMonicsAreKernels x ≡ Abelian.AbMonicsAreKernels y ] )
               → (u : (λ i → helpAbelianEpicsAreCoKernels C  (p i) )[ Abelian.AbEpicsAreCoKernels x ≡ Abelian.AbEpicsAreCoKernels y ] )
               → x ≡ y
Abelian≡ p q w e r t u = cong abeleanCat p <*> q <*> w <*> e <*> r <*> t <*> u

--******************************************* isProp *************************************************

isAbelian : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type (ℓ-suc (ℓ-max ℓ  ℓ'))
isAbelian C = Abelian C

isAbelianIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → isProp (isAbelian C)
isAbelianIsProp C p q = Abelian≡
                        (hasZeroObjectIsProp C (Abelian.AbHasZero p) (Abelian.AbHasZero q))
                        (hasAllBinaryProductsIsProp C (Abelian.AbHasProd p) (Abelian.AbHasProd q))
                        (hasAllBinaryCoProductsIsProp C (Abelian.AbHasCoProd p) (Abelian.AbHasCoProd q))
                        (isProp→PathP (λ i → hasAllKernelsIsProp C (hasZeroObjectIsProp C (Abelian.AbHasZero p)
                        (Abelian.AbHasZero q) i)) (Abelian.AbHasKernel p) (Abelian.AbHasKernel q))
                        (isProp→PathP (λ i → hasAllCoKernelsIsProp C ((hasZeroObjectIsProp C (Abelian.AbHasZero p)
                        (Abelian.AbHasZero q) i))) (Abelian.AbHasCoKernel p) (Abelian.AbHasCoKernel q))
                        (isProp→PathP (λ i → λ r s → implicitFunExt (λ {A} → implicitFunExt (λ {B} → implicitFunExt (λ {S} →
                        funExt (λ k → funExt (λ isMonicCk → propTruncIsProp (r k isMonicCk) (s k isMonicCk)))
                        ))))
                        (Abelian.AbMonicsAreKernels p)
                        (Abelian.AbMonicsAreKernels q))
                        (isProp→PathP (λ i → λ r s → implicitFunExt (λ {A} → implicitFunExt (λ {B} → implicitFunExt (λ {S} →
                        funExt (λ k → funExt (λ isEpicCk → propTruncIsProp (r k isEpicCk) (s k isEpicCk)))
                        ))))
                        (Abelian.AbEpicsAreCoKernels p)
                        (Abelian.AbEpicsAreCoKernels q))
