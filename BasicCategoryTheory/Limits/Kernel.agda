{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.Kernel where

--open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.HelpFunctions
open import Cubical.HITs.PropositionalTruncation
open import ThesisWork.CompatibilityCode

kernelFactors : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
                (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (ker : Precategory.hom (UnivalentCategory.cat C) S A) →
                Type (ℓ-max ℓ  ℓ')
kernelFactors C {A = A} {S = S} hasZero f ker = {D : Precategory.ob (UnivalentCategory.cat C)} (h : Precategory.hom (UnivalentCategory.cat C) D A) →
                 Precategory.seq (UnivalentCategory.cat C) h f ≡ (ZeroArrow.f (getZeroArrow C hasZero)) →
                 Σ (Precategory.hom (UnivalentCategory.cat C) D S)
                 (λ h' → (Precategory.seq (UnivalentCategory.cat C) h' ker ≡ h))
                       

record Kernel {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') {A B S : Precategory.ob (UnivalentCategory.cat C)}
       (hasZero : CategoryWithZeroObject C) (f : Precategory.hom (UnivalentCategory.cat C) A B) : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor kernelConst
  field
    ker : Precategory.hom (UnivalentCategory.cat C) S A
    kerComp : Precategory.seq (UnivalentCategory.cat C) ker f ≡ (ZeroArrow.f (getZeroArrow C hasZero))
    kerFactors : kernelFactors C hasZero f ker
    kerFactorsUnique : isMonic C ker

isKernel :  {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
            hasZeroObject C → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) S A)
            → Type (ℓ-suc (ℓ-max ℓ ℓ'))
isKernel C {S = S} hasZero f k = Σ (Kernel C {S = S} hasZero f) λ ker → Kernel.ker ker ≡ k

record isKernel' {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') {A B S : Precategory.ob (UnivalentCategory.cat C)}
       (hasZero : CategoryWithZeroObject C)
       (f : Precategory.hom (UnivalentCategory.cat C) A B)
       (ker : Precategory.hom (UnivalentCategory.cat C) S A) : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor isKernel'Const
  field
    kerComp : Precategory.seq (UnivalentCategory.cat C) ker f ≡ (ZeroArrow.f (getZeroArrow C hasZero))
    kerFactors : kernelFactors C hasZero f ker
    kerFactorsUnique : isMonic C ker


-- --************************************************* Help Functions ********************************************

HelpKerComp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)}
               → (hasZero : CategoryWithZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) →
               (ker : Precategory.hom (UnivalentCategory.cat C) S A) → Type ℓ'
HelpKerComp C hasZero f ker = Precategory.seq (UnivalentCategory.cat C) ker f ≡ (ZeroArrow.f (getZeroArrow C hasZero))

HelpKerFactorsUnique : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A S : Precategory.ob (UnivalentCategory.cat C)}
                       (ker : Precategory.hom (UnivalentCategory.cat C) S A) → Type (ℓ-max ℓ ℓ')
HelpKerFactorsUnique C {A = A} {S = S} ker = isMonic C ker

Kernel≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {A B S : Precategory.ob (UnivalentCategory.cat C)}
               → {hasZero : CategoryWithZeroObject C} {f : Precategory.hom (UnivalentCategory.cat C) A B} {x y : Kernel C {S = S} hasZero f}
               → (p : Kernel.ker x ≡ Kernel.ker y)
               → (q : (λ i → HelpKerComp C hasZero f (p i) )[ Kernel.kerComp x ≡ Kernel.kerComp y ] )
               → (r : (λ i → kernelFactors C hasZero f (p i) ) [ Kernel.kerFactors x ≡ Kernel.kerFactors y ] )
               → (s : (λ i → HelpKerFactorsUnique C (p i)) [ Kernel.kerFactorsUnique x ≡ Kernel.kerFactorsUnique y ] )
               → x ≡ y
Kernel≡ p q r s = cong kernelConst p <*> q <*> r <*> s

-- -- ********************************************************************* Help functions ****************************************************************

KerEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) S A)
            → (p q : isKernel C hasZero f k) → Kernel.ker (fst p) ≡ Kernel.ker (fst q)
KerEq C hasZero f k p q = (snd p) ∙ (sym (snd q))

KerCompEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) S A)
            → (p q : isKernel C hasZero f k) → (λ i → HelpKerComp C hasZero f (KerEq C hasZero f k p q i)) [ Kernel.kerComp (fst p) ≡ Kernel.kerComp (fst q) ]
KerCompEq C hasZero f k p q = (isProp→PathP (λ i → homIsSet ((UnivalentCategory.isCat C)) (Precategory.seq (UnivalentCategory.cat C) ((KerEq C hasZero f k p q) i) f) ((ZeroArrow.f (getZeroArrow C hasZero)))) (Kernel.kerComp (fst p)) (Kernel.kerComp (fst q)))

KerFactorsEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) S A)
            → (p q : isKernel C hasZero f k) → (λ i → HelpKerFactorsUnique C (KerEq C hasZero f k p q i)) [ Kernel.kerFactorsUnique (fst p) ≡
                                                 Kernel.kerFactorsUnique (fst q) ]
            → (λ i → kernelFactors C hasZero f (KerEq C hasZero f k p q i)) [ Kernel.kerFactors (fst p) ≡ Kernel.kerFactors (fst q) ]
KerFactorsEq C {A} {B} {S} hasZero f k p q uniFact = isProp→PathP (λ i → λ r s → implicitFunExt (λ {D} → funExt (λ h → funExt (λ hf=0 →
                                             Σ≡ (uniFact i D (fst (r h hf=0)) (fst (s h hf=0)) ((snd (r h hf=0)) ∙ (sym (snd (s h hf=0)))))
                                             (isProp→PathP (λ j → homIsSet (UnivalentCategory.isCat C)
                                             (Precategory.seq (UnivalentCategory.cat C) (uniFact i D (fst (r h hf=0)) (fst (s h hf=0))
                                             (snd (r h hf=0) ∙ sym (snd (s h hf=0))) j) (KerEq C hasZero f k p q i)) h)
                                             (snd (r h hf=0))
                                             (snd (s h hf=0)))))))
                                             (Kernel.kerFactors (fst p))
                                             (Kernel.kerFactors (fst q))

-- --******************************************************* is Prop and unique *********************************************

isKerneIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) S A)
            → isProp (isKernel C hasZero f k)
isKerneIsProp C hasZero f k p q = Σ≡
                                  (Kernel≡
                                  (KerEq C hasZero f k p q)
                                  (KerCompEq C hasZero f k p q)
                                  (KerFactorsEq C hasZero f k p q
                                  (isProp→PathP (λ i → isPropIsMonic C ((KerEq C hasZero f k p q) i)) (Kernel.kerFactorsUnique (fst p)) (Kernel.kerFactorsUnique (fst q))))
                                  (isProp→PathP (λ i → isPropIsMonic C ((KerEq C hasZero f k p q) i)) (Kernel.kerFactorsUnique (fst p)) (Kernel.kerFactorsUnique (fst q))))
                                  (isProp→PathP (λ i → homIsSet (UnivalentCategory.isCat C) ((KerEq C hasZero f k p q) i) k) (snd p) (snd q)) 

--********************************************************** has kernel *****************************************************

hasKernel : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} →
            hasZeroObject C → (f : Precategory.hom (UnivalentCategory.cat C) A B) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasKernel C hasZero f = ∥ Σ (Precategory.ob (UnivalentCategory.cat C)) (λ S → Kernel C {S = S} hasZero f) ∥
--{S : Precategory.ob (UnivalentCategory.cat C)} → Kernel C {S = S} hasZero f

hasKernelIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → isProp (hasKernel C hasZero f)
hasKernelIsProp C hasZero f = propTruncIsProp

hasAllKernels : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → hasZeroObject C → Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasAllKernels C hasZero = {A B : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A B) → hasKernel C hasZero f

hasAllKernelsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (hasZero : hasZeroObject C) → isProp (hasAllKernels C hasZero)
hasAllKernelsIsProp C hasZero p q = implicitFunExt (λ {A} → implicitFunExt (λ {B} → funExt (λ f →
                                    hasKernelIsProp C hasZero f (p f) (q f))))
