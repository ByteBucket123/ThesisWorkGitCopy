{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.CoKernel where

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



coKernelFactors : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
                (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (ker : Precategory.hom (UnivalentCategory.cat C) B S) →
                Type (ℓ-max ℓ  ℓ')
coKernelFactors C {B = B} {S = S} hasZero f ker = {D : Precategory.ob (UnivalentCategory.cat C)} (h : Precategory.hom (UnivalentCategory.cat C) B D) →
                 Precategory.seq (UnivalentCategory.cat C) f h ≡ (ZeroArrow.f (getZeroArrow C hasZero)) →
                 Σ (Precategory.hom (UnivalentCategory.cat C) S D)
                 (λ h' → (Precategory.seq (UnivalentCategory.cat C) ker h' ≡ h))
                   
record CoKernel {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') {A B S : Precategory.ob (UnivalentCategory.cat C)}
       (hasZero : CategoryWithZeroObject C) (f : Precategory.hom (UnivalentCategory.cat C) A B) : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor coKernelConst
  field
    coKer : Precategory.hom (UnivalentCategory.cat C) B S
    coKerComp : Precategory.seq (UnivalentCategory.cat C) f coKer ≡ (ZeroArrow.f (getZeroArrow C hasZero))
    coKerFactors : coKernelFactors C hasZero f coKer
    coKerFactorsUnique : isEpic C coKer


isCoKernel :  {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
              hasZeroObject C → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) B S)
              → Type (ℓ-suc (ℓ-max ℓ ℓ'))
isCoKernel C {S = S} hasZero f k = Σ (CoKernel C {S = S} hasZero f) λ ker → CoKernel.coKer ker ≡ k

isCoKernel→CoKernel : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
                      (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) →
                      (k : Precategory.hom (UnivalentCategory.cat C) B S) → isCoKernel C hasZero f k →
                      CoKernel C hasZero f
isCoKernel→CoKernel C hasZero f k isCoK = fst isCoK

--************************************************* Help Functions ********************************************

HelpCoKerComp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)}
                 → (hasZero : CategoryWithZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) →
                 (coKer : Precategory.hom (UnivalentCategory.cat C) B S) → Type ℓ'
HelpCoKerComp C hasZero f coKer = Precategory.seq (UnivalentCategory.cat C) f coKer ≡ (ZeroArrow.f (getZeroArrow C hasZero))

HelpCoKerFactorsUnique : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {B S : Precategory.ob (UnivalentCategory.cat C)}
                         (ker : Precategory.hom (UnivalentCategory.cat C) B S) → Type (ℓ-max ℓ ℓ')
HelpCoKerFactorsUnique C coKer = isEpic C coKer

CoKernel≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {A B S : Precategory.ob (UnivalentCategory.cat C)}
                 → {hasZero : CategoryWithZeroObject C} {f : Precategory.hom (UnivalentCategory.cat C) A B} {x y : CoKernel C {S = S} hasZero f}
                 → (p : CoKernel.coKer x ≡ CoKernel.coKer y)
                 → (q : (λ i → HelpCoKerComp C hasZero f (p i) )[ CoKernel.coKerComp x ≡ CoKernel.coKerComp y ] )
                 → (r : (λ i → coKernelFactors C hasZero f (p i) ) [ CoKernel.coKerFactors x ≡ CoKernel.coKerFactors y ] )
                 → (s : (λ i → HelpCoKerFactorsUnique C (p i)) [ CoKernel.coKerFactorsUnique x ≡ CoKernel.coKerFactorsUnique y ] )
                 → x ≡ y
CoKernel≡ p q r s = cong coKernelConst p <*> q <*> r <*> s

--********************************************************************* Help functions ****************************************************************

CoKerEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
        (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) B S)
         → (p q : isCoKernel C hasZero f k) → CoKernel.coKer (fst p) ≡ CoKernel.coKer (fst q)
CoKerEq C hasZero f k p q = (snd p) ∙ (sym (snd q))

CoKerCompEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) B S)
            → (p q : isCoKernel C hasZero f k) → (λ i → HelpCoKerComp C hasZero f (CoKerEq C hasZero f k p q i)) [ CoKernel.coKerComp (fst p) ≡ CoKernel.coKerComp (fst q) ]
CoKerCompEq C hasZero f k p q = (isProp→PathP (λ i → homIsSet ((UnivalentCategory.isCat C)) (Precategory.seq (UnivalentCategory.cat C) f ((CoKerEq C hasZero f k p q) i)) ((ZeroArrow.f (getZeroArrow C hasZero)))) (CoKernel.coKerComp (fst p)) (CoKernel.coKerComp (fst q)))

CoKerFactorsEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
                 (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) B S)
                  → (p q : isCoKernel C hasZero f k) →
                  (λ i → HelpCoKerFactorsUnique C (CoKerEq C hasZero f k p q i))
                  [ CoKernel.coKerFactorsUnique (fst p) ≡ CoKernel.coKerFactorsUnique (fst q) ]
                  → (λ i → coKernelFactors C hasZero f (CoKerEq C hasZero f k p q i))
                  [ CoKernel.coKerFactors (fst p) ≡ CoKernel.coKerFactors (fst q) ]
CoKerFactorsEq C {A} {B} {S} hasZero f k p q uniFact = isProp→PathP (λ i → λ r s → implicitFunExt λ {D} → funExt (λ h → funExt (λ fh=0 →
                                                       Σ≡
                                                       (uniFact i D (fst (r h fh=0)) (fst (s h fh=0))
                                                       ((snd (r h fh=0)) ∙ (sym (snd (s h fh=0)))))
                                                       (isProp→PathP
                                                       (λ j →
                                                       homIsSet (UnivalentCategory.isCat C)
                                                       (Precategory.seq (UnivalentCategory.cat C)
                                                       ((CoKerEq C hasZero f k p q i))
                                                       (uniFact i D (fst (r h fh=0)) (fst (s h fh=0))
                                                       ((snd (r h fh=0) ∙ sym (snd (s h fh=0)))) j))
                                                       h
                                                       )
                                                       (snd (r h fh=0)) (snd (s h fh=0)))
                                                       )))
                                                       ((CoKernel.coKerFactors (fst p)))
                                                       ((CoKernel.coKerFactors (fst q)))

--******************************************************* is Prop and unique *********************************************

isCoKerneIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)} →
                (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → (k : Precategory.hom (UnivalentCategory.cat C) B S)
                 → isProp (isCoKernel C hasZero f k)
isCoKerneIsProp C hasZero f k p q = Σ≡
                                  (CoKernel≡
                                  (CoKerEq C hasZero f k p q)
                                  (CoKerCompEq C hasZero f k p q)
                                  (CoKerFactorsEq C hasZero f k p q
                                  (isProp→PathP (λ i → isPropIsEpic C ((CoKerEq C hasZero f k p q) i))
                                  (CoKernel.coKerFactorsUnique (fst p))
                                  (CoKernel.coKerFactorsUnique (fst q))
                                  ))
                                  (isProp→PathP (λ i → isPropIsEpic C ((CoKerEq C hasZero f k p q) i))
                                  (CoKernel.coKerFactorsUnique (fst p))
                                  (CoKernel.coKerFactorsUnique (fst q))
                                  ))
                                  (isProp→PathP (λ i → homIsSet (UnivalentCategory.isCat C) ((CoKerEq C hasZero f k p q) i) k)
                                  (snd p) (snd q)) 

--********************************************************** has kernel *****************************************************

hasCoKernel : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} →
            hasZeroObject C → (f : Precategory.hom (UnivalentCategory.cat C) A B) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasCoKernel C hasZero f = ∥ Σ (Precategory.ob (UnivalentCategory.cat C)) (λ S → CoKernel C {S = S} hasZero f) ∥
--{S : Precategory.ob (UnivalentCategory.cat C)} → Kernel C {S = S} hasZero f

hasCoKernelIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} →
                  (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → isProp (hasCoKernel C hasZero f)
hasCoKernelIsProp C hasZero f = propTruncIsProp

hasAllCoKernels : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → hasZeroObject C → Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasAllCoKernels C hasZero = {A B : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A B) → hasCoKernel C hasZero f

hasAllCoKernelsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (hasZero : hasZeroObject C) → isProp (hasAllCoKernels C hasZero)
hasAllCoKernelsIsProp C hasZero p q = implicitFunExt (λ {A} → implicitFunExt (λ {B} → funExt (λ f →
                                    hasCoKernelIsProp C hasZero f (p f) (q f))))
