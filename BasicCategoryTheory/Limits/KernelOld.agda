{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.Kernel where

open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.HelpFunctions

record Kernel {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') {A B S : ob (UnivalentCategory.cat C)}
       (hasZero : CategoryWithZeroObject C) (f : hom (UnivalentCategory.cat C) A B) : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor kernelConst
  field
    ker : hom (UnivalentCategory.cat C) S A
    kerComp : seq (UnivalentCategory.cat C) ker f ≡ (ZeroArrow.f (getZeroArrow C hasZero))
    kerFactors : {D : ob (UnivalentCategory.cat C)} (h : hom (UnivalentCategory.cat C) D A) →
                 seq (UnivalentCategory.cat C) h f ≡ (ZeroArrow.f (getZeroArrow C hasZero)) →
                 Σ (hom (UnivalentCategory.cat C) D S)
                 (λ h' → seq (UnivalentCategory.cat C) h' ker ≡ h)
    kerFactorsUnique : {D : ob (UnivalentCategory.cat C)} (h : hom (UnivalentCategory.cat C) D A) →
                       (p : seq (UnivalentCategory.cat C) h f ≡ (ZeroArrow.f (getZeroArrow C hasZero))) →
                       (h'' : hom (UnivalentCategory.cat C) D S) → seq (UnivalentCategory.cat C) h'' ker ≡ h →
                       fst (kerFactors h p) ≡ h''

isKernel :  {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : ob (UnivalentCategory.cat C)} →
            hasZeroObject C → (f : hom (UnivalentCategory.cat C) A B) → (k : hom (UnivalentCategory.cat C) S A)
            → Type (ℓ-suc (ℓ-max ℓ ℓ'))
isKernel C {S = S} hasZero f k = Σ (Kernel C {S = S} hasZero f) λ ker → Kernel.ker ker ≡ k

--************************************************* Help Functions ********************************************

HelpKerComp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)}
               → (hasZero : CategoryWithZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) →
               (ker : hom (UnivalentCategory.cat C) S A) → Type ℓ'
HelpKerComp C hasZero f ker = seq (UnivalentCategory.cat C) ker f ≡ (ZeroArrow.f (getZeroArrow C hasZero))

HelpKerFactors : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)}
               → (hasZero : CategoryWithZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) →
               (ker : hom (UnivalentCategory.cat C) S A) → Type (ℓ-max ℓ ℓ')
HelpKerFactors C {A = A} {S = S} hasZero f ker =
  {D : ob (UnivalentCategory.cat C)} (h : hom (UnivalentCategory.cat C) D A) →
  seq (UnivalentCategory.cat C) h f ≡ (ZeroArrow.f (getZeroArrow C hasZero)) →
  Σ (hom (UnivalentCategory.cat C) D S)
  (λ h' → seq (UnivalentCategory.cat C) h' ker ≡ h)

HelpKerFactorsUnique : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : Precategory.ob (UnivalentCategory.cat C)}
               → (hasZero : CategoryWithZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) →
               (ker : hom (UnivalentCategory.cat C) S A) → (HelpKerFactors C hasZero f ker) → Type (ℓ-max ℓ ℓ')
HelpKerFactorsUnique C {A = A} {S = S} hasZero f ker kerFactors =
  {D : ob (UnivalentCategory.cat C)} (h : hom (UnivalentCategory.cat C) D A) →
  (p : seq (UnivalentCategory.cat C) h f ≡ (ZeroArrow.f (getZeroArrow C hasZero))) →
  (h'' : hom (UnivalentCategory.cat C) D S) → seq (UnivalentCategory.cat C) h'' ker ≡ h →
  fst (kerFactors h p) ≡ h''

Kernel≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {A B S : Precategory.ob (UnivalentCategory.cat C)}
               → {hasZero : CategoryWithZeroObject C} {f : hom (UnivalentCategory.cat C) A B} {x y : Kernel C {S = S} hasZero f}
               → (p : Kernel.ker x ≡ Kernel.ker y)
               → (q : (λ i → HelpKerComp C hasZero f (p i) )[ Kernel.kerComp x ≡ Kernel.kerComp y ] )
               → (r : (λ i → HelpKerFactors C hasZero f (p i) ) [ Kernel.kerFactors x ≡ Kernel.kerFactors y ] )
               → (s : (λ i → HelpKerFactorsUnique C hasZero f (p i) (r i) ) [ Kernel.kerFactorsUnique x ≡ Kernel.kerFactorsUnique y ] )
               → x ≡ y
Kernel≡ p q r s = cong kernelConst p <*> q <*> r <*> s

-- ********************************************************************* Help functions ****************************************************************

--TODO: Redo in smaller steps

KerEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) → (k : hom (UnivalentCategory.cat C) S A)
            → (p q : isKernel C hasZero f k) → Kernel.ker (fst p) ≡ Kernel.ker (fst q)
KerEq C hasZero f k p q = (snd p) ∙ (sym (snd q))

KerCompEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) → (k : hom (UnivalentCategory.cat C) S A)
            → (p q : isKernel C hasZero f k) → (λ i → HelpKerComp C hasZero f (KerEq C hasZero f k p q i)) [ Kernel.kerComp (fst p) ≡ Kernel.kerComp (fst q) ]
KerCompEq C hasZero f k p q = (isProp→PathP (λ i → homIsSet ((UnivalentCategory.isCat C)) (seq (UnivalentCategory.cat C) ((KerEq C hasZero f k p q) i) f) ((ZeroArrow.f (getZeroArrow C hasZero)))) (Kernel.kerComp (fst p)) (Kernel.kerComp (fst q)))

KerFactorsEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) → (k : hom (UnivalentCategory.cat C) S A)
            → (p q : isKernel C hasZero f k) → (λ i → HelpKerFactors C hasZero f (KerEq C hasZero f k p q i)) [ Kernel.kerFactors (fst p) ≡ Kernel.kerFactors (fst q) ]
KerFactorsEq C hasZero f k p q = isProp→PathP (λ i → λ r s → implicitFunExt (λ {D} → funExt (λ h → funExt (λ hf=0 →
  Σ≡ ((sym (Kernel.kerFactorsUnique {!!} h hf=0 (fst  (r h hf=0) ) (snd (r h  hf=0)))) ∙ Kernel.kerFactorsUnique {!!} h hf=0 (fst  (s h hf=0) ) (snd (s h  hf=0))) {!!}
  )))) {!!} {!!}

--******************************************************* is Prop and unique *********************************************

isKerneIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : ob (UnivalentCategory.cat C)} →
            (hasZero : hasZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) → (k : hom (UnivalentCategory.cat C) S A)
            → isProp (isKernel C hasZero f k)
isKerneIsProp C hasZero f k p q = Σ≡ (Kernel≡ (KerEq C hasZero f k p q) (KerCompEq C hasZero f k p q) {!!} {!!}) {!!} -- (isProp→PathP (λ i → homIsSet (UnivalentCategory.isCat C) {!!} {!!}) (snd p) (snd q))


-- isKerneIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B S : ob (UnivalentCategory.cat C)} →
--             (hasZero : hasZeroObject C) → (f : hom (UnivalentCategory.cat C) A B) → (k : hom (UnivalentCategory.cat C) S A)
--             → isProp (isKernel C hasZero f k)
-- isKerneIsProp C hasZero f k p q = Σ≡ (Kernel≡ ((snd p) ∙ (sym (snd q)))
--                                                (isProp→PathP (λ i → homIsSet ((UnivalentCategory.isCat C)) (seq (UnivalentCategory.cat C) (((snd p) ∙ (sym (snd q))) i) f) ((ZeroArrow.f (getZeroArrow C hasZero)))) (Kernel.kerComp (fst p)) (Kernel.kerComp (fst q)))
--                                                (isProp→PathP (λ i → λ r s → implicitFunExt (λ {D} → funExt (λ h → funExt (λ hf≡0 →
--                                                Σ≡
--                                                (Kernel.kerFactorsUnique {!!} {!!} {!!} {!!} {!!})
--                                                (isProp→PathP (λ i → {!!}) (snd (r h hf≡0)) (snd (s h hf≡0)))
-- --                                               Σ≡
-- --                                               {!!}
--                                                --(homIsSet (UnivalentCategory.isCat C) (fst (r h hf≡0)) (fst (s h hf≡0)) {!!} {!!} i)
-- --                                               {!!}
--                                                ))))
--                                                {!!} {!!})
--                                                {!!})
--                                                {!!}

-- --{D : ob (UnivalentCategory.cat C)} (h : hom (UnivalentCategory.cat C) D A) →
-- --                 seq (UnivalentCategory.cat C) h f ≡ (ZeroArrow.f (getZeroArrow C hasZero)) →
-- --                 Σ (hom (UnivalentCategory.cat C) D S)
-- --                 (λ h' → seq (UnivalentCategory.cat C) h' ker ≡ h)
