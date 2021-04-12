{-# OPTIONS --cubical #-}

module ThesisWork.RProj.Projective where

open import ThesisWork.CompatibilityCode
open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.RModules.CommutativeRing
open import ThesisWork.RModules.RModule
open import ThesisWork.RModules.RModuleHomomorphism

private
  ob : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type ℓ
  ob C = Precategory.ob (UnivalentCategory.cat C)
  hom : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : ob C) → Type ℓ'
  hom C A B = Precategory.hom (UnivalentCategory.cat C) A B

homIsSurj : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
            (f : ModuleHomomorphism R M N) → Type ℓ
homIsSurj {M = M} {N} f = (n : ⟨ N ⟩M) → Σ ⟨ M ⟩M (λ m → ModuleHomomorphism.h f m ≡ n)

homSurj→Epic : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
               (f : ModuleHomomorphism R M N) → homIsSurj f →
               {E : Module R} → (g h : ModuleHomomorphism R N E) →
               ModuleHomoComp f g ≡ ModuleHomoComp f h  → g ≡ h
homSurj→Epic {R = R} {M} {N} f fsurj g h fg=fh =
  ModuleHomo≡ (funExt (λ n →
    g' n             ≡⟨ cong g' (sym (fm=n n)) ⟩
    g' (f' (mObj n)) ≡⟨ (λ i → ModuleHomomorphism.h (fg=fh i) (mObj n)) ⟩
    h' (f' (mObj n)) ≡⟨ cong h' (fm=n n) ⟩
    h' n ∎))
    where
      f' = ModuleHomomorphism.h f
      g' = ModuleHomomorphism.h g
      h' = ModuleHomomorphism.h h
      mObj : (n : ⟨ N ⟩M) → ⟨ M ⟩M
      mObj n = fst (fsurj n)
      fm=n : (n : ⟨ N ⟩M) → ModuleHomomorphism.h f (mObj n) ≡ n
      fm=n n = snd (fsurj n)

isProjectiveObject : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (P : ob C) → Type (ℓ-max ℓ ℓ')
isProjectiveObject C P = {E X : ob C} → (f : hom C P X) → (e : hom C E X) → isEpic C e →
                         isContr (hom C P E)

isProjectiveModule : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (P : Module R) → Type (ℓ-suc ℓ)
isProjectiveModule R P = {E X : Module R} → (f : ModuleHomomorphism R P X) →
                         (e : ModuleHomomorphism R E X) → homIsSurj e →
                         isContr (ModuleHomomorphism R P E)

--***************************************** Test ***********************************************

homIsInj : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
           (f : ModuleHomomorphism R M N) → Type ℓ
homIsInj {M = M} {N} f = (m m' : ⟨ M ⟩M) → (ModuleHomomorphism.h f m ≡ ModuleHomomorphism.h f m') →
                         (m ≡ m')

homInj→Monic : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
               (f : ModuleHomomorphism R M N) → homIsInj f →
               {E : Module R} → (g h : ModuleHomomorphism R E M) →
               ModuleHomoComp g f ≡ ModuleHomoComp h f  → g ≡ h
homInj→Monic f fInj g h gf=hf =
  ModuleHomo≡ (funExt (λ e → fInj (g' e) (h' e) λ i → ModuleHomomorphism.h (gf=hf i) e))
    where
      f' = ModuleHomomorphism.h f
      g' = ModuleHomomorphism.h g
      h' = ModuleHomomorphism.h h
