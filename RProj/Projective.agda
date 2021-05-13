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
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

private
  cat = UnivalentCategory.cat
  ob : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type ℓ
  ob C = Precategory.ob (cat C)
  hom : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : ob C) → Type ℓ'
  hom C A B = Precategory.hom (cat C) A B
  _,_∘_ : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B D : ob C} → (f : hom C A B) → (g : hom C B D) → hom C A D
  _,_∘_ C = Precategory.seq (cat C)

homIsSurj : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
            (f : ModuleHomomorphism R M N) → Type ℓ
homIsSurj {M = M} {N} f = (n : ⟨ N ⟩M) → ∥ (Σ ⟨ M ⟩M (λ m → ModuleHomomorphism.h f m ≡ n)) ∥

homSurj→Epic : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
               (f : ModuleHomomorphism R M N) → homIsSurj f →
               {E : Module R} → (g h : ModuleHomomorphism R N E) →
               ModuleHomoComp f g ≡ ModuleHomoComp f h  → g ≡ h
homSurj→Epic {R = R} {M} {N} f fsurj {E} g h fg=fh =
  ModuleHomo≡ (funExt (λ n →
    rec (isSetModule E _ _)
        (λ fsurj' → g' n                  ≡⟨ cong g' (sym (fm=n fsurj')) ⟩
                    g' (f' (mObj fsurj')) ≡⟨ (λ i → ModuleHomomorphism.h (fg=fh i) (mObj fsurj')) ⟩
                    h' (f' (mObj fsurj')) ≡⟨ cong h' (fm=n fsurj') ⟩
                    h' n ∎)
        (fsurj n)))
    where
      f' = ModuleHomomorphism.h f
      g' = ModuleHomomorphism.h g
      h' = ModuleHomomorphism.h h
      mObj : {n : ⟨ N ⟩M} → (Σ ⟨ M ⟩M (λ m → ModuleHomomorphism.h f m ≡ n)) → ⟨ M ⟩M
      mObj fsurj' = fst (fsurj')
      fm=n : {n : ⟨ N ⟩M} → (fsurj' : Σ ⟨ M ⟩M (λ m → ModuleHomomorphism.h f m ≡ n)) →
             ModuleHomomorphism.h f (mObj fsurj') ≡ n
      fm=n fsurj' = snd (fsurj')

isProjectiveObject : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (P : ob C) → Type (ℓ-max ℓ ℓ')
isProjectiveObject C P = {E X : ob C} → (f : hom C P X) → (e : hom C E X) → isEpic C e →
                         ∥ (Σ (hom C P E) (λ f' → (C , f' ∘ e) ≡ f)) ∥

isProjectiveModule : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (P : Module R) → Type (ℓ-suc ℓ)
isProjectiveModule R P = {E X : Module R} → (f : ModuleHomomorphism R P X) →
                         (e : ModuleHomomorphism R E X) → homIsSurj e →
                         ∥ (Σ (ModuleHomomorphism R P E) λ f' → (ModuleHomoComp f' e) ≡ f) ∥

-- --***************************************** Test ***********************************************

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
