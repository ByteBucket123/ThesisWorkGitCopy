{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.IsomorphismHelp where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.CompatibilityCode
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties

private
  ob : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type ℓ
  ob C = Precategory.ob (UnivalentCategory.cat C)
  hom : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : ob C) → Type ℓ'
  hom C = Precategory.hom (UnivalentCategory.cat C)
  CatAsso : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B D E : ob C} → (f : hom C A B) → (g : hom C B D) → (h : hom C D E) →
            Precategory.seq (UnivalentCategory.cat C) (Precategory.seq (UnivalentCategory.cat C) f g) h ≡
            Precategory.seq (UnivalentCategory.cat C) f (Precategory.seq (UnivalentCategory.cat C) g h)
  CatAsso C = Precategory.seq-α (UnivalentCategory.cat C)

PostCompIsEpicToEpic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A S B : ob C} → (f : hom C A B) → isEpic C f →
                       (g : hom C S B) → (i : hom C A S) → (Precategory.seq (UnivalentCategory.cat C) i g ≡ f) → isEpic C g
PostCompIsEpicToEpic C f fEpic g i ig=f E h k gh=gk = fEpic E h k
  ((f ∘ h)      ≡⟨ cong (λ x → x ∘ h) (sym ig=f) ⟩
  ((i ∘ g) ∘ h) ≡⟨ CatAsso C i g h ⟩
  (i ∘ (g ∘ h)) ≡⟨ cong (λ x → i ∘ x) gh=gk ⟩
  (i ∘ (g ∘ k)) ≡⟨ sym (CatAsso C i g k) ⟩
  ((i ∘ g) ∘ k) ≡⟨ cong (λ x → x ∘ k) ig=f ⟩
  (f ∘ k) ∎)
    where
      _∘_ = Precategory.seq (UnivalentCategory.cat C)

