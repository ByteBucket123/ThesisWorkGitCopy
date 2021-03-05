{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.ElementaryArrowProperties where

--open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.CompatibilityCode

---****************************************** Monic Arrows *******************************

isMonic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A B ) → Type (ℓ-max ℓ ℓ')
isMonic {ℓ} {ℓ'} C {A = A} {B = B} f = (D : Precategory.ob (UnivalentCategory.cat C)) → (g h : Precategory.hom (UnivalentCategory.cat C) D A) → Precategory.seq (UnivalentCategory.cat C) g f ≡ Precategory.seq (UnivalentCategory.cat C) h f → g ≡ h

isPropIsMonic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A B ) → isProp (isMonic C f)
isPropIsMonic C {A = A} {B = B} f p q = funExt λ D → funExt (λ g → funExt (λ h → funExt (λ gEqH → homIsSet (UnivalentCategory.isCat C) g h (p D g h gEqH) (q D g h gEqH))))

---****************************************** Epic Arrows *******************************

isEpic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A D : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) D A ) → Type (ℓ-max ℓ ℓ')
isEpic {ℓ} {ℓ'} C {A = A} {D = D} f = (B : Precategory.ob (UnivalentCategory.cat C)) → (g h : Precategory.hom (UnivalentCategory.cat C) A B) → Precategory.seq (UnivalentCategory.cat C) f g ≡ Precategory.seq (UnivalentCategory.cat C) f h → g ≡ h

isPropIsEpic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {B D : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) B D ) → isProp (isEpic C f)
isPropIsEpic C f p q = funExt λ D → funExt (λ g → funExt (λ h → funExt (λ gEqH → homIsSet (UnivalentCategory.isCat C) g h (p D g h gEqH) (q D g h gEqH))))

---****************************************** Epic Arrows *******************************

isUniqueArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A B ) → Type ℓ'
isUniqueArrow C {A = A} {B = B} f = (g : Precategory.hom (UnivalentCategory.cat C) A B) → f ≡ g

isUniqueArrowToHomsetContr : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A B ) → isUniqueArrow C f → isContr (Precategory.hom (UnivalentCategory.cat C) A B)
isUniqueArrowToHomsetContr C f ifUniquef = f , ifUniquef

isUniqueArrowIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A B ) → isProp (isUniqueArrow C f)
isUniqueArrowIsProp C f p q = funExt (λ g → homIsSet ((UnivalentCategory.isCat C)) f g (p g) (q g))
