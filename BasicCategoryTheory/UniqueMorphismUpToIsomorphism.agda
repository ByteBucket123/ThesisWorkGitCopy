{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.UniqueMorphismUpToIsomorphism where

--open import Cubical.Categories.Category
--open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.CompatibilityCode

record UniqueUpToIsoLeft {ℓ ℓ' ℓ''} {C : UnivalentCategory ℓ ℓ'} {A B : Precategory.ob (UnivalentCategory.cat C)}
       (D : Precategory.ob (UnivalentCategory.cat C)) (k : Precategory.hom (UnivalentCategory.cat C) A B)
       (P : Precategory.hom (UnivalentCategory.cat C) D B → Type ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    h : (k' : Precategory.hom (UnivalentCategory.cat C) D B) → P k' →
        Precategory.hom (UnivalentCategory.cat C) A D
    hInv : (k' : Precategory.hom (UnivalentCategory.cat C) D B) → P k' →
           Precategory.hom (UnivalentCategory.cat C) D A
    compH : (k' : Precategory.hom (UnivalentCategory.cat C) D B) → (pk' : P k') → k ≡ Precategory.seq (UnivalentCategory.cat C) (h k' pk') k'
    invComp : (k' : Precategory.hom (UnivalentCategory.cat C) D B) → (pk' : P k') →
              Precategory.seq (UnivalentCategory.cat C) (hInv k' pk') (h k' pk') ≡ Precategory.idn (UnivalentCategory.cat C) D
    compInv : (k' : Precategory.hom (UnivalentCategory.cat C) D B) → (pk' : P k') →
              Precategory.seq (UnivalentCategory.cat C) (h k' pk') (hInv k' pk') ≡ Precategory.idn (UnivalentCategory.cat C) A

record UniqueUpToIsoRight {ℓ ℓ' ℓ''} {C : UnivalentCategory ℓ ℓ'} {A B : Precategory.ob (UnivalentCategory.cat C)}
       (D : Precategory.ob (UnivalentCategory.cat C)) (k : Precategory.hom (UnivalentCategory.cat C) A B)
       (P : Precategory.hom (UnivalentCategory.cat C) A D → Type ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    h : (k' : Precategory.hom (UnivalentCategory.cat C) A D) → P k' → Precategory.hom (UnivalentCategory.cat C) B D
    hInv : (k' : Precategory.hom (UnivalentCategory.cat C) A D) → P k' → Precategory.hom (UnivalentCategory.cat C) D B
    compH : (k' : Precategory.hom (UnivalentCategory.cat C) A D) → (pk' : P k') → k ≡ Precategory.seq (UnivalentCategory.cat C) k' (hInv k' pk') 
    invComp : (k' : Precategory.hom (UnivalentCategory.cat C) A D) → (pk' : P k') →
              Precategory.seq (UnivalentCategory.cat C) (hInv k' pk') (h k' pk') ≡ Precategory.idn (UnivalentCategory.cat C) D
    compInv : (k' : Precategory.hom (UnivalentCategory.cat C) A D) → (pk' : P k') →
              Precategory.seq (UnivalentCategory.cat C) (h k' pk') (hInv k' pk') ≡ Precategory.idn (UnivalentCategory.cat C) B
