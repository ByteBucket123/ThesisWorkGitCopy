{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.UniqueMorphismUpToIsomorphism where

open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions

record UniqueUpToIsoLeft {ℓ ℓ' ℓ''} {C : UnivalentCategory ℓ ℓ'} {A B : ob (UnivalentCategory.cat C)}
       (D : ob (UnivalentCategory.cat C)) (k : hom (UnivalentCategory.cat C) A B)
       (P : hom (UnivalentCategory.cat C) D B → Type ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    h : (k' : hom (UnivalentCategory.cat C) D B) → P k' →
        hom (UnivalentCategory.cat C) A D
    hInv : (k' : hom (UnivalentCategory.cat C) D B) → P k' →
           hom (UnivalentCategory.cat C) D A
    compH : (k' : hom (UnivalentCategory.cat C) D B) → (pk' : P k') → k ≡ seq (UnivalentCategory.cat C) (h k' pk') k'
    invComp : (k' : hom (UnivalentCategory.cat C) D B) → (pk' : P k') →
              seq (UnivalentCategory.cat C) (hInv k' pk') (h k' pk') ≡ idn (UnivalentCategory.cat C) D
    compInv : (k' : hom (UnivalentCategory.cat C) D B) → (pk' : P k') →
              seq (UnivalentCategory.cat C) (h k' pk') (hInv k' pk') ≡ idn (UnivalentCategory.cat C) A

record UniqueUpToIsoRight {ℓ ℓ' ℓ''} {C : UnivalentCategory ℓ ℓ'} {A B : ob (UnivalentCategory.cat C)}
       (D : ob (UnivalentCategory.cat C)) (k : hom (UnivalentCategory.cat C) A B)
       (P : hom (UnivalentCategory.cat C) A D → Type ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    h : (k' : hom (UnivalentCategory.cat C) A D) → P k' → hom (UnivalentCategory.cat C) B D
    hInv : (k' : hom (UnivalentCategory.cat C) A D) → P k' → hom (UnivalentCategory.cat C) D B
    compH : (k' : hom (UnivalentCategory.cat C) A D) → (pk' : P k') → k ≡ seq (UnivalentCategory.cat C) k' (hInv k' pk') 
    invComp : (k' : hom (UnivalentCategory.cat C) A D) → (pk' : P k') →
              seq (UnivalentCategory.cat C) (hInv k' pk') (h k' pk') ≡ idn (UnivalentCategory.cat C) D
    compInv : (k' : hom (UnivalentCategory.cat C) A D) → (pk' : P k') →
              seq (UnivalentCategory.cat C) (h k' pk') (hInv k' pk') ≡ idn (UnivalentCategory.cat C) B
