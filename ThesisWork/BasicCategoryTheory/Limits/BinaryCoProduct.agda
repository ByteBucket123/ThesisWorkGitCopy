{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct where

open import Cubical.Categories.Category
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


record BinaryCoProduct {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') (A B : Precategory.ob (UnivalentCategory.cat C)) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,BinCoProd_,_,_
  field
    A×B : ob (UnivalentCategory.cat C)
    pA : hom (UnivalentCategory.cat C) A A×B
    pB : hom (UnivalentCategory.cat C) B A×B
    uni : {Z : ob (UnivalentCategory.cat C)} → (f : hom (UnivalentCategory.cat C) A Z) → (g : hom (UnivalentCategory.cat C) B Z) →
          isContr (Σ (hom (UnivalentCategory.cat C) A×B Z)
          (λ z → Pair (seq (UnivalentCategory.cat C) pA z ≡ f) (seq (UnivalentCategory.cat C) pB z ≡ g)))

--TODO: Could be done more cleanly if I looked up how to prove equality of objects is a property
isBinaryCoProduct : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                  (A×B : ob (UnivalentCategory.cat C)) → Type ((ℓ-suc (ℓ-max ℓ ℓ')))
isBinaryCoProduct C A B A×B = ∥ Σ (BinaryCoProduct C A B) (λ binProd → (BinaryCoProduct.A×B binProd) ≡ A×B) ∥

isBinaryCoProductIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                        (A×B : ob (UnivalentCategory.cat C)) → isProp (isBinaryCoProduct C A B A×B)
isBinaryCoProductIsProp C A B A×B = propTruncIsProp

hasBinaryCoProducts : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                    Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasBinaryCoProducts C A B = ∥ ((A B : Precategory.ob (UnivalentCategory.cat C)) →
                            Σ (ob (UnivalentCategory.cat C)) (isBinaryCoProduct C A B)) ∥

hasBinaryCoProductsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                          isProp (hasBinaryCoProducts C A B)
hasBinaryCoProductsIsProp C A B = propTruncIsProp

hasAllBinaryCoProducts : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasAllBinaryCoProducts C = (A B : Precategory.ob (UnivalentCategory.cat C)) → hasBinaryCoProducts C A B

hasAllBinaryCoProductsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → isProp (hasAllBinaryCoProducts C)
hasAllBinaryCoProductsIsProp C p q = funExt (λ A → funExt (λ B → hasBinaryCoProductsIsProp C A B (p A B) (q A B)))
