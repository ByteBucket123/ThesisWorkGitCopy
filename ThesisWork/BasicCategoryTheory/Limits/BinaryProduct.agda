{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.BinaryProduct where

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


record BinaryProduct {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') (A B : Precategory.ob (UnivalentCategory.cat C)) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,BinProd_,_,_
  field
    A×B : ob (UnivalentCategory.cat C)
    pA : hom (UnivalentCategory.cat C) A×B A
    pB : hom (UnivalentCategory.cat C) A×B B
    uni : {Z : ob (UnivalentCategory.cat C)} → (f : hom (UnivalentCategory.cat C) Z A) → (g : hom (UnivalentCategory.cat C) Z B) →
          isContr (Σ (hom (UnivalentCategory.cat C) Z A×B)
          (λ z → Pair (seq (UnivalentCategory.cat C) z pA ≡ f) (seq (UnivalentCategory.cat C) z pB ≡ g)))

--TODO: Could be done more cleanly if I looked up how to prove equality of objects is a property
isBinaryProduct : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                  (A×B : ob (UnivalentCategory.cat C)) → Type ((ℓ-suc (ℓ-max ℓ ℓ')))
isBinaryProduct C A B A×B = ∥ Σ (BinaryProduct C A B) (λ binProd → (BinaryProduct.A×B binProd) ≡ A×B) ∥

isBinaryProductIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                        (A×B : ob (UnivalentCategory.cat C)) → isProp (isBinaryProduct C A B A×B)
isBinaryProductIsProp C A B A×B = propTruncIsProp

hasBinaryProducts : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                    Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasBinaryProducts C A B = ∥ ((A B : Precategory.ob (UnivalentCategory.cat C)) →
                            Σ (ob (UnivalentCategory.cat C)) (isBinaryProduct C A B)) ∥

hasBinaryProductsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                          isProp (hasBinaryProducts C A B)
hasBinaryProductsIsProp C A B = propTruncIsProp

hasAllBinaryProducts : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasAllBinaryProducts C = (A B : Precategory.ob (UnivalentCategory.cat C)) → hasBinaryProducts C A B

hasAllBinaryProductsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → isProp (hasAllBinaryProducts C)
hasAllBinaryProductsIsProp C p q = funExt (λ A → funExt (λ B → hasBinaryProductsIsProp C A B (p A B) (q A B)))
