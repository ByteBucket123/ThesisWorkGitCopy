{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct where

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

record BinaryCoProduct {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') (A B : Precategory.ob (UnivalentCategory.cat C)) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor BinCoProd
  field
    A×B : Precategory.ob (UnivalentCategory.cat C)
    pA : Precategory.hom (UnivalentCategory.cat C) A A×B
    pB : Precategory.hom (UnivalentCategory.cat C) B A×B
    <_×_> : {Z : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A Z) →
            (g : Precategory.hom (UnivalentCategory.cat C) B Z) → Precategory.hom (UnivalentCategory.cat C) A×B Z
    pAcomp : {Z : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A Z) →
             (g : Precategory.hom (UnivalentCategory.cat C) B Z) → Precategory.seq (UnivalentCategory.cat C) pA < f × g > ≡ f
    pBcomp : {Z : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A Z) →
             (g : Precategory.hom (UnivalentCategory.cat C) B Z) → Precategory.seq (UnivalentCategory.cat C) pB < f × g > ≡ g
    uni : {Z : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A Z) →
          (g : Precategory.hom (UnivalentCategory.cat C) B Z) → (h : Precategory.hom (UnivalentCategory.cat C) A×B Z) →
          Precategory.seq (UnivalentCategory.cat C) pA h ≡ f → Precategory.seq (UnivalentCategory.cat C) pB h ≡ g →
          < f × g > ≡ h

--TODO: Could be done more cleanly if I looked up how to prove equality of objects is a property
isBinaryCoProduct : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                  (A×B : Precategory.ob (UnivalentCategory.cat C)) → Type ((ℓ-suc (ℓ-max ℓ ℓ')))
isBinaryCoProduct C A B A×B = ∥ Σ (BinaryCoProduct C A B) (λ binProd → (BinaryCoProduct.A×B binProd) ≡ A×B) ∥

isBinaryCoProductIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                        (A×B : Precategory.ob (UnivalentCategory.cat C)) → isProp (isBinaryCoProduct C A B A×B)
isBinaryCoProductIsProp C A B A×B = propTruncIsProp

hasBinaryCoProduct : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                    Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasBinaryCoProduct C A B = ∥ Σ (Precategory.ob (UnivalentCategory.cat C)) (isBinaryCoProduct C A B) ∥

hasBinaryCoProductsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) →
                          isProp (hasBinaryCoProduct C A B)
hasBinaryCoProductsIsProp C A B = propTruncIsProp

hasAllBinaryCoProducts : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasAllBinaryCoProducts C = (A B : Precategory.ob (UnivalentCategory.cat C)) → hasBinaryCoProduct C A B

hasAllBinaryCoProductsIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → isProp (hasAllBinaryCoProducts C)
hasAllBinaryCoProductsIsProp C p q = funExt (λ A → funExt (λ B → hasBinaryCoProductsIsProp C A B (p A B) (q A B)))
