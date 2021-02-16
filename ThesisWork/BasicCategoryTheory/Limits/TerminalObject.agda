{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.TerminalObject where

open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.HelpFunctions

--********************************************* Terminal **********************************************************

isTerminalObject : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (B : Precategory.ob (UnivalentCategory.cat C)) → Type (ℓ-max ℓ ℓ')
isTerminalObject C B = (A : Precategory.ob (UnivalentCategory.cat C)) → isContr (hom (UnivalentCategory.cat C) A B)

isTerminalToIsUniqueArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (B : Precategory.ob (UnivalentCategory.cat C)) → isTerminalObject C B → {A : Precategory.ob (UnivalentCategory.cat C)} → (f : hom (UnivalentCategory.cat C) A B) → isUniqueArrow C f
isTerminalToIsUniqueArrow C B isTerminalB {A = A} f g = isContr→isProp (isTerminalB A) f g

isTerminalObjectIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (B : Precategory.ob (UnivalentCategory.cat C)) → isProp (isTerminalObject C B)
isTerminalObjectIsProp {ℓ = ℓ}  {ℓ' = ℓ'} C B p q = funExt (λ A → Σ≡ {ℓ'} {ℓ'} ((snd (p A) (fst (q A)))) (funExt λ y → isProp→PathP (λ i → homIsSet (UnivalentCategory.isCat C) (snd (p A) (fst (q A)) i) y) (snd (p A) y) (snd (q A) y)))

--TODO
--TerinalToInitialInOp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (B : Precategory.ob (UnivalentCategory.cat C)) → isTerminalObject C B → isInitialObject {!!} B
--TerinalToInitialInOp = {!!}

TerminalObjectIsUniqueHelp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) → isTerminalObject C A → isTerminalObject C B → CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} A B
TerminalObjectIsUniqueHelp C A B AisTerm BisTerm = record {h = fst (BisTerm A) ;
                                                          h⁻¹ = fst (AisTerm B) ;
                                                          sec = isContr→isProp (BisTerm B) ((UnivalentCategory.cat C .seq (fst (AisTerm B)) (fst (BisTerm A)))) ((UnivalentCategory.cat C .idn B)) ;
                                                          ret = isContr→isProp (AisTerm A) ((UnivalentCategory.cat C .seq (fst (BisTerm A)) (fst (AisTerm B)))) ((UnivalentCategory.cat C .idn A)) }


TerminalObjectIsUnique : {ℓ ℓ' : Level} →
                         (C : UnivalentCategory ℓ ℓ') →
                         {A B : Precategory.ob (UnivalentCategory.cat C)} →
                         isTerminalObject C A →
                         isTerminalObject C B →
                         -------------------------------------------------
                         A ≡ B
TerminalObjectIsUnique C {A = A} {B = B} AisTerm BisTerm = CatIsoToPath C A B (TerminalObjectIsUniqueHelp C A B AisTerm BisTerm)

--*************************************************** To have terminal object ************************************

record CategoryWithTerminalObject {ℓ ℓ' : Level} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor _,CatWithTerm_
  field
    obj : ob (UnivalentCategory.cat C)
    isTerm : isTerminalObject C obj

CatWithTerm≡ : {ℓ ℓ' : Level} {C : UnivalentCategory ℓ ℓ'} {x y : CategoryWithTerminalObject C}
               → (p : CategoryWithTerminalObject.obj x ≡ CategoryWithTerminalObject.obj y)
               → (λ i → isTerminalObject C (p i)) [ CategoryWithTerminalObject.isTerm x ≡ CategoryWithTerminalObject.isTerm y ]
               → x ≡ y
CatWithTerm≡ p q = cong (_,CatWithTerm_) p <*> q

hasTerminalObject : {ℓ ℓ' : Level} →
                  (C : UnivalentCategory ℓ ℓ') →
                  ---------------------------------------------------
                  Type (ℓ-max ℓ ℓ')
hasTerminalObject C = CategoryWithTerminalObject C



hasTerminalObjectIsProp : {ℓ ℓ' : Level} →
                  (C : UnivalentCategory ℓ ℓ') →
                  ---------------------------------------------------
                  isProp (hasTerminalObject C)
hasTerminalObjectIsProp {ℓ = ℓ} {ℓ' = ℓ'} C p q = CatWithTerm≡ (TerminalObjectIsUnique C (CategoryWithTerminalObject.isTerm p) (CategoryWithTerminalObject.isTerm q))
                                                              (isProp→PathP (λ i → isTerminalObjectIsProp C
                                                              ((TerminalObjectIsUnique C (CategoryWithTerminalObject.isTerm p) (CategoryWithTerminalObject.isTerm q)) i))
                                                              (CategoryWithTerminalObject.isTerm p) ((CategoryWithTerminalObject.isTerm q)))
                                                
