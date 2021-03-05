{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.ZeroObject where

open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.HelpFunctions

--********************************************* Zero **********************************************************

record ZeroObject {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') (A : Precategory.ob (UnivalentCategory.cat C)) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,Zero_
  field
    isInit : isInitialObject C A
    isTerm : isTerminalObject C A

--********************************************* Help function *********************************************

ZeroObj≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {D : Precategory.ob (UnivalentCategory.cat C)} → {x y : ZeroObject {ℓ} {ℓ'} C D} → (p : ZeroObject.isInit x ≡ ZeroObject.isInit y)
             → (q :  ZeroObject.isTerm x ≡ ZeroObject.isTerm y )
             → x ≡ y
ZeroObj≡ p q = cong (_,Zero_) p <*> q

--********************************************* isZero **********************************************************

isZeroObject : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (Z : Precategory.ob (UnivalentCategory.cat C)) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
isZeroObject C Z = ZeroObject C Z

isZeroObjectIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (Z : Precategory.ob (UnivalentCategory.cat C)) → isProp (isZeroObject C Z)
isZeroObjectIsProp C Z p q = ZeroObj≡ (isInitialObjectIsProp C Z (ZeroObject.isInit p) (ZeroObject.isInit q)) (isTerminalObjectIsProp C Z (ZeroObject.isTerm p) (ZeroObject.isTerm q))

ZeroObjectIsUnique : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {Z A : Precategory.ob (UnivalentCategory.cat C)} → isZeroObject C Z → isZeroObject C A → Z ≡ A
ZeroObjectIsUnique C {Z = Z} {A = A} ZisZero AisZero = InitialObjectIsUnique C Z A (ZeroObject.isInit ZisZero) (ZeroObject.isInit AisZero)

--********************************************************* Zero Arrow *****************************************************

record ZeroArrow {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') {A B Z : Precategory.ob (UnivalentCategory.cat C)} (f : hom (UnivalentCategory.cat C) A B) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,Zero_,_
  field
    isZero : isZeroObject C Z
    toZero : hom (UnivalentCategory.cat C) A Z
    fromZero : hom (UnivalentCategory.cat C) Z B
    compZero : seq (UnivalentCategory.cat C) toZero fromZero ≡ f

-- --********************************************* Help function *********************************************

HelpCompZero : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B Z : Precategory.ob (UnivalentCategory.cat C)} (f : hom (UnivalentCategory.cat C) A B) → (g : hom (UnivalentCategory.cat C) A Z) → (h : hom (UnivalentCategory.cat C) Z B) → Type ℓ'
HelpCompZero C f g h = seq (UnivalentCategory.cat C) g h ≡ f

ZeroArrow≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {A B Z : Precategory.ob (UnivalentCategory.cat C)} {f : hom (UnivalentCategory.cat C) A B} → {x y : ZeroArrow {ℓ} {ℓ'} C {A} {B} {Z} f}
               → (p : ZeroArrow.isZero x ≡ ZeroArrow.isZero y)
               → (q :  ZeroArrow.toZero x ≡ ZeroArrow.toZero y )
               → (r :  ZeroArrow.fromZero x ≡ ZeroArrow.fromZero y )
               → (λ i → HelpCompZero C f (q i) (r i)) [ ZeroArrow.compZero x ≡ ZeroArrow.compZero y ]
               → x ≡ y
ZeroArrow≡ p q r d = cong (_,Zero_,_) p <*> q <*> r <*> d

-- -- --********************************************************* Back to Zero Arrow *****************************************************

isZeroArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B Z : Precategory.ob (UnivalentCategory.cat C)} → isZeroObject C Z → (f : hom (UnivalentCategory.cat C) A B) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
isZeroArrow C {A = A} {B = B} {Z = Z} isZeroZ f = ZeroArrow C {Z = Z} f

isZeroArrowIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B Z : Precategory.ob (UnivalentCategory.cat C)} → (isZero : isZeroObject C Z) → (f : hom (UnivalentCategory.cat C) A B) → isProp (isZeroArrow C isZero f)
isZeroArrowIsProp C {A = A} {B = B} {Z = Z} isZero f p q = ZeroArrow≡ (isZeroObjectIsProp C Z (ZeroArrow.isZero p) (ZeroArrow.isZero q))
                                                                       (isContr→isProp (ZeroObject.isTerm isZero A) (ZeroArrow.toZero p) (ZeroArrow.toZero q))
                                                                       (isContr→isProp (ZeroObject.isInit isZero B) (ZeroArrow.fromZero p) (ZeroArrow.fromZero q))
                                                                       (isProp→PathP (λ i → homIsSet (UnivalentCategory.isCat C) (seq (UnivalentCategory.cat C)
                                                                       (isContr→isProp (ZeroObject.isTerm isZero A) (ZeroArrow.toZero p) (ZeroArrow.toZero q) i)
                                                                       (isContr→isProp (ZeroObject.isInit isZero B) (ZeroArrow.fromZero p) (ZeroArrow.fromZero q) i))
                                                                       f) (ZeroArrow.compZero p) (ZeroArrow.compZero q))

ZeroArrowIsUnique : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B Z : Precategory.ob (UnivalentCategory.cat C)} {f g : Precategory.hom (UnivalentCategory.cat C) A B} (isZero : isZeroObject C Z) → isZeroArrow C isZero f → isZeroArrow C isZero g → f ≡ g
ZeroArrowIsUnique C {A = A} {B = B} {Z = Z} ZisZero fZeroArrow gZeroArrow = (sym (ZeroArrow.compZero  fZeroArrow)) ∙ ((cong₂ (λ h k → seq (UnivalentCategory.cat C) h k)
                                                                            (isTerminalToIsUniqueArrow C Z (ZeroObject.isTerm ZisZero) (ZeroArrow.toZero fZeroArrow) (ZeroArrow.toZero gZeroArrow))
                                                                            (isInitialToIsUniqueArrow C Z (ZeroObject.isInit ZisZero) (ZeroArrow.fromZero fZeroArrow) (ZeroArrow.fromZero gZeroArrow))) ∙
                                                                            (ZeroArrow.compZero gZeroArrow))

--*************************************************** To have zero object ************************************

record CategoryWithZeroObject {ℓ ℓ' : Level} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,CatWithZero_
  field
    obj : ob (UnivalentCategory.cat C)
    isZero : isZeroObject C obj

CatWithZero≡ : {ℓ ℓ' : Level} {C : UnivalentCategory ℓ ℓ'} {x y : CategoryWithZeroObject C}
               → (p : CategoryWithZeroObject.obj x ≡ CategoryWithZeroObject.obj y)
               → (λ i → isZeroObject C (p i)) [ CategoryWithZeroObject.isZero x ≡ CategoryWithZeroObject.isZero y ]
               → x ≡ y
CatWithZero≡ p q = cong (_,CatWithZero_) p <*> q

hasZeroObject : {ℓ ℓ' : Level} →
                (C : UnivalentCategory ℓ ℓ') →
                ---------------------------------------------------
                Type (ℓ-suc (ℓ-max ℓ ℓ'))
hasZeroObject C = CategoryWithZeroObject C



hasZeroObjectIsProp : {ℓ ℓ' : Level} →
                      (C : UnivalentCategory ℓ ℓ') →
                      ---------------------------------------------------
                      isProp (hasZeroObject C)
hasZeroObjectIsProp {ℓ = ℓ} {ℓ' = ℓ'} C p q = CatWithZero≡ (ZeroObjectIsUnique C (CategoryWithZeroObject.isZero p) (CategoryWithZeroObject.isZero q))
                                             (isProp→PathP (λ i →
                                             isZeroObjectIsProp C ((ZeroObjectIsUnique C (CategoryWithZeroObject.isZero p) (CategoryWithZeroObject.isZero q)) i))
                                             (CategoryWithZeroObject.isZero p) (CategoryWithZeroObject.isZero q))

getZeroArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (hasZero : hasZeroObject C) → {f : hom (UnivalentCategory.cat C) A B} → ZeroArrow C {Z = (CategoryWithZeroObject.obj hasZero)} f
getZeroArrow C {A = A} {B = B} hasZero = record {isZero   = CategoryWithZeroObject.isZero hasZero ;
                                 toZero   = fst (ZeroObject.isTerm (CategoryWithZeroObject.isZero hasZero) A) ;
                                 fromZero = fst (ZeroObject.isInit (CategoryWithZeroObject.isZero hasZero) B) ;
                                 compZero = {!!}}
