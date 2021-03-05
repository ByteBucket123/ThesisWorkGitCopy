{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.ZeroObject where

--open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.HelpFunctions
open import ThesisWork.CompatibilityCode

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

--*************************************************** To have zero object ************************************

record CategoryWithZeroObject {ℓ ℓ' : Level} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,CatWithZero_
  field
    obj : Precategory.ob (UnivalentCategory.cat C)
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

--********************************************************* Zero Arrow *****************************************************

record ZeroArrow {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') {Z : Precategory.ob (UnivalentCategory.cat C)} (A B : Precategory.ob (UnivalentCategory.cat C)) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor ZeroArrowConst
  field
    f : Precategory.hom (UnivalentCategory.cat C) A B
    isZero : isZeroObject C Z
    toZero : Precategory.hom (UnivalentCategory.cat C) A Z
    fromZero : Precategory.hom (UnivalentCategory.cat C) Z B
    compZero : Precategory.seq (UnivalentCategory.cat C) toZero fromZero ≡ f

--********************************************* Help function *********************************************

HelpCompZero : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B Z : Precategory.ob (UnivalentCategory.cat C)} (f : Precategory.hom (UnivalentCategory.cat C) A B) → (g : Precategory.hom (UnivalentCategory.cat C) A Z) → (h : Precategory.hom (UnivalentCategory.cat C) Z B) → Type ℓ'
HelpCompZero C f g h = Precategory.seq (UnivalentCategory.cat C) g h ≡ f

ZeroArrow≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {A B Z : Precategory.ob (UnivalentCategory.cat C)}  → {x y : ZeroArrow {ℓ} {ℓ'} C {Z} A B }
               → (s : ZeroArrow.f x ≡ ZeroArrow.f y)
               → (p : ZeroArrow.isZero x ≡ ZeroArrow.isZero y)
               → (q :  ZeroArrow.toZero x ≡ ZeroArrow.toZero y )
               → (r :  ZeroArrow.fromZero x ≡ ZeroArrow.fromZero y )
               → (λ i → HelpCompZero C (s i) (q i) (r i)) [ ZeroArrow.compZero x ≡ ZeroArrow.compZero y ]
               → x ≡ y
ZeroArrow≡ s p q r d = cong ZeroArrowConst s <*> p <*> q <*> r <*> d

-- -- -- --********************************************************* Back to Zero Arrow *****************************************************

getZeroArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (hasZero : hasZeroObject C) → ZeroArrow C {Z = (CategoryWithZeroObject.obj hasZero)} A B
getZeroArrow C {A = A} {B = B} hasZero = record {f        = Precategory.seq (UnivalentCategory.cat C) (fst (ZeroObject.isTerm (CategoryWithZeroObject.isZero hasZero) A)) (fst (ZeroObject.isInit (CategoryWithZeroObject.isZero hasZero) B)) ;
                                                 isZero   = CategoryWithZeroObject.isZero hasZero ;
                                                 toZero   = fst (ZeroObject.isTerm (CategoryWithZeroObject.isZero hasZero) A) ;
                                                 fromZero = fst (ZeroObject.isInit (CategoryWithZeroObject.isZero hasZero) B) ;
                                                 compZero = refl}

isZeroArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → hasZeroObject C → (f : Precategory.hom (UnivalentCategory.cat C) A B) → Type ℓ'
isZeroArrow C {A = A} {B = B} hasZero f = {g : Precategory.hom (UnivalentCategory.cat C) A (CategoryWithZeroObject.obj hasZero)} →
                                          {h : Precategory.hom (UnivalentCategory.cat C) (CategoryWithZeroObject.obj hasZero) B} →
                                          Precategory.seq (UnivalentCategory.cat C) g h ≡ f

ZeroArrowIsUnique : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} {f g : Precategory.hom (UnivalentCategory.cat C) A B} → (hasZero : hasZeroObject C) →
                    {h k : Precategory.hom (UnivalentCategory.cat C) A (CategoryWithZeroObject.obj hasZero)} → {j l : Precategory.hom (UnivalentCategory.cat C) (CategoryWithZeroObject.obj hasZero) B} → 
                    isZeroArrow C hasZero f → isZeroArrow C hasZero g →
                    -----------------------------------
                    f ≡ g
ZeroArrowIsUnique C {A = A} {B = B} hasZero {h = h} {k = k} {j = j} {l = l} fZeroArrow gZeroArrow =
  (sym (fZeroArrow {h} {j})) ∙
  (cong₂ (λ g h → Precategory.seq (UnivalentCategory.cat C) g h)
  (isTerminalToIsUniqueArrow C (CategoryWithZeroObject.obj hasZero) (ZeroObject.isTerm (CategoryWithZeroObject.isZero hasZero)) h k)
  (isInitialToIsUniqueArrow C (CategoryWithZeroObject.obj hasZero) (ZeroObject.isInit (CategoryWithZeroObject.isZero hasZero)) j l)) ∙
  (gZeroArrow {k} {l})


isZeroArrowIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} → (hasZero : hasZeroObject C) → (f : Precategory.hom (UnivalentCategory.cat C) A B) → isProp (isZeroArrow C hasZero f)
isZeroArrowIsProp C {A = A} {B = B} isZero f p q = implicitFunExt λ {g} → implicitFunExt (λ {h} → homIsSet (UnivalentCategory.isCat C) (Precategory.seq (UnivalentCategory.cat C) g h) f p q)
