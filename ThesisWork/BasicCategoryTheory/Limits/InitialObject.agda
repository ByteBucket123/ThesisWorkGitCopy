{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.Limits.InitialObject where

open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.HelpFunctions

--********************************************* Initial **********************************************************

isInitialObject : {ℓ ℓ' : Level} →
                  (C : UnivalentCategory ℓ ℓ') →
                  (A : Precategory.ob (UnivalentCategory.cat C)) →
                  ---------------------------------------------------
                  Type (ℓ-max ℓ ℓ')
isInitialObject C A = (B : Precategory.ob (UnivalentCategory.cat C)) →
                       isContr (hom (UnivalentCategory.cat C) A B)

isInitialToIsUniqueArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A : Precategory.ob (UnivalentCategory.cat C)) → isInitialObject C A → {B : Precategory.ob (UnivalentCategory.cat C)} → (f : hom (UnivalentCategory.cat C) A B) → isUniqueArrow C f
isInitialToIsUniqueArrow C A isInitialA {B = B} f g = isContr→isProp (isInitialA B) f g

isInitialObjectIsProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A : Precategory.ob (UnivalentCategory.cat C)) → isProp (isInitialObject C A)
isInitialObjectIsProp {ℓ = ℓ}  {ℓ' = ℓ'} C A p q = funExt (λ B → Σ≡ {ℓ'} {ℓ'} ((snd (p B) (fst (q B)))) (funExt λ y → isProp→PathP (λ i → homIsSet (UnivalentCategory.isCat C) (snd (p B) (fst (q B)) i) y) (snd (p B) y) (snd (q B) y)))

--isInitialObjectIsProp {ℓ = ℓ}  {ℓ' = ℓ'} C A p q = funExt (λ B → Σ≡ {ℓ'} {ℓ'} (snd (p B) (fst (q B))) (funExt (λ y → homIsSet {ℓ} {ℓ'} {!UnivalentCategory.isCat C!} {!!} {!!} {!!} {!!} {!!})))
--isInitialObjectIsProp {ℓ = ℓ}  {ℓ' = ℓ'} C A p q = funExt (λ B → Σ≡ {ℓ'} {ℓ'} (snd (p B) (fst (q B))) {!!})
--isInitialObjectIsProp {ℓ = ℓ}  {ℓ' = ℓ'} C A p q = funExt (λ B → Σ≡ {ℓ'} {ℓ'} (snd (p B) (fst (q B))) λ i → λ y → isCategory.homIsSet {ℓ} {ℓ'} (UnivalentCategory.isCat C) {!!} {!!} {!!} {!!} i)
--isInitialObjectIsProp {ℓ = ℓ}  {ℓ' = ℓ'} C A p q = funExt (λ B → Σ≡ {!snd (p B) (fst (q B))!} {!!})
--homIsSet (UnivalentCategory.isCat C) g h (p D g h gEqH) (q D g h gEqH))))

InitialObjectIsUniqueHelp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) → isInitialObject C A → isInitialObject C B → CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} A B
InitialObjectIsUniqueHelp C A B AisInit BisInit = record {h = fst (AisInit B) ;
                                                          h⁻¹ = fst (BisInit A) ;
                                                          sec = isContr→isProp (BisInit B) (UnivalentCategory.cat C .seq (fst (BisInit A)) (fst (AisInit B))) (UnivalentCategory.cat C .idn B) ;
                                                          ret = isContr→isProp (AisInit A) (UnivalentCategory.cat C .seq (fst (AisInit B)) (fst (BisInit A))) (UnivalentCategory.cat C .idn A)}


InitialObjectIsUnique : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) → isInitialObject C A → isInitialObject C B → A ≡ B
InitialObjectIsUnique {ℓ = ℓ} {ℓ' = ℓ'} C A B AisInit BisInit = CatIsoToPath C A B (InitialObjectIsUniqueHelp C A B AisInit BisInit)

--*************************************************** To have initial object ************************************

record CategoryWithInitialObject {ℓ ℓ' : Level} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor _,CatWithInit_
  field
    obj : ob (UnivalentCategory.cat C)
    isInit : isInitialObject C obj

CatWithInit≡ : {ℓ ℓ' : Level} {C : UnivalentCategory ℓ ℓ'} {x y : CategoryWithInitialObject C}
               → (p : CategoryWithInitialObject.obj x ≡ CategoryWithInitialObject.obj y)
               → (λ i → isInitialObject C (p i)) [ CategoryWithInitialObject.isInit x ≡ CategoryWithInitialObject.isInit y ]
               → x ≡ y
CatWithInit≡ p q = cong (_,CatWithInit_) p <*> q

hasInitialObject : {ℓ ℓ' : Level} →
                  (C : UnivalentCategory ℓ ℓ') →
                  ---------------------------------------------------
                  Type (ℓ-max ℓ ℓ')
hasInitialObject C = CategoryWithInitialObject C



hasInitialObjectIsProp : {ℓ ℓ' : Level} →
                  (C : UnivalentCategory ℓ ℓ') →
                  ---------------------------------------------------
                  isProp (hasInitialObject C)
hasInitialObjectIsProp {ℓ = ℓ} {ℓ' = ℓ'} C p q = CatWithInit≡ (InitialObjectIsUnique C (CategoryWithInitialObject.obj p) ((CategoryWithInitialObject.obj q)) ((CategoryWithInitialObject.isInit p)) ((CategoryWithInitialObject.isInit q)))
                                               (isProp→PathP
                                               (λ i → isInitialObjectIsProp C ((InitialObjectIsUnique C (CategoryWithInitialObject.obj p) ((CategoryWithInitialObject.obj q)) ((CategoryWithInitialObject.isInit p)) ((CategoryWithInitialObject.isInit q))) i))
                                               (CategoryWithInitialObject.isInit p) (CategoryWithInitialObject.isInit q))
                                                
