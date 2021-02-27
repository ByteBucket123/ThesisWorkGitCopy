{-# OPTIONS --cubical #-}

module ThesisWork.HelpFunctions where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Core.Glue
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import Cubical.Foundations.Equiv

--****************************** SIGMA *****************************************

infixl 20 _<*>_
_<*>_ : ∀ {a b} {A : I → Type a} {B : ∀ i → A i → Type b}
        → ∀ {f g} → (\ i → (a : A i) → B i a) [ f ≡ g ]
        → ∀ {x y} → (p : A [ x ≡ y ])
        → (\ i → B i (p i)) [ f x ≡ g y ]
p <*> q = \ i → p i (q i)


Σ≡ : {ℓ ℓ' : Level} → ∀ {A B} → {x y : Σ {ℓ} {ℓ'} A B} → (p : fst x ≡ fst y)
             → (\ i → B (p i)) [ snd x ≡ snd y ]
             → x ≡ y
Σ≡ p q = cong (_,_) p <*> q

--*************************************************** CatIso *****************************************************************

PathEqCatIso :  {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) → (A ≡ B) ≃ (CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} A B)
PathEqCatIso C A B = pathToIso A B , univ (UnivalentCategory.isUni C) A B

CatIsoToPath :  {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (A B : Precategory.ob (UnivalentCategory.cat C)) → (CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} A B) → A ≡ B
CatIsoToPath C A B = invEq (PathEqCatIso C A B)

flipEq : ∀ {ℓ} {C : Type ℓ} → {A B : C} → (p : A ≡ B) → isProp (A ≡ B) → isProp (B ≡ A) → (A ≡ B) ≃ (B ≡ A)
flipEq p propA≡B propB≡A = sym , (record{equiv-proof = λ y → (p , propB≡A (sym p) y) , λ y' → Σ≡ (propA≡B p (fst y'))
                           (isProp→PathP (λ i →
                           isProp→isSet propB≡A (sym (propA≡B p (fst y') i)) y
                           ) (propB≡A (sym p) y) (snd y'))
                           })

HelpSecEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : ob (UnivalentCategory.cat C)} →
            (h : hom (UnivalentCategory.cat C) A B) → (hinv : hom (UnivalentCategory.cat C) B A) → Type ℓ'
HelpSecEq C {B = B} h hinv = (UnivalentCategory.cat C) .seq hinv h ≡ (UnivalentCategory.cat C) .idn B

HelpRetEq : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : ob (UnivalentCategory.cat C)} →
            (h : hom (UnivalentCategory.cat C) A B) → (hinv : hom (UnivalentCategory.cat C) B A) → Type ℓ'
HelpRetEq C {A = A} h hinv = (UnivalentCategory.cat C) .seq h hinv ≡ (UnivalentCategory.cat C) .idn A

CatIso≡ : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → {A B : Precategory.ob (UnivalentCategory.cat C)} →
          {x y : CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} A B} → (p : CatIso.h x ≡ CatIso.h y)
           → (q : CatIso.h⁻¹ x ≡ CatIso.h⁻¹ y) → (\ i → HelpSecEq C (p i) (q i)) [ CatIso.sec x ≡ CatIso.sec y ]
           → (\ i → HelpRetEq C (p i) (q i)) [ CatIso.ret x ≡ CatIso.ret y ]
           → x ≡ y
CatIso≡ p q r s = cong catiso p <*> q <*> r <*> s

HelpSecEq2 : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') → {A B : ob C} → (h : hom C A B) → (hinv : hom C B A) → Type ℓ'
HelpSecEq2 C {B = B} h hinv = C .seq hinv h ≡ C .idn B

HelpRetEq2 : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') → {A B : ob C} → (h : hom C A B) → (hinv : hom C B A) → Type ℓ'
HelpRetEq2 C {A = A} h hinv = C .seq h hinv ≡ C .idn A


CatIsoPreCat≡ : {ℓ ℓ' : Level} → {C : Precategory ℓ ℓ'} → {A B : Precategory.ob C} →
                {x y : CatIso {ℓ} {ℓ'} {C} A B} → (p : CatIso.h x ≡ CatIso.h y)
                → (q : CatIso.h⁻¹ x ≡ CatIso.h⁻¹ y) → (\ i → HelpSecEq2 C (p i) (q i)) [ CatIso.sec x ≡ CatIso.sec y ]
                → (\ i → HelpRetEq2 C (p i) (q i)) [ CatIso.ret x ≡ CatIso.ret y ]
                → x ≡ y
CatIsoPreCat≡ p q r s = cong catiso p <*> q <*> r <*> s

CatIsoCat≡ : {ℓ ℓ' : Level} → {C : Precategory ℓ ℓ'} → (isCat : isCategory C) → {A B : Precategory.ob C} →
                {x y : CatIso {ℓ} {ℓ'} {C} A B}
                → (p : CatIso.h x ≡ CatIso.h y)
                → (q : CatIso.h⁻¹ x ≡ CatIso.h⁻¹ y)
                → x ≡ y
CatIsoCat≡ {C = C} isCat {A = A} {B = B} {x = x} {y = y} p q =
  CatIsoPreCat≡ p q
  (isProp→PathP (λ i → λ t s → homIsSet isCat (C .seq (q i) (p i)) (C .idn B) t s) (CatIso.sec x) (CatIso.sec y))
  (isProp→PathP (λ i → λ t s → homIsSet isCat (C .seq (p i) (q i)) (C .idn A) t s) (CatIso.ret x) (CatIso.ret y))

invCatIso : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} →
             (CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} A B) → (CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} B A)
invCatIso C catIso = record {h = CatIso.h⁻¹ catIso ;
                             h⁻¹ = CatIso.h catIso ;
                             sec = CatIso.ret catIso ;
                             ret = CatIso.sec catIso}

--flipCatIso : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {A B : Precategory.ob (UnivalentCategory.cat C)} →
--             (CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} A B) ≃ (CatIso {ℓ} {ℓ'} {UnivalentCategory.cat C} B A)
--flipCatIso C = (invCatIso C) , record {equiv-proof = λ y → ((invCatIso C y) , refl) , λ catIso → Σ≡
--               {!!}
--               (isProp→PathP (λ i → {!!}) {!!} {!!})
--               }

--flipEquivCatIso : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {x y : Precategory.ob (UnivalentCategory.cat C)} → isEquiv (pathToIso {ℓ} {ℓ'} {UnivalentCategory.cat C} y x)
--flipEquivCatIso C {x = x} {y = y} = snd (compEquiv (invEquiv (flipEq {!!} {!!} {!!})) (compEquiv ( pathToIso x y , isUnivalent.univ (UnivalentCategory.isUni C) x y) (flipCatIso C)))




--****************************************************** Pair *****************************************************************

--record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
--  constructor _,_
--  field
--    fst : A
--    snd : B fst


record Pair {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  constructor <_,_>
  field
    fstElem : A
    sndElem : B

PairEq : {ℓ ℓ' : Level} → {A : Set ℓ} →  {B : Set ℓ'} → (x y : Pair A B) → Pair.fstElem x ≡ Pair.fstElem y → Pair.sndElem x ≡ Pair.sndElem y → x ≡ y
PairEq x y x₁=y₁ x₂=y₂ = cong <_,_> x₁=y₁ <*> x₂=y₂

--***************************************************** LiftFunExt ************************************************************

--There should be a more elegant way to do this
liftFunExt : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → isSet B → {h k : A → B} → (p q : h ≡ k) → p ≡ q
liftFunExt setB {h = h} {k = k} p q = λ i → funExt (λ x → setB (h x) (k x) (λ j → (p j) x) (λ j → (q j) x) i)
