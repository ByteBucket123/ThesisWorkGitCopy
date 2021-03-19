{-# OPTIONS --cubical #-}

module ThesisWork.UnivalentFormulations where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import ThesisWork.CompatibilityCode
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Fiberwise

ob = Precategory.ob

infixl 20 _<*>_
_<*>_ : ∀ {a b} {A : I → Type a} {B : ∀ i → A i → Type b}
        → ∀ {f g} → (\ i → (a : A i) → B i a) [ f ≡ g ]
        → ∀ {x y} → (p : A [ x ≡ y ])
        → (\ i → B i (p i)) [ f x ≡ g y ]
p <*> q = \ i → p i (q i)

tempΣ≡ : {ℓ ℓ' : Level} → ∀ {A B} → {x y : Σ {ℓ} {ℓ'} A B} → (p : fst x ≡ fst y)
                       → (\ i → B (p i)) [ snd x ≡ snd y ]
                       → x ≡ y
tempΣ≡ p q = cong (_,_) p <*> q

--Alternative definition of univalent category.

record isUnivalentAlt {ℓ ℓ' : Level} (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x : ob C) → isContr (Σ (ob C) (λ y → CatIso {C = C} x y))

isoEquivToUnivalentHelp : {ℓ : Level} → {C : Precategory ℓ ℓ} →
                      ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) →
                      ((x : ob C) → isContr (Σ (ob C) (λ y →  x ≡ y))) →
                      isUnivalentAlt C
isoEquivToUnivalentHelp {C = C} isocat contrEq = record{ univ = λ x → transport (cong (λ x → isContr (Σ (ob C) x)) (funExt (λ y → ua (isocat x y)))) (contrEq x) }

isoEquivToUnivalent : {ℓ : Level} → {C : Precategory ℓ ℓ} →
                      ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) →
                      isUnivalentAlt C
isoEquivToUnivalent = flip isoEquivToUnivalentHelp (λ x → isContrSingl x)

--************************************************************* Help Theorems ******************************************************************************************

idCatIso : {ℓ ℓ' : Level} → {C : Precategory ℓ ℓ'} → (x : Precategory.ob C) → CatIso {C = C} x x
idCatIso {C = C} x = catiso (Precategory.idn C x) (Precategory.idn C x) (Precategory.seq-λ C (Precategory.idn C x)) (Precategory.seq-ρ C (Precategory.idn C x))



--************************************************************* *******************************************************************************************

makeUnivalentFromSet : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') →
                       ((x y : Precategory.ob C) → isProp (x ≡ y)) →
                       ((x y : Precategory.ob C) → isProp (CatIso {C = C} x y)) →
                       ((x y : Precategory.ob C) → CatIso {C = C} x y → x ≡ y) →
                       isUnivalent C
makeUnivalentFromSet C propEq propCatIso catIso→Eq = record {univ = λ x y → equivIsEquiv (isoToEquiv
  (record {fun = pathToIso x y ;
           inv = catIso→Eq x y ;
           leftInv = λ z → propEq x y (catIso→Eq x y (pathToIso x y z)) z ;
           rightInv = λ z → propCatIso x y (pathToIso x y (catIso→Eq x y z)) z }))}

makeUnivalentFromSetEq : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                       ((x y : Precategory.ob C) → isProp (x ≡ y)) →
                       ((x y : Precategory.ob C) → (CatIso {C = C} x y) ≃ (x ≡ y)) →
                       isUnivalent C
makeUnivalentFromSetEq C propEq EquivIso = makeUnivalentFromSet C propEq (λ x y → transport (cong isProp (sym (ua (EquivIso x y)))) (propEq x y)) λ x y → equivFun (EquivIso x y)

univalent→Alt' : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                ((x y : Precategory.ob C) → isProp (x ≡ y)) →
                isUnivalent C →
                isUnivalentAlt C
univalent→Alt' C propEq isUniv = isoEquivToUnivalentHelp (univEquiv isUniv) (λ x → (x , refl) , (λ z → ΣPathP ((snd z) , (isProp→PathP (λ i → propEq x (snd z i)) refl (snd z)))))

univalent→Alt : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                isUnivalent C →
                isUnivalentAlt C
univalent→Alt C isUniv = isoEquivToUnivalent (univEquiv isUniv)

isContr→EquivFun : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → isContr A → isContr B → (f : A → B) → isEquiv f
isContr→EquivFun isContrA isContrB f = equivIsEquiv (isoToEquiv (
  iso f (λ b → fst isContrA) (λ z → isContr→isProp isContrB (f (fst isContrA)) z) (snd isContrA)))

univalentAlt→' : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                isUnivalentAlt C →
                isUnivalent C
univalentAlt→' C isUnivAlt =
  record {univ = λ x → fiberEquiv (λ y → x ≡ y) (λ y → CatIso {C = C} x y) (pathToIso x) (
                                  isContr→EquivFun (isContrSingl x) (isUnivalentAlt.univ isUnivAlt x) (total x)) }
  where
    total : (x : ob C) → singl x → Σ (ob C) (CatIso x)
    total x = (\ p → p .fst , pathToIso x (p .fst) (p .snd))

univalentAlt→ : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                isUnivalentAlt C →
                isUnivalent C
univalentAlt→ C isUnivAlt = record {univ = λ x y → isContrToUniv CatIso (pathToIso _ _) (isUnivalentAlt.univ isUnivAlt)}

--                                  (record {equiv-proof = λ y → {!!}})}

--univalentAlt→isProp : {ℓ : Level} → (C : Precategory ℓ ℓ) →
--                     isUnivalentAlt C →
--                     (x y : Precategory.ob C) → isProp (CatIso {C = C} x y)
--univalentAlt→isProp C isUniv x y p q = (sym (snd (PathPΣ (snd (isUnivalentAlt.univ isUniv x) (y , p))))) ∙ {!!}
--snd (PathPΣ (snd (isUnivalentAlt.univ isUniv x) (x , idCatIso x)))

--univalentAlt→ : {ℓ : Level} → (C : Precategory ℓ ℓ) →
--                ((x y : Precategory.ob C) → isProp (x ≡ y)) →
--                isUnivalentAlt C →
--                isUnivalent C
--univalentAlt→ C propEq isUniv = {!!}
