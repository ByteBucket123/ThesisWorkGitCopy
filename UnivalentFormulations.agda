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
open import ThesisWork.HelpFunctions
open import Cubical.Data.Sigma.Properties

-- ob = Precategory.ob

-- --Alternative definition of univalent category.

-- record isUnivalentAlt {ℓ ℓ' : Level} (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
--   field
--     univ : (x : ob C) → isContr (Σ (ob C) (λ y → CatIso {C = C} x y))

-- isoEquivToUnivalent : {ℓ : Level} → {C : Precategory ℓ ℓ} → ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) → ((x : ob C) → isContr (Σ (ob C) (λ y →  x ≡ y))) →  isUnivalentAlt C
-- isoEquivToUnivalent {C = C} isocat contrEq = record{ univ = λ x → transport (cong (λ x → isContr (Σ (ob C) x)) (funExt (λ y → ua (isocat x y)))) (contrEq x) }

-- --************************************************************* Help Theorems ******************************************************************************************

-- idCatIso : {ℓ ℓ' : Level} → {C : Precategory ℓ ℓ'} → (x : Precategory.ob C) → CatIso {C = C} x x
-- idCatIso {C = C} x = catiso (Precategory.idn C x) (Precategory.idn C x) (Precategory.seq-λ C (Precategory.idn C x)) (Precategory.seq-ρ C (Precategory.idn C x))


-- --PathPΣ2 : {ℓ ℓ' : Level} {A : Type ℓ} {B : (i : I) → A → Type ℓ'} {x : Σ A (B i0)} {y : Σ A (B i1)} → {eqFst : (fst x) ≡ (fst y)} →  (eq : PathP (λ i → Σ ? (B i)) x y) → PathP (λ i → B i (eqFst i)) (snd x) (snd y)
-- --PathPΣ2 eq same i = snd (eq i)

-- --************************************************************* *******************************************************************************************

-- makeUnivalentFromSet : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') →
--                        ((x y : Precategory.ob C) → isProp (x ≡ y)) →
--                        ((x y : Precategory.ob C) → isProp (CatIso {C = C} x y)) →
--                        ((x y : Precategory.ob C) → CatIso {C = C} x y → x ≡ y) →
--                        isUnivalent C
-- makeUnivalentFromSet C propEq propCatIso catIso→Eq = record {univ = λ x y → equivIsEquiv (isoToEquiv
--   (record {fun = pathToIso x y ;
--            inv = catIso→Eq x y ;
--            leftInv = λ z → propEq x y (catIso→Eq x y (pathToIso x y z)) z ;
--            rightInv = λ z → propCatIso x y (pathToIso x y (catIso→Eq x y z)) z }))}

-- univalent→Alt : {ℓ : Level} → (C : Precategory ℓ ℓ) →
--                 ((x y : Precategory.ob C) → isProp (x ≡ y)) →
--                 isUnivalent C →
--                 isUnivalentAlt C
-- univalent→Alt C propEq isUniv = isoEquivToUnivalent (univEquiv isUniv) (λ x → (x , refl) , (λ z → Σ≡ (snd z) (isProp→PathP (λ i → propEq x (snd z i)) refl (snd z))))

-- univalentAlt→isProp : {ℓ : Level} → (C : Precategory ℓ ℓ) →
--                      isUnivalentAlt C →
--                      (x y : Precategory.ob C) → isProp (CatIso {C = C} x y)
-- univalentAlt→isProp C isUniv x y p q = (sym (snd (PathPΣ (snd (isUnivalentAlt.univ isUniv x) (y , p))))) ∙ {!!}
-- --snd (PathPΣ (snd (isUnivalentAlt.univ isUniv x) (x , idCatIso x)))

-- univalentAlt→ : {ℓ : Level} → (C : Precategory ℓ ℓ) →
--                 ((x y : Precategory.ob C) → isProp (x ≡ y)) →
--                 isUnivalentAlt C →
--                 isUnivalent C
-- univalentAlt→ C propEq isUniv = {!!}
