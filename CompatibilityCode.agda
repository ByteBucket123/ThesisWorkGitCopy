{-# OPTIONS --cubical #-}

module ThesisWork.CompatibilityCode where

--Remake of the old category theory cod for compatibility reasons
open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' : Level

-- Precategories

record Precategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- no-eta-equality ; NOTE: need eta equality for `opop`
  field
    ob : Type ℓ
    hom : ob → ob → Type ℓ'
    idn : ∀ x → hom x x
    seq : ∀ {x y z} (f : hom x y ) (g : hom y z) → hom x z
    -- TODO: change these to implicit argument
    seq-λ : ∀ {x y : ob} (f : hom x y) → seq (idn x) f ≡ f
    seq-ρ : ∀ {x y} (f : hom x y) → seq f (idn y) ≡ f
    seq-α : ∀ {u v w x} (f : hom u v) (g : hom v w) (h : hom w x) → seq (seq f g) h ≡ seq f (seq g h)

open Precategory

-- Categories

record isCategory (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    homIsSet : ∀ {x y} → isSet (hom C x y)

-- Isomorphisms and paths in precategories

record CatIso {C : Precategory ℓ ℓ'} (x y : C .Precategory.ob) : Type ℓ' where
  constructor catiso
  field
    h : hom C x y
    h⁻¹ : hom C y x
    sec : seq C h⁻¹ h ≡ C .idn y
    ret : seq C h h⁻¹ ≡ C .idn x


pathToIso : {C : Precategory ℓ ℓ'} (x y : C .ob) (p : x ≡ y) → CatIso {C = C} x y
pathToIso {C = C} x y p = J (λ z _ → CatIso x z) (catiso idx idx (C .seq-λ idx) (C .seq-ρ idx)) p
  where
    idx = C .idn x

-- Univalent Categories

record isUnivalent (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x y : C .ob) → isEquiv (pathToIso {C = C} x y)

  -- package up the univalence equivalence
  univEquiv : ∀ (x y : C .ob) → (x ≡ y) ≃ (CatIso x y)
  univEquiv x y = (pathToIso {C = C} x y) , (univ x y)

open isUnivalent public

record isUnivalentAlt (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x : C .ob) → isContr (Σ (C .ob) (λ y → CatIso {C = C} x y))

isoEquivToUnivalent : {ℓ : Level} → {C : Precategory ℓ ℓ} → ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) → ((x : C .ob) → isContr (Σ (C .ob) (λ y →  x ≡ y))) →  isUnivalentAlt C
isoEquivToUnivalent {C = C} isocat contrEq = record{ univ = λ x → transport (cong (λ x → isContr (Σ (C .ob) x)) (funExt (λ y → ua (isocat x y)))) (contrEq x) }

-- Opposite Categories

_^op : Precategory ℓ ℓ' → Precategory ℓ ℓ'
(C ^op) .ob = C .ob
(C ^op) .hom x y = C .hom y x
(C ^op) .idn = C .idn
(C ^op) .seq f g = C .seq g f
(C ^op) .seq-λ = C .seq-ρ
(C ^op) .seq-ρ = C .seq-λ
(C ^op) .seq-α f g h = sym (C .seq-α _ _ _)

open isCategory public
