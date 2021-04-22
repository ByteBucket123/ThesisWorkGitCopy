{-# OPTIONS --cubical #-}

module ThesisWork.CompatibilityCode where

--Remake of the old category theory code for compatibility reasons
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

--***************************************************** SetTruncation ************************************************

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥; ∣_∣; squash)

truncRelIso : {ℓ : Level} → {A : Type ℓ} → {R : A → A → Type ℓ} → Iso (A / R) (A / (λ a b → ∥ R a b ∥))
Iso.fun truncRelIso = rec squash/ [_] λ _ _ r → eq/ _ _ ∣ r ∣
Iso.inv truncRelIso = rec squash/ [_] λ _ _ → PropTrunc.rec (squash/ _ _) λ r → eq/ _ _ r
Iso.rightInv truncRelIso = elimProp (λ _ → squash/ _ _) λ _ → refl
Iso.leftInv truncRelIso = elimProp (λ _ → squash/ _ _) λ _ → refl

truncRelEquiv : {ℓ : Level} → {A : Type ℓ} → {R : A → A → Type ℓ} → A / R ≃ A / (λ a b → ∥ R a b ∥)
truncRelEquiv = isoToEquiv truncRelIso


open import Cubical.Relation.Binary.Base
open BinaryRelation

isEquivRel→effectiveIso : {ℓ : Level} → {A : Type ℓ} → {R : A → A → Type ℓ} →
                          isPropValued R → isEquivRel R → (a b : A) → Iso ([ a ] ≡ [ b ]) (R a b)
Iso.fun (isEquivRel→effectiveIso {R = R} Rprop Req a b) = effective Rprop Req a b
Iso.inv (isEquivRel→effectiveIso {R = R} Rprop Req a b) = eq/ a b
Iso.rightInv (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = Rprop a b _ _
Iso.leftInv (isEquivRel→effectiveIso {R = R} Rprop Req a b) _ = squash/ _ _ _ _

isEquivRel→TruncIso : {ℓ : Level} → {A : Type ℓ} → {R : A → A → Type ℓ} → isEquivRel R → (a b : A) → Iso ([ a ] ≡ [ b ])  ∥ R a b ∥
isEquivRel→TruncIso {A = A} {R = R} Req a b =
  compIso (isProp→Iso (squash/ _ _) (squash/ _ _)
    (cong (Iso.fun truncRelIso)) (cong (Iso.inv truncRelIso)))
      (isEquivRel→effectiveIso  (λ _ _ → PropTrunc.propTruncIsProp) ∥R∥eq a b)
  where
    open isEquivRel
    ∥R∥eq : isEquivRel  λ a b → ∥ R a b ∥
    reflexive ∥R∥eq a = ∣ reflexive Req a ∣
    symmetric ∥R∥eq a b = PropTrunc.map (symmetric Req a b)
    transitive ∥R∥eq a b c = PropTrunc.map2 (transitive Req a b c)
