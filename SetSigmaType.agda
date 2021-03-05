{-# OPTIONS --cubical #-}

module ThesisWork.SetSigmaType where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Glue
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import Cubical.Foundations.Equiv
open import ThesisWork.CompatibilityCode
open import Cubical.Foundations.Equiv.Properties
open import ThesisWork.HelpFunctions
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

--This is a translation of a module in ctt. (TODO: Create ref.)

--****************************************************** isSetΣ ***************************************************************

substInv' : {ℓ ℓ' : Level} → (B : Type ℓ → Type ℓ') → (x y : Type ℓ) → (p : x ≡ y) → B y → B x
substInv' B x y p By = subst B (sym p) By

propSig : {ℓ ℓ' : Level} → (A : Type ℓ) → (B : A → Type ℓ') → isProp A → ((a : A) → isProp (B a))
          → isProp (Σ A B)
propSig A B pA pB t u = Σ≡ (pA (fst t) (fst u))
                           (isProp→PathP (λ i → λ r s →
                           pB (pA (fst t) (fst u) i) r s)
                           (snd t)
                           (snd u))

lemPathSig : {ℓ ℓ' : Level} → (A : Type ℓ) → (B : A → Type ℓ') → (t u : Σ A B) →
             (t ≡ u) ≡ Σ (fst t ≡ fst u) (λ p → PathP (λ i → B (p i)) (snd t) (snd u))
lemPathSig A B t u = isoToPath (iso f g s r)
    where
      T0 = Path (Σ A B) t u
      T1 = Σ (fst t ≡ fst u) (λ p → PathP (λ i → B (p i)) (snd t) (snd u))
      f : (q : T0) → T1
      f q = cong fst q , cong snd q
      g : (z : T1) → T0
      g z = λ i → (fst z i) , snd z i
      s : (z : T1) → f(g z) ≡ z
      s z = refl
      r : (q : T0) → g (f q) ≡ q
      r z = refl

funDepTr : {ℓ ℓ' : Level} → (A : Type ℓ) → (P : A → Type ℓ') → (a0 a1 : A) → (p : a0 ≡ a1) →
           (u0 : P a0) → (u1 : P a1) →
           PathP (λ i → P (p i)) u0 u1 ≡ Path (P a1) (transport (λ i → P (p i)) u0) u1
funDepTr A P a0 a1 p u0 u1 j = PathP (λ i → P (p (j ∨ i))) (transport-filler (λ i → P (p i)) u0 j) u1

lem2 : {ℓ ℓ' : Level} → (A : Type ℓ) → (B : A → Type ℓ') → (t u : Σ A B) → (p : fst t ≡ fst u) →
       PathP (λ i → B (p i)) (snd t) (snd u) ≡ Path (B (fst u)) (transport (cong B p) (snd t)) (snd u)
lem2 A B t u p = funDepTr A B (fst t) (fst u) p (snd t) (snd u)

corSigSet : {ℓ ℓ' : Level} → (A : Type ℓ) → (B : A → Type ℓ') → (sB : (a : A) → isSet (B a))
            → (t u : Σ A B) → (p : fst t ≡ fst u) → isProp (PathP (λ i → B (p i)) (snd t) (snd u))
corSigSet A B sB t u p = substInv' isProp T0 T1 rem rem1
  where
    P = λ i → B (p i) 
    T0 = PathP P (snd t) (snd u)
    T1 = Path (B (fst u)) (transport (cong B p) (snd t)) (snd u)
    rem : T0 ≡ T1
    rem = lem2 A B t u p
    v2 : B (fst u)
    v2 = transport (cong B p) (snd t)
    rem1 : isProp T1
    rem1 = sB (fst u) v2 (snd u)
    
isSetΣ : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → isSet A → ((a : A) → isSet (B a)) → isSet (Σ A B)
isSetΣ {ℓ} {ℓ'} {A} {B} sA sB t u =
  substInv' isProp (t ≡ u) (Σ T (λ p → C p)) rem3 rem2
    where
      T = fst t ≡ fst u
      C : (p : T) → Type ℓ'
      C p = PathP (λ i → B (p i)) (snd t) (snd u)
      rem : (p : T) → isProp (C p)
      rem = corSigSet A B sB t u
      rem1 : isProp T
      rem1 = sA (fst t) (fst u)
      rem2 : isProp (Σ T (λ p → C p))
      rem2 = propSig T C rem1 rem
      rem3 : (t ≡ u) ≡ Σ T (λ p → C p)
      rem3 = lemPathSig A B t u
