{-# OPTIONS --cubical #-}

module ThesisWork.RProj.ProjModule where

open import Cubical.Foundations.Prelude
open import ThesisWork.RModules.CommutativeRing
open import ThesisWork.RModules.RModule
open import Cubical.Foundations.Structure
open import ThesisWork.RProj.Projective
open import ThesisWork.RProj.FinitelyGeneratedModule
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation.Properties

--isProjectiveModule : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (P : Module R) → Type (ℓ-suc ℓ)
--isProjectiveModule R P = {E X : Module R} → (f : ModuleHomomorphism R P X) →
--                         (e : ModuleHomomorphism R E X) → homIsSurj e →
--                         isContr (ModuleHomomorphism R P E)

record IsProjModule {ℓ : Level} (R : CommutativeRing {ℓ}) {M : Type ℓ}
              (0m : M)
              (_+_ : M → M → M)
              (-_ : M → M)
              (_⋆_ : ⟨ R ⟩ → M → M) : Type (ℓ-suc ℓ) where
  constructor isProjModule
  field
    isMod : IsModule R 0m _+_ -_ _⋆_
    isProjective : isProjectiveModule R (moduleConst M 0m _+_ -_ _⋆_ isMod)
    isFinGen : isFinitelyGenerated (moduleConst M 0m _+_ -_ _⋆_ isMod)
    

record ProjModule {ℓ : Level} (R : CommutativeRing {ℓ}) : Type (ℓ-suc ℓ) where
  constructor projModule
  field
    Carrier        : Type ℓ
    0m             : Carrier
    _+_            : Carrier → Carrier → Carrier
    -_             : Carrier → Carrier
    _⋆_            : ⟨ R ⟩ → Carrier → Carrier
    isProjMod   : IsProjModule R 0m _+_ -_ _⋆_


⟨_⟩PM : {ℓ : Level} {R : CommutativeRing {ℓ}} → ProjModule R → Type ℓ
⟨ x ⟩PM = ProjModule.Carrier x

ProjModule→Module : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : ProjModule R) → Module R
ProjModule→Module (projModule Carrier 0m _+_ -_ _⋆_ isProjMod) =
  moduleConst Carrier 0m _+_ -_ _⋆_ (IsProjModule.isMod isProjMod)

isSetProjModule : {ℓ : Level} {R : CommutativeRing {ℓ}} (P : ProjModule R) → isSet ⟨ P ⟩PM
isSetProjModule P = isSetModule (ProjModule→Module P)

Module→ProjModule : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → isProjectiveModule R M → isFinitelyGenerated M → ProjModule R
Module→ProjModule (moduleConst Carrier 0m _+_ -_ _⋆_ isMod) isProjM isFinGenM =
  projModule Carrier 0m _+_ -_ _⋆_ (isProjModule isMod isProjM isFinGenM)

getIsProj : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (P : ProjModule R) → isProjectiveModule R (ProjModule→Module P)
getIsProj (projModule Carrier 0m _+_ -_ _⋆_ (isProjModule isMod isProjective isFinGen)) = isProjective

getIsFinGen : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (P : ProjModule R) → isFinitelyGenerated (ProjModule→Module P)
getIsFinGen (projModule Carrier 0m _+_ -_ _⋆_ (isProjModule isMod isProjective isFinGen)) = isFinGen

--***************************************************************** Equiv ***************************************************************************

ModuleProjIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → Iso (ProjModule R) (Σ (Module R)  λ M → (isProjectiveModule R M) × (isFinitelyGenerated M))
ModuleProjIso = iso (λ P → (ProjModule→Module P) , ((IsProjModule.isProjective (ProjModule.isProjMod P)) , IsProjModule.isFinGen (ProjModule.isProjMod P)))
                    (λ (M , profM , finM) → Module→ProjModule M profM finM)
                    (λ z → refl)
                    λ z → refl 

isPropisProj : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → isProp (isProjectiveModule R M)
isPropisProj P p q = implicitFunExt (λ {E} → implicitFunExt (λ {X} → funExt (λ f → funExt (λ e → funExt (λ esurj → propTruncIsProp _ _)))))

--implicitFunExt (λ {E} → implicitFunExt (λ {X} → funExt (λ f → funExt (λ e → funExt (λ esurj → isPropIsContr _ _)))))

--inhProp→isContr

isContr→≡ : {ℓ : Level} → {A B : Type ℓ} → isContr A → isContr B → A ≡ B
isContr→≡ {A = A} {B} contrA contrB = ua (isoToEquiv (iso (λ a → fst contrB) (λ b → fst contrA) (snd contrB) (snd contrA)))

Prop→≡ : {ℓ : Level} → {A B : Type ℓ} → (x : A) → (y : B) → isProp A → isProp B → A ≡ B
Prop→≡ {A = A} {B} x y propA propB = ua (isoToEquiv (iso (λ a → y) (λ b → x) (λ z → propB y z) (λ z → propA x z)))

Prop→≡Ext : {ℓ : Level} → {A B : Type ℓ} → (x : A) → (y : B) → (pA : isProp A) → (pB : isProp B) → PathP (λ i → (Prop→≡ x y pA pB) i ) x y
Prop→≡Ext {A = A} {B} x y propA propB = toPathP (propB _ _)

ProjModule≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} →
              (p : ProjModule→Module P ≡ ProjModule→Module Q) → PathP (λ i → isProjectiveModule R (p i)) (getIsProj P) (getIsProj Q) -- (getIsProj P)  (getIsProj Q)
              → PathP (λ i → isFinitelyGenerated (p i)) (getIsFinGen P) (getIsFinGen Q) → P ≡ Q
ProjModule≡ p q r i = Module→ProjModule (p i) (q i) (r i)


Module≡→ProjModule≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} →
                      ProjModule→Module P ≡ ProjModule→Module Q → P ≡ Q
Module≡→ProjModule≡ {R = R} {P} {Q} p = ProjModule≡ p (toPathP (isPropisProj (ProjModule→Module Q) _ _)) (toPathP (FinGenIsProp (ProjModule→Module Q) _ _))
--  where
--    isProjP=isProjQ : isProjectiveModule R (ProjModule→Module P) ≡ isProjectiveModule R (ProjModule→Module Q)
--    isProjP=isProjQ = isProjectiveModule R (ProjModule→Module P) ≡⟨ cong (isProjectiveModule R) p ⟩
--                      isProjectiveModule R (ProjModule→Module Q) ∎
