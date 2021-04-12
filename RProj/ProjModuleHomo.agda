{-# OPTIONS --cubical #-}

module ThesisWork.RProj.ProjModuleHomo where

open import Cubical.Foundations.Prelude
open import ThesisWork.RModules.CommutativeRing
open import ThesisWork.RModules.RModuleHomomorphism
open import ThesisWork.RProj.ProjModule
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

record ProjectiveModuleHomomorphism {ℓ : Level} (R : CommutativeRing {ℓ}) (P Q : ProjModule R) : Type ℓ where
  constructor projModuleHomo
  field
    h : ⟨ P ⟩PM → ⟨ Q ⟩PM
    linear : (x y : ⟨ P ⟩PM) → h ((P ProjModule.+ x) y) ≡ (Q ProjModule.+ (h x)) (h y)
    scalar : (r : ⟨ R ⟩) → (x : ⟨ P ⟩PM) → h ((P ProjModule.⋆ r) x) ≡ (Q ProjModule.⋆ r) (h x)

ProjModHom→ModHom : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → (ProjectiveModuleHomomorphism R P Q) → ModuleHomomorphism R (ProjModule→Module P) (ProjModule→Module Q)
ProjModHom→ModHom (projModuleHomo h linear scalar) = moduleHomo h linear scalar

ModHom→ProjModHom : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → (ModuleHomomorphism R (ProjModule→Module P) (ProjModule→Module Q)) → ProjectiveModuleHomomorphism R P Q
ModHom→ProjModHom (moduleHomo h linear scalar) = projModuleHomo h linear scalar


ProjModHomIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → Iso (ProjectiveModuleHomomorphism R P Q) (ModuleHomomorphism R (ProjModule→Module P) (ProjModule→Module Q))
ProjModHomIso = iso ProjModHom→ModHom ModHom→ProjModHom (λ z → refl) (λ z → refl)

ProjModHom≡ModHom : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → ProjectiveModuleHomomorphism R P Q ≡ ModuleHomomorphism R (ProjModule→Module P) (ProjModule→Module Q)
ProjModHom≡ModHom = ua (isoToEquiv ProjModHomIso)

ProjModuleHomo≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → {x y : ProjectiveModuleHomomorphism R P Q} → ProjectiveModuleHomomorphism.h x ≡ ProjectiveModuleHomomorphism.h y → x ≡ y
ProjModuleHomo≡ {x = x} {y} hx=hy i = ModHom→ProjModHom (ModuleHomo≡ {x = ProjModHom→ModHom x} {ProjModHom→ModHom y} hx=hy i)

--*********************************************************************************** HomoComp *************************************************************************************************

ProjModuleHomoComp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q K : ProjModule R} → ProjectiveModuleHomomorphism R P Q →
                     ProjectiveModuleHomomorphism R Q K → ProjectiveModuleHomomorphism R P K
ProjModuleHomoComp homoH homoK = ModHom→ProjModHom (ModuleHomoComp (ProjModHom→ModHom homoH) (ProjModHom→ModHom homoK))

ProjModuleHomoId : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P : ProjModule R} → ProjectiveModuleHomomorphism R P P
ProjModuleHomoId = ModHom→ProjModHom ModuleHomoId

ProjModuleHomoIdLeftComp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → (h : ProjectiveModuleHomomorphism R P Q) → 
                           ProjModuleHomoComp ProjModuleHomoId h ≡ h
ProjModuleHomoIdLeftComp h = ProjModuleHomo≡ refl

ProjModuleHomoIdRightComp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → (h : ProjectiveModuleHomomorphism R P Q) → 
                        ProjModuleHomoComp h ProjModuleHomoId ≡ h
ProjModuleHomoIdRightComp h = ProjModuleHomo≡ refl

ProjModuleHomoCompAsso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q K L : ProjModule R} → (h : ProjectiveModuleHomomorphism R P Q) →
                         (k : ProjectiveModuleHomomorphism R Q K) → (f : ProjectiveModuleHomomorphism R K L) →
                         ProjModuleHomoComp h (ProjModuleHomoComp k f) ≡ ProjModuleHomoComp (ProjModuleHomoComp h k) f
ProjModuleHomoCompAsso h k f = ProjModuleHomo≡ refl

isSetProjModuleHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {P Q : ProjModule R} → isSet (ProjectiveModuleHomomorphism R P Q)
isSetProjModuleHomo {P = P} {Q} = transport (cong isSet (sym ProjModHom≡ModHom)) (isSetModuleHomo (ProjModule→Module P) (ProjModule→Module Q))
