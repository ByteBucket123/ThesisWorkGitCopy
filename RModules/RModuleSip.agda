{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModuleSip where

open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
--open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.Module.Base
--open import Cubical.Algebra.Ring
open import Cubical.Foundations.Structure
open import ThesisWork.RModules.CommutativeRing
--open import Cubical.Foundations.Isomorphism
--open import Cubical.Foundations.Equiv
open import ThesisWork.SetSigmaType
open import Cubical.Data.Sigma.Base

open import Cubical.Algebra.AbGroup

open import Cubical.Foundations.SIP
open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro

module ModuleΣTheory {ℓ : Level} (R : CommutativeRing {ℓ}) where
  RawRModuleStructure = λ (M : Type ℓ) → (M → M → M) × (⟨ R ⟩ → M → M)

  RawRModuleEquivStr = AutoEquivStr RawRModuleStructure

  RawRModuleUnivalentStr : UnivalentStr _ RawRModuleEquivStr
  RawRModuleUnivalentStr = autoUnivalentStr RawRModuleStructure

  RModuleAxioms : (M : Type ℓ) (s : RawRModuleStructure M) → Type ℓ
  RModuleAxioms M (_+_ , _·_) = LeftModuleΣTheory.LeftModuleAxioms (CommutativeRing→Ring R) M (_+_ , _·_)

  RModuleStructure : Type ℓ → Type ℓ
  RModuleStructure = AxiomsStructure RawRModuleStructure RModuleAxioms

  RModuleΣ : Type (ℓ-suc ℓ)
  RModuleΣ = TypeWithStr ℓ RModuleStructure

  RModuleEquivStr : StrEquiv RModuleStructure ℓ
  RModuleEquivStr = AxiomsEquivStr RawRModuleEquivStr RModuleAxioms



  isSetRModuleΣ : (M : RModuleΣ)  → isSet (typ M)
  isSetRModuleΣ (M , snd) = LeftModuleΣTheory.isSetLeftModuleΣ (CommutativeRing→Ring R) (M , snd)

  isPropRModuleAxioms : (M : Type ℓ) (s : RawRModuleStructure M) → isProp (RModuleAxioms M s)
  isPropRModuleAxioms M (_+_ , _·_) = LeftModuleΣTheory.isPropLeftModuleAxioms (CommutativeRing→Ring R) M (_+_ , _·_)


  RModuleUnivalentStr : UnivalentStr RModuleStructure RModuleEquivStr
  RModuleUnivalentStr = axiomsUnivalentStr _ isPropRModuleAxioms RawRModuleUnivalentStr

  isSetRModuleStructure : (M : RModuleΣ) → isSet (RModuleStructure (typ M))
  isSetRModuleStructure M = isSetΣ
                            (isSetΣ (λ N K → liftFunExt λ Nx Kx → liftFunExt (isSetRModuleΣ M)) λ _ → λ N K → liftFunExt (λ Nr Kr → liftFunExt (isSetRModuleΣ M)))
                            (λ s → isProp→isSet (isPropRModuleAxioms (typ M) s))

--  isSetRModuleΣLift : isSet RModuleΣ
--  isSetRModuleΣLift M N p q = isSetΣ {!!} (λ K → isSetRModuleStructure {!M!})                              
--                              {!!} {!!} {!!} {!!}

-- module LeftModuleΣTheory (R : Ring {ℓ}) where

--   RawLeftModuleStructure = λ (M : Type ℓ) → (M → M → M) × (⟨ R ⟩ → M → M)

--   RawLeftModuleEquivStr = AutoEquivStr RawLeftModuleStructure

--   rawLeftModuleUnivalentStr : UnivalentStr _ RawLeftModuleEquivStr
--   rawLeftModuleUnivalentStr = autoUnivalentStr RawLeftModuleStructure

--   open RingStr (snd R) using (_·_; 1r) renaming (_+_ to _+r_)

--   LeftModuleAxioms : (M : Type ℓ) (s : RawLeftModuleStructure M) → Type ℓ
--   LeftModuleAxioms M (_+_ , _⋆_) = AbGroupΣTheory.AbGroupAxioms M _+_
--                                     × ((r s : ⟨ R ⟩) (x : M) → (r · s) ⋆ x ≡ r ⋆ (s ⋆ x))
--                                     × ((r s : ⟨ R ⟩) (x : M) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
--                                     × ((r : ⟨ R ⟩) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
--                                     × ((x : M) → 1r ⋆ x ≡ x)

--   LeftModuleStructure : Type ℓ → Type ℓ
--   LeftModuleStructure = AxiomsStructure RawLeftModuleStructure LeftModuleAxioms

--   LeftModuleΣ : Type (ℓ-suc ℓ)
--   LeftModuleΣ = TypeWithStr ℓ LeftModuleStructure

--   LeftModuleEquivStr : StrEquiv LeftModuleStructure ℓ
--   LeftModuleEquivStr = AxiomsEquivStr RawLeftModuleEquivStr LeftModuleAxioms

--   open AbGroupΣTheory using (isSetAbGroupΣ)

--   isSetLeftModuleΣ : (M : LeftModuleΣ)  → isSet _
--   isSetLeftModuleΣ (M , (_+_ , _) , (isAbGroup-M , _)) = isSetAbGroupΣ (M , _+_ , isAbGroup-M)

--   isPropLeftModuleAxioms : (M : Type ℓ) (s : RawLeftModuleStructure M)
--                              → isProp (LeftModuleAxioms M s)
--   isPropLeftModuleAxioms M (_+_ , _⋆_) =
--      isPropΣ (AbGroupΣTheory.isPropAbGroupAxioms M _+_)
--              λ isAbGroup-M →
--              isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
--             (isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
--             (isProp× (isPropΠ3 λ _ _ _ → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)
--                      (isPropΠ  λ _     → (isSetAbGroupΣ (M , _+_ , isAbGroup-M)) _ _)))

--   LeftModule→LeftModuleΣ : LeftModule R → LeftModuleΣ
--   LeftModule→LeftModuleΣ
--     (leftmodule M 0m _+_ -_ _⋆_ (ismodule +-isAbGroup ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid)) =
--     M , (_+_ , _⋆_) ,
--     AbGroupΣTheory.AbGroup→AbGroupΣ (_ , abgroupstr _ _ _ +-isAbGroup) .snd .snd ,
--     ⋆-assoc , ⋆-ldist , ⋆-rdist , ⋆-lid

--   LeftModuleΣ→LeftModule : LeftModuleΣ → LeftModule R
--   LeftModuleΣ→LeftModule (M , (_+_ , _⋆_) , isAbGroup-M , ⋆-assoc , ⋆-ldist , ⋆-rdist , ⋆-lid) =
--     let isAbGroup = AbGroupΣTheory.AbGroupΣ→AbGroup (_ , _ , isAbGroup-M ) .snd .AbGroupStr.isAbGroup
--     in leftmodule M _ _+_ _ _⋆_
--        (ismodule isAbGroup ⋆-assoc ⋆-ldist ⋆-rdist ⋆-lid)

--   LeftModuleIsoLeftModuleΣ : Iso (LeftModule R) LeftModuleΣ
--   LeftModuleIsoLeftModuleΣ = iso LeftModule→LeftModuleΣ LeftModuleΣ→LeftModule
--                                  (λ _ → refl) (λ _ → refl)

--   leftModuleUnivalentStr : UnivalentStr LeftModuleStructure LeftModuleEquivStr
--   leftModuleUnivalentStr = axiomsUnivalentStr _ isPropLeftModuleAxioms rawLeftModuleUnivalentStr

--   LeftModuleΣPath : (M N : LeftModuleΣ) → (M ≃[ LeftModuleEquivStr ] N) ≃ (M ≡ N)
--   LeftModuleΣPath = SIP leftModuleUnivalentStr

--   LeftModuleEquivStrΣ : (M N : LeftModule R) → Type ℓ
--   LeftModuleEquivStrΣ M N = LeftModule→LeftModuleΣ M ≃[ LeftModuleEquivStr ] LeftModule→LeftModuleΣ N

--   LeftModuleEquivStrΣPath : {M N : LeftModule R} → Iso (LeftModuleEquiv M N) (LeftModuleEquivStrΣ M N)
--   fun LeftModuleEquivStrΣPath (moduleiso e isHom+ comm⋆) = e , isHom+ , comm⋆
--   inv LeftModuleEquivStrΣPath (e , isHom+ , comm⋆) = moduleiso e isHom+ comm⋆
--   rightInv LeftModuleEquivStrΣPath _ = refl
--   leftInv LeftModuleEquivStrΣPath _ = refl

--   LeftModulePath : (M N : LeftModule R) → (LeftModuleEquiv M N) ≃ (M ≡ N)
--   LeftModulePath M N =
--     LeftModuleEquiv M N                                    ≃⟨ isoToEquiv LeftModuleEquivStrΣPath ⟩
--     LeftModuleEquivStrΣ M N                                   ≃⟨ LeftModuleΣPath _ _ ⟩
--     LeftModule→LeftModuleΣ M ≡ LeftModule→LeftModuleΣ N  ≃⟨ isoToEquiv
--                                                              (invIso
--                                                              (congIso
--                                                              LeftModuleIsoLeftModuleΣ))
--                                                            ⟩
--     M ≡ N ■

-- LeftModulePath : {R : Ring {ℓ}} (M N : LeftModule R) → (LeftModuleEquiv M N) ≃ (M ≡ N)
-- LeftModulePath {ℓ} {R} = LeftModuleΣTheory.LeftModulePath R

