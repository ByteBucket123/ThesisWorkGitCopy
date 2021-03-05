{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModule where

--open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.Kernel
open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
open import ThesisWork.HelpFunctions
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.Module.Base
open import Cubical.Algebra.Ring
open import Cubical.Foundations.Structure
open import ThesisWork.RModules.CommutativeRing
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import ThesisWork.SetSigmaType

record IsModule {ℓ : Level} (R : CommutativeRing {ℓ}) {M : Type ℓ}
              (0m : M)
              (_+_ : M → M → M)
              (-_ : M → M)
              (_⋆_ : ⟨ R ⟩ → M → M) : Type ℓ where
  constructor isModule
  field
    isLeftModule : IsLeftModule (CommutativeRing→Ring R) 0m _+_ -_ _⋆_
    
record Module {ℓ : Level} (R : CommutativeRing {ℓ}) : Type (ℓ-suc ℓ) where

  constructor moduleConst

  field
    Carrier        : Type ℓ
    0m             : Carrier
    _+_            : Carrier → Carrier → Carrier
    -_             : Carrier → Carrier
    _⋆_            : ⟨ R ⟩ → Carrier → Carrier
    isMod   : IsModule R 0m _+_ -_ _⋆_

⟨_⟩M : {ℓ : Level} {R : CommutativeRing {ℓ}} → Module R → Type ℓ
⟨ x ⟩M = Module.Carrier x

Module→LeftModule : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → LeftModule (CommutativeRing→Ring R)
Module→LeftModule (moduleConst Carrier 0m _+_ -_ _⋆_ isLeftModule) =
  leftmodule Carrier 0m _+_ -_ _⋆_ (IsModule.isLeftModule isLeftModule)

isSetModule : {ℓ : Level} {R : CommutativeRing {ℓ}} (M : Module R) → isSet ⟨ M ⟩M
isSetModule M = isSetLeftModule (Module→LeftModule M)

LeftModule→Module : {ℓ : Level} → {R : CommutativeRing {ℓ}} → LeftModule (CommutativeRing→Ring R) → (Module R)
LeftModule→Module {R = R} (leftmodule Carrier 0m _+_ -_ _⋆_ isLeftModule) =
  moduleConst Carrier 0m _+_ -_ _⋆_ (isModule isLeftModule)

record ModuleEquiv {ℓ : Level} {R : CommutativeRing {ℓ}} (M N : Module R) : Type ℓ where
  constructor moduleIso
  field
    e : ⟨ M ⟩M ≃ ⟨ N ⟩M
    isHom+ : (x y : ⟨ M ⟩M) → (equivFun e) ((M Module.+ x) y) ≡ (N Module.+ (equivFun e x)) (equivFun e y)
    comm⋆ : (r : ⟨ R ⟩) (x : ⟨ M ⟩M) → (equivFun e ((M Module.⋆ r) x)) ≡ ((N Module.⋆ r) (equivFun e x))

--******************************************* Help Funcs ******************************************************

HelpIsHom : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (e : ⟨ M ⟩M ≃ ⟨ N ⟩M) → Type ℓ
HelpIsHom {M = M} {N = N} e = (x y : ⟨ M ⟩M) → (equivFun e) ((M Module.+ x) y) ≡ (N Module.+ (equivFun e x)) (equivFun e y)

HelpComm : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (e : ⟨ M ⟩M ≃ ⟨ N ⟩M) → Type ℓ
HelpComm {R = R} {M = M} {N = N} e = (r : ⟨ R ⟩) (x : ⟨ M ⟩M) → (equivFun e ((M Module.⋆ r) x)) ≡ ((N Module.⋆ r) (equivFun e x))

HelpModuleEquiv≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleEquiv M N}
               → (p : ModuleEquiv.e x ≡ ModuleEquiv.e y)
               → (λ i → HelpIsHom {M = M} {N = N} (p i)) [ ModuleEquiv.isHom+ x ≡ ModuleEquiv.isHom+ y ]
               → (λ i → HelpComm {M = M} {N = N} (p i)) [ ModuleEquiv.comm⋆ x ≡ ModuleEquiv.comm⋆ y ]
               → (x ≡ y)
HelpModuleEquiv≡ p q r = cong moduleIso p <*> q <*> r

ModuleEquivHom+IsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleEquiv M N}
                        → (p : ModuleEquiv.e x ≡ ModuleEquiv.e y)
                        → (λ i → HelpIsHom {M = M} {N = N} (p i)) [ ModuleEquiv.isHom+ x ≡ ModuleEquiv.isHom+ y ]
ModuleEquivHom+IsProp {M = M} {N = N} {x = homoH} {y = homoK} p = isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
  isSetModule N
  ((equivFun (p i)) ((M Module.+ x) y))
  ((N Module.+ (equivFun (p i) x)) (equivFun (p i) y))
  (t x y)
  (s x y)
  )))
  (ModuleEquiv.isHom+ homoH) (ModuleEquiv.isHom+ homoK)

ModuleEquivCommIsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleEquiv M N}
                        → (p : ModuleEquiv.e x ≡ ModuleEquiv.e y)
                        → (λ i → HelpComm {M = M} {N = N} (p i)) [ ModuleEquiv.comm⋆ x ≡ ModuleEquiv.comm⋆ y ]
ModuleEquivCommIsProp {M = M} {N = N} {x = homoH} {y = homoK} p = isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
  isSetModule N
  (equivFun (p i) ((M Module.⋆ r) x))
  (((N Module.⋆ r) (equivFun (p i) x)))
  (t r x)
  (s r x)
  )))
  (ModuleEquiv.comm⋆ homoH) (ModuleEquiv.comm⋆ homoK)

ModuleEquiv≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleEquiv M N}
               → (p : ModuleEquiv.e x ≡ ModuleEquiv.e y)
               → (x ≡ y)
ModuleEquiv≡ {x = x} {y = y} p =
  HelpModuleEquiv≡ p (ModuleEquivHom+IsProp {x = x} {y = y} p) (ModuleEquivCommIsProp {x = x} {y = y} p)


--******************************************* Univalence ******************************************************

ModuleEquiv→LeftModuleEquiv : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R}
                              → (ModuleEquiv M N) → (LeftModuleEquiv (Module→LeftModule M) (Module→LeftModule N))
ModuleEquiv→LeftModuleEquiv (moduleIso e isHom+ comm⋆) = moduleiso e isHom+ comm⋆

LeftModuleEquiv→ModuleEquiv : {ℓ : Level} → {R : CommutativeRing {ℓ}} →  {M N : Module R}
                              → (LeftModuleEquiv (Module→LeftModule M) (Module→LeftModule N)) → (ModuleEquiv M N)
LeftModuleEquiv→ModuleEquiv (moduleiso e isHom+ comm⋆) = moduleIso e isHom+ comm⋆

IsoModuleEquivLeftModuleEquiv : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R}
                    → Iso (ModuleEquiv M N) (LeftModuleEquiv (Module→LeftModule M) (Module→LeftModule N))
IsoModuleEquivLeftModuleEquiv = record {fun = ModuleEquiv→LeftModuleEquiv ;
                                        inv = LeftModuleEquiv→ModuleEquiv ;
                                        rightInv = λ z → refl ;
                                        leftInv = λ z → refl }

Module≃LeftModule : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R}
                    → (ModuleEquiv M N) ≃ (LeftModuleEquiv (Module→LeftModule M) (Module→LeftModule N))
Module≃LeftModule = isoToEquiv IsoModuleEquivLeftModuleEquiv

IsoModuleEquivLeftModuleEquivMap : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : LeftModule (CommutativeRing→Ring R)}
                    → Iso (ModuleEquiv {R = R} (LeftModule→Module M) (LeftModule→Module N)) (LeftModuleEquiv M N)
IsoModuleEquivLeftModuleEquivMap = record {fun = ModuleEquiv→LeftModuleEquiv ;
                                           inv = LeftModuleEquiv→ModuleEquiv ;
                                           rightInv = λ z → refl ;
                                           leftInv = λ z → refl }

Module≃LeftModuleMap : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : LeftModule (CommutativeRing→Ring R)}
                    → (ModuleEquiv {R = R} (LeftModule→Module M) (LeftModule→Module N)) ≃ (LeftModuleEquiv M N)
Module≃LeftModuleMap = isoToEquiv IsoModuleEquivLeftModuleEquivMap

Module→LeftModuleInj : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R}
                       → Iso (M ≡ N) (Module→LeftModule M ≡ Module→LeftModule N)
Module→LeftModuleInj = record {fun = λ p → λ i → Module→LeftModule (p i) ;
                               inv = λ p → λ i → LeftModule→Module (p i) ;
                               rightInv = λ z → refl ;
                               leftInv = λ z → refl }

Module≡LeftModule : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R}
                       → (M ≡ N) ≃ (Module→LeftModule M ≡ Module→LeftModule N)
Module≡LeftModule = isoToEquiv Module→LeftModuleInj

ModulePath : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R}
                       → (ModuleEquiv M N) ≃ (M ≡ N)
ModulePath {M = M} {N = N} = ModuleEquiv M N                                                      ≃⟨ Module≃LeftModule ⟩
                             LeftModuleEquiv (Module→LeftModule M) (Module→LeftModule N)          ≃⟨ LeftModulePath
                                                                                                     (Module→LeftModule M)
                                                                                                     (Module→LeftModule N) ⟩
                             Module→LeftModule M ≡ Module→LeftModule N                            ≃⟨ invEquiv Module≡LeftModule ⟩
                             (M ≡ N) ■

--******************************************************** Σ represenation ***************************************************************************************

ModuleΣ : {ℓ : Level} → (R : CommutativeRing {ℓ}) → Type (ℓ-suc ℓ)
ModuleΣ {ℓ} R =
  Σ (Type ℓ) λ Carrier →
  Σ Carrier (λ 0m →
  Σ (Carrier → Carrier → Carrier) (λ _+_ →
  Σ (Carrier → Carrier) (λ -_ →
  Σ (⟨ R ⟩ → Carrier → Carrier) (λ _⋆_ →
  IsModule R 0m _+_ -_ _⋆_))))

Module→ModuleΣ : {ℓ : Level} → (R : CommutativeRing {ℓ}) → Module R → ModuleΣ R
Module→ModuleΣ R (moduleConst Carrier 0m _+_ -_ _⋆_ isMod) = Carrier , (0m , (_+_ , (-_ , (_⋆_ , isMod))))

ModuleΣ→Module : {ℓ : Level} → (R : CommutativeRing {ℓ}) → ModuleΣ R → Module R
ModuleΣ→Module R (Carrier , 0m , _+_ , -_ , _⋆_ , isMod) = moduleConst Carrier 0m _+_ -_ _⋆_ isMod

ModuleΣIso : {ℓ : Level} → (R : CommutativeRing {ℓ}) → Iso (ModuleΣ R) (Module R)
ModuleΣIso R = record {fun = ModuleΣ→Module R ;
                       inv = Module→ModuleΣ R ;
                       rightInv = λ z → refl ;
                       leftInv = λ z → refl}

ModuleΣEq : {ℓ : Level} → (R : CommutativeRing {ℓ}) → ModuleΣ R ≃ Module R
ModuleΣEq R = isoToEquiv (ModuleΣIso R)

--isSetModuleΣ : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isSet (ModuleΣ R)
--isSetModuleΣ R M N p q i = isSetΣ {!!} (λ K →
--                           isSetΣ {!isSetModule M!} {!!}) M N p q i
