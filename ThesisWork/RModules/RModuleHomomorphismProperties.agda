{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModuleHomomorphismProperties where

--open import Cubical.Categories.Category
--open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
--open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
--open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
--open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
--open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
--open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
--open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
--open import ThesisWork.BasicCategoryTheory.Limits.Kernel
--open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
--open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
--open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
--open import ThesisWork.HelpFunctions
--open import Cubical.HITs.PropositionalTruncation
--open import Cubical.Algebra.Module.Base
--open import Cubical.Algebra.Ring
open import Cubical.Foundations.Structure
open import ThesisWork.RModules.CommutativeRing
open import ThesisWork.RModules.RModule
--open import Cubical.Foundations.Isomorphism
--open import Cubical.Foundations.Equiv
--open import Cubical.Foundations.Path
--open import Cubical.Foundations.Function
open import ThesisWork.RModules.RModuleHomomorphism
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Module.Base

ModuleHomomorphismPreserveZero : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ModuleHomomorphism R M N) →
                                 (ModuleHomomorphism.h h) (Module.0m M) ≡ (Module.0m N)
ModuleHomomorphismPreserveZero {M = M} {N = N} h =
  f 0M                                  ≡⟨ x≡x+N0 (f 0M) ⟩
  ((f 0M) +N 0N)                        ≡⟨ cong (λ x → (f 0M) +N x) (sym (x+-Nx≡0 (f 0M))) ⟩
  ((f 0M) +N ((f 0M) +N (-N (f 0M))))   ≡⟨ assoN (f 0M) (f 0M) (-N (f 0M)) ⟩
  (((f 0M) +N (f 0M)) +N (-N (f 0M)))   ≡⟨ cong (λ x → x +N (-N f 0M)) (sym (ModuleHomomorphism.linear h 0M 0M)) ⟩
  (((f (0M +M 0M)) +N (-N (f 0M))))     ≡⟨ cong (λ x → f x +N (-N f 0M)) (sym (x≡x+M0 0M)) ⟩
  ((f 0M) +N (-N (f 0M)))               ≡⟨ x+-Nx≡0 (f 0M) ⟩
  0N ∎ 
    where
      f = ModuleHomomorphism.h h
      0M = Module.0m M
      0N = Module.0m N
      _+N_ : ⟨ N ⟩M → ⟨ N ⟩M  → ⟨ N ⟩M
      x +N y = (N Module.+ x) y
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      -N_ : ⟨ N ⟩M  → ⟨ N ⟩M
      -N x = (Module.- N) x

      x≡x+N0 : (x : ⟨ N ⟩M ) → x ≡ x +N 0N
      x≡x+N0 x = sym (fst (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup
                   (IsModule.isLeftModule (Module.isMod N))))) x))

      x≡x+M0 : (x : ⟨ M ⟩M ) → x ≡ x +M 0M
      x≡x+M0 x = sym (fst (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup
                   (IsModule.isLeftModule (Module.isMod M))))) x))

      x+-Nx≡0 : (x : ⟨ N ⟩M ) → x +N (-N x) ≡ 0N
      x+-Nx≡0 x = fst (IsGroup.inverse (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup (IsModule.isLeftModule (Module.isMod N)))) x)

      assoN : (x y z : ⟨ N ⟩M) → x +N (y +N z) ≡ (x +N y) +N z
      assoN = IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup
              (IsModule.isLeftModule (Module.isMod N))))))

--********************************************** TODO : These should be moved **********************************************

Module+Isasso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (x y z : ⟨ M ⟩M) →
               (M Module.+ x) ((M Module.+ y) z) ≡ (M Module.+ ((M Module.+ x) y)) z
Module+Isasso {M = M} = IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup
                      (IsModule.isLeftModule (Module.isMod M))))))

ModuleZeroRight : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (x : ⟨ M ⟩M) → (M Module.+ x) (Module.0m M) ≡ x
ModuleZeroRight {M = M} x = (fst (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup
                            (IsModule.isLeftModule (Module.isMod M))))) x))

ModuleZeroLeft : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (x : ⟨ M ⟩M) → (M Module.+ (Module.0m M)) x ≡ x
ModuleZeroLeft {M = M} x = (snd (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup
                            (IsModule.isLeftModule (Module.isMod M))))) x))

ModuleInvRight : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (x : ⟨ M ⟩M) →
                 (M Module.+ x) ((Module.- M) x) ≡ Module.0m M
ModuleInvRight {M = M} x = fst (IsGroup.inverse (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup (IsModule.isLeftModule
                               (Module.isMod M)))) x)

ModuleInvLeft : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (x : ⟨ M ⟩M) →
                (M Module.+ (Module.- M) x) x ≡ Module.0m M
ModuleInvLeft {M = M} x = snd (IsGroup.inverse (IsAbGroup.isGroup (IsLeftModule.+-isAbGroup (IsModule.isLeftModule
                               (Module.isMod M)))) x)

ModuleIsAb : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (x y : ⟨ M ⟩M) →
                (M Module.+ x) y ≡ (M Module.+ y) x
ModuleIsAb {M = M} = IsAbGroup.comm (IsLeftModule.+-isAbGroup (IsModule.isLeftModule (Module.isMod M)))

Module·Isasso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (r s : ⟨ R ⟩) → (x : ⟨ M ⟩M) →
               (M Module.⋆ (((snd R) CommutativeRingStr.· r) s)) x  ≡ (M Module.⋆ r) ((M Module.⋆ s) x)
Module·Isasso {M = M} = IsLeftModule.⋆-assoc (IsModule.isLeftModule (Module.isMod M))

ModuleLDist : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (r s : ⟨ R ⟩) → (x : ⟨ M ⟩M) →
               ((M Module.⋆ ((snd R) CommutativeRingStr.+ r) s) x) ≡ (M Module.+ ((M Module.⋆ r) x)) ((M Module.⋆ s) x)
ModuleLDist {M = M} = IsLeftModule.⋆-ldist (IsModule.isLeftModule (Module.isMod M))

ModuleRDist : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (r : ⟨ R ⟩) → (x y : ⟨ M ⟩M) →
              ((M Module.⋆ r) ((M Module.+ x) y)) ≡ (M Module.+ ((M Module.⋆ r) x)) ((M Module.⋆ r) y)
ModuleRDist {M = M} = IsLeftModule.⋆-rdist (IsModule.isLeftModule (Module.isMod M))

ModuleLId : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (x : ⟨ M ⟩M) →
                 ((M Module.⋆ (CommutativeRingStr.1r (snd R))) x) ≡ x
ModuleLId {M = M} = IsLeftModule.⋆-lid (IsModule.isLeftModule (Module.isMod M))
