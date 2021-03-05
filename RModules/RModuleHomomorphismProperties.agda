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

--******************************************************* Module Properties *********************************************************************
--These should also be moved.

ModuleSubPresZero : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (Module.- M) (Module.0m M) ≡ Module.0m M
ModuleSubPresZero {M = M} =
  (-M 0M)         ≡⟨ sym (ModuleZeroLeft {M = M} (-M 0M)) ⟩
  (0M +M (-M 0M)) ≡⟨ ModuleInvRight {M = M} 0M ⟩
  0M ∎
    where
      0M = Module.0m M
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      -M_ : ⟨ M ⟩M  → ⟨ M ⟩M
      -M x = (Module.- M) x

ModuleMulPresZero : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → (r : ⟨ R ⟩) → (M Module.⋆ r) (Module.0m M) ≡ Module.0m M
ModuleMulPresZero {R = R} {M = M} r =
  (r ⋆M 0M)                                    ≡⟨ sym (ModuleZeroRight {M = M} (r ⋆M 0M)) ⟩
  ((r ⋆M 0M) +M 0M)                            ≡⟨ cong (λ x → (r ⋆M 0M) +M x) (sym (ModuleInvRight {M = M} (r ⋆M 0M))) ⟩
  ((r ⋆M 0M) +M ((r ⋆M 0M) +M (-M (r ⋆M 0M)))) ≡⟨ Module+Isasso {M = M} (r ⋆M 0M) (r ⋆M 0M) (-M (r ⋆M 0M)) ⟩
  (((r ⋆M 0M) +M (r ⋆M 0M)) +M (-M (r ⋆M 0M))) ≡⟨ cong (λ x → x +M (-M (r ⋆M 0M))) (sym (ModuleRDist {M = M} r 0M 0M)) ⟩
  (((r ⋆M (0M +M 0M)) +M (-M (r ⋆M 0M))))      ≡⟨ cong (λ x → (r ⋆M x) +M (-M (r ⋆M 0M))) (ModuleZeroRight {M = M} 0M) ⟩
  (((r ⋆M 0M) +M (-M (r ⋆M 0M))))              ≡⟨ ModuleInvRight {M = M} (r ⋆M 0M) ⟩
  0M ∎
    where
      0M = Module.0m M
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M  → ⟨ M ⟩M
      r ⋆M x = (M Module.⋆ r) x
      -M_ : ⟨ M ⟩M  → ⟨ M ⟩M
      -M x = (Module.- M) x
     
      x≡x+M0 : (x : ⟨ M ⟩M ) → x ≡ x +M 0M
      x≡x+M0 x = sym (ModuleZeroRight {M = M} x)


--******************************************************** Homo properties ***********************************************************************

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
      x≡x+N0 x = sym (ModuleZeroRight {M = N} x)

      x≡x+M0 : (x : ⟨ M ⟩M ) → x ≡ x +M 0M
      x≡x+M0 x = sym (ModuleZeroRight {M = M} x)

      x+-Nx≡0 : (x : ⟨ N ⟩M ) → x +N (-N x) ≡ 0N
      x+-Nx≡0 x = ModuleInvRight {M = N} x

      assoN : (x y z : ⟨ N ⟩M) → x +N (y +N z) ≡ (x +N y) +N z
      assoN = Module+Isasso {M = N}

ModuleHomomorphismAddHomZero : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N K : Module R} → (m : ⟨ M ⟩M) → (h : ModuleHomomorphism R M K) → (k : ModuleHomomorphism R N K) → 
                               (K Module.+ (ModuleHomomorphism.h h m)) (ModuleHomomorphism.h k (Module.0m N)) ≡ (ModuleHomomorphism.h h) m
ModuleHomomorphismAddHomZero {N = N} {K = K} m h k =
  (f m +K g 0N) ≡⟨ cong (λ u → f m +K u) (ModuleHomomorphismPreserveZero k) ⟩
  (f m +K 0K)   ≡⟨ x+K0≡x (f m) ⟩
  f m ∎
    where
      f = ModuleHomomorphism.h h
      g = ModuleHomomorphism.h k
      0N = Module.0m N
      0K = Module.0m K
      _+K_ : ⟨ K ⟩M → ⟨ K ⟩M  → ⟨ K ⟩M
      x +K y = (K Module.+ x) y
      x+K0≡x : (x : ⟨ K ⟩M ) → x +K 0K ≡ x
      x+K0≡x x = ModuleZeroRight {M = K} x
      
ModuleHomomorphismAddHomZeroSym : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N K : Module R} → (n : ⟨ N ⟩M) → (h : ModuleHomomorphism R M K) → (k : ModuleHomomorphism R N K) → 
                               (K Module.+ (ModuleHomomorphism.h h (Module.0m M))) (ModuleHomomorphism.h k n) ≡ (ModuleHomomorphism.h k) n
ModuleHomomorphismAddHomZeroSym {M = M} {K = K} n h k =
  ((f 0M) +K (g n)) ≡⟨ +KAb (f 0M) (g n) ⟩
  ((g n) +K (f 0M)) ≡⟨ ModuleHomomorphismAddHomZero n k h ⟩
  g n ∎
    where
      f = ModuleHomomorphism.h h
      g = ModuleHomomorphism.h k
      0M = Module.0m M
      0K = Module.0m K
      _+K_ : ⟨ K ⟩M → ⟨ K ⟩M  → ⟨ K ⟩M
      x +K y = (K Module.+ x) y
      +KAb : (x y : ⟨ K ⟩M) → x +K y ≡ y +K x
      +KAb = ModuleIsAb {M = K}

ModuleHomomorphismLinSub : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (m : ⟨ M ⟩M) → (h : ModuleHomomorphism R M N) →
                           ModuleHomomorphism.h h ((Module.- M) m) ≡ (Module.- N) (ModuleHomomorphism.h h m)
ModuleHomomorphismLinSub {M = M} {N = N} m h =
  f (-M m)                              ≡⟨ sym (x+N0≡x (f (-M m))) ⟩
  ((f (-M m)) +N 0N)                    ≡⟨ cong (λ x → (f (-M m)) +N x) (sym (x+-Nx≡0 (f m))) ⟩
  ((f (-M m)) +N ((f m) +N (-N (f m)))) ≡⟨ assoN (f (-M m)) (f m) (-N (f m)) ⟩
  ((f (-M m) +N (f m)) +N (-N (f m)))   ≡⟨ cong (λ x → x +N (-N (f m))) (sym (ModuleHomomorphism.linear h (-M m) m)) ⟩
  (f ((-M m) +M m) +N (-N (f m)))       ≡⟨ cong (λ x → f x +N (-N (f m))) (-Mx+x≡0 m) ⟩
  (f 0M +N (-N (f m)))                  ≡⟨ cong (λ x → x +N (-N (f m))) (ModuleHomomorphismPreserveZero h) ⟩
  (0N +N (-N (f m)))                    ≡⟨ ModuleZeroLeft {M = N} (-N (f m)) ⟩
  (-N (f m)) ∎
    where
      f = ModuleHomomorphism.h h
      0M = Module.0m M
      0N = Module.0m N
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _+N_ : ⟨ N ⟩M → ⟨ N ⟩M  → ⟨ N ⟩M
      x +N y = (N Module.+ x) y
      -M_ : ⟨ M ⟩M → ⟨ M ⟩M
      -M x = (Module.- M) x
      -N_ : ⟨ N ⟩M → ⟨ N ⟩M
      -N x = (Module.- N) x
      x+N0≡x : (x : ⟨ N ⟩M ) → x +N 0N ≡ x
      x+N0≡x x = ModuleZeroRight {M = N} x
      x+-Nx≡0 : (x : ⟨ N ⟩M ) → x +N (-N x) ≡ 0N
      x+-Nx≡0 x = ModuleInvRight {M = N} x
      -Mx+x≡0 : (x : ⟨ M ⟩M ) → (-M x) +M x ≡ 0M
      -Mx+x≡0 x = ModuleInvLeft {M = M} x
      assoN : (x y z : ⟨ N ⟩M) → x +N (y +N z) ≡ (x +N y) +N z
      assoN = Module+Isasso {M = N}
      

