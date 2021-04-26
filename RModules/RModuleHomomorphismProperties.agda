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
open import Cubical.Algebra.Ring.Base
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

--******************************************************* Ring Help *****************************************************************

Ring+Isasso : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (x y z : ⟨ R ⟩) →
              ((snd R) CommutativeRingStr.+ x) (((snd R) CommutativeRingStr.+ y) z) ≡
              ((snd R) CommutativeRingStr.+ (((snd R) CommutativeRingStr.+ x) y)) z
Ring+Isasso R x y z = IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (IsAbGroup.isGroup (IsRing.+-isAbGroup
                        (IsCommutativeRing.isRing (CommutativeRingStr.isCommutativeRing (snd R))))))) x y z

RingZeroRight : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (x : ⟨ R ⟩) →
                ((snd R) CommutativeRingStr.+ x) (CommutativeRingStr.0r (snd R)) ≡ x
RingZeroRight R x = fst (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (IsRing.+-isAbGroup (IsCommutativeRing.isRing
                      (CommutativeRingStr.isCommutativeRing (snd R)))))) x)

RingZeroLeft : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (x : ⟨ R ⟩) →
                ((snd R) CommutativeRingStr.+ (CommutativeRingStr.0r (snd R))) x ≡ x
RingZeroLeft R x = snd (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (IsRing.+-isAbGroup (IsCommutativeRing.isRing
                      (CommutativeRingStr.isCommutativeRing (snd R)))))) x)

RingInvRight : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (x : ⟨ R ⟩) →
                 ((snd R) CommutativeRingStr.+ x) ((CommutativeRingStr.- (snd R)) x) ≡ CommutativeRingStr.0r (snd R)
RingInvRight R x = fst (IsGroup.inverse (IsAbGroup.isGroup (IsRing.+-isAbGroup (IsCommutativeRing.isRing
                     (CommutativeRingStr.isCommutativeRing (snd R))))) x)

RingInvLeft : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (x : ⟨ R ⟩) →
              ((snd R) CommutativeRingStr.+ ((CommutativeRingStr.- (snd R)) x)) x ≡ CommutativeRingStr.0r (snd R)
RingInvLeft R x = snd (IsGroup.inverse (IsAbGroup.isGroup (IsRing.+-isAbGroup (IsCommutativeRing.isRing
                     (CommutativeRingStr.isCommutativeRing (snd R))))) x)

RingIsAb : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (x y : ⟨ R ⟩) →
           ((snd R) CommutativeRingStr.+ x) y ≡ ((snd R) CommutativeRingStr.+ y) x
RingIsAb R = IsAbGroup.comm (IsRing.+-isAbGroup (IsCommutativeRing.isRing (CommutativeRingStr.isCommutativeRing (snd R))))

Ring·Isasso : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (r s t : ⟨ R ⟩) →
              ((snd R) CommutativeRingStr.· r) (((snd R) CommutativeRingStr.· s) t) ≡
              ((snd R) CommutativeRingStr.· (((snd R) CommutativeRingStr.· r) s)) t
Ring·Isasso R = IsSemigroup.assoc (IsMonoid.isSemigroup (IsRing.·-isMonoid (IsCommutativeRing.isRing
                  (CommutativeRingStr.isCommutativeRing (snd R)))))

Ring·OneRight : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (r : ⟨ R ⟩) →
                ((snd R) CommutativeRingStr.· r) (CommutativeRingStr.1r (snd R)) ≡ r
Ring·OneRight R r = fst (IsMonoid.identity (IsRing.·-isMonoid (IsCommutativeRing.isRing
                      (CommutativeRingStr.isCommutativeRing (snd R)))) r)

Ring·OneLeft : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (r : ⟨ R ⟩) →
               ((snd R) CommutativeRingStr.· (CommutativeRingStr.1r (snd R))) r ≡ r
Ring·OneLeft R r = snd (IsMonoid.identity (IsRing.·-isMonoid (IsCommutativeRing.isRing
                      (CommutativeRingStr.isCommutativeRing (snd R)))) r)

Ring·DistRight : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (r s t : ⟨ R ⟩) →
                 ((snd R) CommutativeRingStr.· r) (((snd R) CommutativeRingStr.+ s) t) ≡
                 ((snd R) CommutativeRingStr.+ (((snd R) CommutativeRingStr.· r) s)) (((snd R) CommutativeRingStr.· r) t)
Ring·DistRight R r s t = fst (IsRing.dist (IsCommutativeRing.isRing (CommutativeRingStr.isCommutativeRing (snd R))) r s t)

Ring·DistLeft : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (r s t : ⟨ R ⟩) →
                ((snd R) CommutativeRingStr.· (((snd R) CommutativeRingStr.+ r) s)) t ≡
                ((snd R) CommutativeRingStr.+ (((snd R) CommutativeRingStr.· r) t)) (((snd R) CommutativeRingStr.· s) t)
Ring·DistLeft R r s t = snd ((IsRing.dist (IsCommutativeRing.isRing (CommutativeRingStr.isCommutativeRing (snd R))) r s t))


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

ModuleCommuteAsso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → (x y z v : ⟨ M ⟩M) →
                    (M Module.+ ((M Module.+ x) y)) ((M Module.+ z) v) ≡ (M Module.+ ((M Module.+ x) z)) ((M Module.+ y) v)
ModuleCommuteAsso {R = R} M x y z v =
  ((x +M y) +M (z +M v)) ≡⟨ sym (Module+Isasso {M = M} x y (z +M v)) ⟩
  (x +M (y +M (z +M v))) ≡⟨ cong (λ w → x +M w) (Module+Isasso {M = M} y z v) ⟩
  (x +M ((y +M z) +M v)) ≡⟨ cong (λ w → x +M (w +M v)) (ModuleIsAb {M = M} y z) ⟩
  (x +M ((z +M y) +M v)) ≡⟨ cong (λ w → x +M w) (sym (Module+Isasso {M = M} z y v)) ⟩
  (x +M (z +M (y +M v))) ≡⟨ Module+Isasso {M = M} x z (y +M v) ⟩
  ((x +M z) +M (y +M v)) ∎
    where
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      
ModuleInvDist : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → (x y : ⟨ M ⟩M) →
                  (Module.- M) ((M Module.+ x) y) ≡ (M Module.+ ((Module.- M) x)) ((Module.- M) y)
ModuleInvDist {R = R} M x y =
  (-M (x +M y))                                       ≡⟨ sym (ModuleZeroRight {M = M} (-M (x +M y))) ⟩
  ((-M (x +M y)) +M 0M)                               ≡⟨ cong (λ w → (-M (x +M y)) +M w) (sym (ModuleInvRight {M = M} x)) ⟩
  ((-M (x +M y)) +M (x +M (-M x)))                    ≡⟨ sym (ModuleZeroRight {M = M} ((-M (x +M y)) +M (x +M (-M x)))) ⟩
  (((-M (x +M y)) +M (x +M (-M x))) +M 0M)            ≡⟨ cong (λ w → ((-M (x +M y)) +M (x +M (-M x))) +M w)
                                                              (sym (ModuleInvRight {M = M} y)) ⟩
  (((-M (x +M y)) +M (x +M (-M x))) +M (y +M (-M y))) ≡⟨ sym (Module+Isasso {M = M} (-M (x +M y)) (x +M (-M x)) (y +M (-M y))) ⟩
  ((-M (x +M y)) +M ((x +M (-M x)) +M (y +M (-M y)))) ≡⟨ cong (λ w → (-M (x +M y)) +M w) (ModuleCommuteAsso M x (-M x) y (-M y)) ⟩
  ((-M (x +M y)) +M ((x +M y) +M ((-M x) +M (-M y)))) ≡⟨ Module+Isasso {M = M} (-M (x +M y)) (x +M y) ((-M x) +M (-M y)) ⟩
  (((-M (x +M y)) +M (x +M y)) +M ((-M x) +M (-M y))) ≡⟨ cong (λ w → w +M ((-M x) +M (-M y))) (ModuleInvLeft {M = M} (x +M y)) ⟩
  (0M +M ((-M x) +M (-M y)))                          ≡⟨ ModuleZeroLeft {M = M} ((-M x) +M (-M y)) ⟩
  ((-M x) +M (-M y)) ∎
    where
      0M = Module.0m M
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M  → ⟨ M ⟩M
      r ⋆M x = (M Module.⋆ r) x
      -M_ : ⟨ M ⟩M  → ⟨ M ⟩M
      -M x = (Module.- M) x

ModuleInvCommScalar : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → (r : ⟨ R ⟩) → (x : ⟨ M ⟩M) →
                      (Module.- M) ((M Module.⋆ r) x) ≡ (M Module.⋆ r) ((Module.- M) x)
ModuleInvCommScalar {R = R} M r x =
  (-M (r ⋆M x))                                  ≡⟨ sym (ModuleZeroRight {M = M} (-M (r ⋆M x))) ⟩
  ((-M (r ⋆M x)) +M 0M)                          ≡⟨ cong (λ w → (-M (r ⋆M x)) +M w) (sym (ModuleMulPresZero {M = M} r)) ⟩
  ((-M (r ⋆M x)) +M (r ⋆M 0M))                   ≡⟨ cong (λ w → (-M (r ⋆M x)) +M (r ⋆M w)) (sym (ModuleInvRight {M = M} x)) ⟩
  ((-M (r ⋆M x)) +M (r ⋆M (x +M (-M x))))        ≡⟨ cong (λ w → (-M (r ⋆M x)) +M w) (ModuleRDist {M = M} r x (-M x)) ⟩
  ((-M (r ⋆M x)) +M ((r ⋆M x) +M (r ⋆M (-M x)))) ≡⟨ Module+Isasso {M = M} (-M (r ⋆M x)) (r ⋆M x) (r ⋆M (-M x)) ⟩
  (((-M (r ⋆M x)) +M (r ⋆M x)) +M (r ⋆M (-M x))) ≡⟨ cong (λ w → w +M (r ⋆M (-M x))) (ModuleInvLeft {M = M} (r ⋆M x)) ⟩
  (0M +M (r ⋆M (-M x)))                          ≡⟨ ModuleZeroLeft {M = M} (r ⋆M (-M x)) ⟩
  (r ⋆M (-M x)) ∎
    where
      0M = Module.0m M
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M  → ⟨ M ⟩M
      r ⋆M x = (M Module.⋆ r) x
      -M_ : ⟨ M ⟩M  → ⟨ M ⟩M
      -M x = (Module.- M) x


--**************************************************** Ring Properties *****************************************************************

ModuleMulZeroRing : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → (m : ⟨ M ⟩M) →
                    (M Module.⋆ CommutativeRingStr.0r (snd R)) m ≡ Module.0m M
ModuleMulZeroRing {R = R} M m =
  (0R ⋆M m)                                    ≡⟨ sym (ModuleZeroRight {M = M} (0R ⋆M m)) ⟩
  ((0R ⋆M m) +M 0M)                            ≡⟨ cong (λ x → (0R ⋆M m) +M x) (sym (ModuleInvRight {M = M} (0R ⋆M m))) ⟩
  ((0R ⋆M m) +M ((0R ⋆M m) +M (-M (0R ⋆M m)))) ≡⟨ Module+Isasso {M = M} (0R ⋆M m) (0R ⋆M m) (-M (0R ⋆M m)) ⟩
  (((0R ⋆M m) +M (0R ⋆M m)) +M (-M (0R ⋆M m))) ≡⟨ cong (λ x → x +M (-M (0R ⋆M m))) (sym (ModuleLDist {M = M} 0R 0R m)) ⟩
  (((0R +R 0R) ⋆M m) +M (-M (0R ⋆M m)))        ≡⟨ cong (λ x → (x ⋆M m) +M (-M (0R ⋆M m))) (RingZeroRight R 0R) ⟩
  ((0R ⋆M m) +M (-M (0R ⋆M m)))                ≡⟨ ModuleInvRight {M = M} (0R ⋆M m) ⟩
  0M ∎
    where
      0M = Module.0m M
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M  → ⟨ M ⟩M
      a ⋆M b = (M Module.⋆ a) b
      -M_ : ⟨ M ⟩M  → ⟨ M ⟩M
      -M x = (Module.- M) x
      0R = CommutativeRingStr.0r (snd R)
      _+R_ : ⟨ R ⟩ → ⟨ R ⟩  → ⟨ R ⟩
      r +R s = ((snd R) CommutativeRingStr.+ r) s
      -R_ : ⟨ R ⟩  → ⟨ R ⟩
      -R s = (CommutativeRingStr.- (snd R)) s


ModuleSubMulRing : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → (m : ⟨ M ⟩M) → (r : ⟨ R ⟩) →
                    (M Module.⋆ (CommutativeRingStr.- (snd R)) r) m ≡ (Module.- M) ((M Module.⋆ r) m)
ModuleSubMulRing {R = R} M m r =
  ((-R r) ⋆M m)                                  ≡⟨ sym (ModuleZeroRight {M = M} ((-R r) ⋆M m)) ⟩
  (((-R r) ⋆M m) +M 0M)                          ≡⟨ cong (λ x → ((-R r) ⋆M m) +M x) (sym (ModuleInvRight {M = M} (r ⋆M m))) ⟩
  (((-R r) ⋆M m) +M ((r ⋆M m) +M (-M (r ⋆M m)))) ≡⟨ Module+Isasso {M = M} ((-R r) ⋆M m) (r ⋆M m) (-M (r ⋆M m)) ⟩
  ((((-R r) ⋆M m) +M (r ⋆M m)) +M (-M (r ⋆M m))) ≡⟨ cong (λ x → x +M (-M (r ⋆M m))) (sym (ModuleLDist {M = M} (-R r) r m)) ⟩
  ((((-R r) +R r) ⋆M m) +M (-M (r ⋆M m)))        ≡⟨ cong (λ x → (x ⋆M m) +M (-M (r ⋆M m))) (RingInvLeft R r) ⟩
  ((0R ⋆M m) +M (-M (r ⋆M m)))                   ≡⟨ cong (λ x → x +M (-M (r ⋆M m))) (ModuleMulZeroRing M m) ⟩
  (0M +M (-M (r ⋆M m)))                          ≡⟨ ModuleZeroLeft {M = M} (-M (r ⋆M m)) ⟩
  (-M (r ⋆M m)) ∎
 where
      0M = Module.0m M
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M  → ⟨ M ⟩M
      a ⋆M b = (M Module.⋆ a) b
      -M_ : ⟨ M ⟩M  → ⟨ M ⟩M
      -M x = (Module.- M) x
      0R = CommutativeRingStr.0r (snd R)
      _+R_ : ⟨ R ⟩ → ⟨ R ⟩  → ⟨ R ⟩
      r +R s = ((snd R) CommutativeRingStr.+ r) s
      -R_ : ⟨ R ⟩  → ⟨ R ⟩
      -R s = (CommutativeRingStr.- (snd R)) s


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
      
ModuleHomoInvIsHomo :  {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (f : ModuleHomomorphism R M N) →
                       (fInv : ⟨ N ⟩M → ⟨ M ⟩M) → ((λ x → ModuleHomomorphism.h f (fInv x)) ≡ λ x → x) →
                       ((λ x → fInv (ModuleHomomorphism.h f x)) ≡ λ x → x) → ModuleHomomorphism R N M
ModuleHomoInvIsHomo {R = R} M N f fInv ffInv=id fInvf=id =
  moduleHomo fInv
             (λ x y → fInv (x +N y)                         ≡⟨ (cong₂ (λ x y → fInv (x +N y)) (funExt⁻ (sym ffInv=id) x)
                                                                                              (funExt⁻ (sym ffInv=id) y)) ⟩
                      fInv ((f' (fInv x)) +N (f' (fInv y))) ≡⟨ cong fInv (sym (ModuleHomomorphism.linear f (fInv x) (fInv y))) ⟩
                      fInv (f' ((fInv x) +M (fInv y)))      ≡⟨ funExt⁻ fInvf=id ((fInv x) +M (fInv y)) ⟩
                      ((fInv x) +M (fInv y)) ∎)
             λ r x → fInv (r ⋆N x)             ≡⟨ cong (λ x → fInv (r ⋆N x)) (funExt⁻ (sym ffInv=id) x) ⟩
                     fInv (r ⋆N (f' (fInv x))) ≡⟨ cong fInv (sym (ModuleHomomorphism.scalar f r (fInv x))) ⟩
                     fInv (f' (r ⋆M (fInv x))) ≡⟨ funExt⁻ fInvf=id (r ⋆M (fInv x)) ⟩
                     (r ⋆M (fInv x)) ∎
    where
      f' = ModuleHomomorphism.h f
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M  → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _+N_ : ⟨ N ⟩M → ⟨ N ⟩M  → ⟨ N ⟩M
      x +N y = (N Module.+ x) y
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M  → ⟨ M ⟩M
      r ⋆M x = (M Module.⋆ r) x
      _⋆N_ : ⟨ R ⟩ → ⟨ N ⟩M  → ⟨ N ⟩M
      r ⋆N x = (N Module.⋆ r) x
