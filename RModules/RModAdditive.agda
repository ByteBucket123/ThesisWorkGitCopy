{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModAdditive where

open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
-- open import Cubical.Data.Sigma.Base
-- open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
-- open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
-- open import ThesisWork.BasicCategoryTheory.Limits.Kernel
-- open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import ThesisWork.RModules.CommutativeRing
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
-- open import Cubical.Algebra.Module.Base
open import ThesisWork.RModules.RModuleHomomorphism
open import ThesisWork.RModules.RModuleHomomorphismProperties
open import ThesisWork.RModules.RModule
open import ThesisWork.RModules.RMod
open import Cubical.Foundations.Structure
-- open import ThesisWork.CompatibilityCode
-- open import ThesisWork.SetSigmaType
-- open import Agda.Builtin.Cubical.HCompU
-- open import Cubical.Core.Primitives renaming (_[_≡_] to _[_≡_]P)

-- open import Cubical.HITs.SetQuotients.Base
-- open import Cubical.HITs.SetQuotients.Properties
-- open import Cubical.HITs.PropositionalTruncation.Base
-- open import ThesisWork.RModules.RModuleProperties
-- open import ThesisWork.SetQuotientHelp
-- open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
-- open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
-- open import Cubical.HITs.PropositionalTruncation.Properties renaming
--   (elim to elimHprop ;
--    elim2 to elim2Hprop ;
--    elim3 to elim3Hprop ;
--    rec to recHprop ;
--    rec2 to rec2Hprop )

-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Relation.Binary.Base
-- open import ThesisWork.RModules.MonicToInjective

open import ThesisWork.RModules.RModProperties
open import ThesisWork.AbelianCategory.AdditiveCategory

private
  0a : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ModuleHomomorphism R M N
  0a {R = R} M N = ZeroArrow.f (getZeroArrow (RMod {R = R}) (hasZeroObjectRMod R))

_+Hom_ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (f g : ModuleHomomorphism R M N) → ModuleHomomorphism R M N
_+Hom_ {R = R} {M} {N} f g =
  moduleHomo (λ x → (f' x) +N (g' x))
             (λ x y → ((f' (x +M y)) +N g' (x +M y))                ≡⟨ cong₂ _+N_ (ModuleHomomorphism.linear f x y)
                                                                                  (ModuleHomomorphism.linear g x y) ⟩
                      (((f' x) +N (f' y)) +N ((g' x) +N (g' y)))    ≡⟨ sym (Module+Isasso {M = N} (f' x) (f' y)
                                                                                                  ((g' x) +N (g' y))) ⟩
                      ((f' x) +N ((f' y) +N ((g' x) +N (g' y))))    ≡⟨ cong (λ z → (f' x) +N z)
                                                                            (Module+Isasso {M = N} (f' y) (g' x) (g' y)) ⟩
                      ((f' x) +N (((f' y) +N (g' x)) +N (g' y)))    ≡⟨ cong (λ z → (f' x) +N (z +N (g' y)))
                                                                            (ModuleIsAb {M = N} (f' y) (g' x)) ⟩
                      ((f' x) +N (((g' x) +N (f' y)) +N (g' y)))    ≡⟨ (cong (λ z → f' x +N z)
                                                                             (sym (Module+Isasso {M = N} (g' x) (f' y) (g' y)))) ⟩
                      ((f' x) +N ((g' x) +N ((f' y) +N (g' y))))    ≡⟨ Module+Isasso {M = N} (f' x) (g' x)
                                                                                             ((f' y) +N (g' y)) ⟩
                      (((f' x) +N (g' x)) +N ((f' y) +N (g' y))) ∎)
             λ r x → ((f' (r ⋆M x)) +N g' (r ⋆M x))   ≡⟨ cong₂ _+N_ (ModuleHomomorphism.scalar f r x)
                                                                    (ModuleHomomorphism.scalar g r x) ⟩
                     ((r ⋆N (f' x)) +N (r ⋆N (g' x))) ≡⟨ sym (ModuleRDist {M = N} r (f' x) (g' x)) ⟩
                     (r ⋆N ((f' x) +N (g' x))) ∎
    where
      f' = ModuleHomomorphism.h f
      g' = ModuleHomomorphism.h g
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _+N_ : ⟨ N ⟩M → ⟨ N ⟩M → ⟨ N ⟩M
      x +N y = (N Module.+ x) y
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
      r ⋆M x = (M Module.⋆ r) x
      _⋆N_ : ⟨ R ⟩ → ⟨ N ⟩M → ⟨ N ⟩M
      r ⋆N x = (N Module.⋆ r) x

-Hom_ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → ModuleHomomorphism R M N → ModuleHomomorphism R M N
-Hom_ {R = R} {M} {N} f =
  moduleHomo (λ x → -N (f' x))
             (λ x y → (-N (f' (x +M y)))              ≡⟨ cong -N_ (ModuleHomomorphism.linear f x y) ⟩
                      (-N ((f' x) +N (f' y)))         ≡⟨ ModuleInvDist N (f' x) (f' y) ⟩
                      ((-N (f' x)) +N (-N (f' y))) ∎)
              λ r x → (-N (f' (r ⋆M x))) ≡⟨ cong -N_ (ModuleHomomorphism.scalar f r x) ⟩
                      (-N (r ⋆N f' x))   ≡⟨ ModuleInvCommScalar N r (f' x) ⟩
                      (r ⋆N (-N (f' x))) ∎
    where
      f' = ModuleHomomorphism.h f
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
      x +M y = (M Module.+ x) y
      _+N_ : ⟨ N ⟩M → ⟨ N ⟩M → ⟨ N ⟩M
      x +N y = (N Module.+ x) y
      -M_ : ⟨ M ⟩M → ⟨ M ⟩M
      -M x = (Module.- M) x
      -N_ : ⟨ N ⟩M → ⟨ N ⟩M
      -N x = (Module.- N) x
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
      r ⋆M x = (M Module.⋆ r) x
      _⋆N_ : ⟨ R ⟩ → ⟨ N ⟩M → ⟨ N ⟩M
      r ⋆N x = (N Module.⋆ r) x


RModAdHomSets : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → AbGroupStr (ModuleHomomorphism R M N)
RModAdHomSets {R = R} M N =
  abgroupstr (0a M N)
             _+Hom_
             -Hom_
             (isabgroup
               (isgroup
                 (ismonoid
                   (issemigroup
                     (isSetModuleHomo M N)
                     (λ f g h → ModuleHomo≡ (funExt (λ x → Module+Isasso {M = N} (ModuleHomomorphism.h f x)
                                            (ModuleHomomorphism.h g x) (ModuleHomomorphism.h h x)))))
                   λ f → ModuleHomo≡ (funExt (λ x → ModuleZeroRight {M = N} (ModuleHomomorphism.h f x))) ,
                         ModuleHomo≡ (funExt (λ x → ModuleZeroLeft {M = N} (ModuleHomomorphism.h f x))))
                 λ f → (ModuleHomo≡ (funExt (λ x → ModuleInvRight {M = N} (ModuleHomomorphism.h f x)))) ,
                        ModuleHomo≡ (funExt (λ x → ModuleInvLeft {M = N} (ModuleHomomorphism.h f x))))
               λ f g → ModuleHomo≡ (funExt (λ x → ModuleIsAb {M = N} (ModuleHomomorphism.h f x)
                                                                           (ModuleHomomorphism.h g x))))

RModIsPreAdditive : {ℓ : Level} → (R : CommutativeRing {ℓ}) → PreAdditiveCategory (RMod {R = R})
RModIsPreAdditive R =
  preAddCat (abHomSets RModAdHomSets)
            (λ {x} {y} {z} {f} {g} {h} → ModulePreAddLinear {x} {y} {z} {f} {g} {h})
            (λ {x} {y} {z} {f} {g} {h} → ModulePostAddLinear {x} {y} {z} {f} {g} {h})
    where
      ModulePreAddLinear : {M N S : Module R} → {f : ModuleHomomorphism R M N} → {g h : ModuleHomomorphism R N S} →
                           ModuleHomoComp f (g +Hom h) ≡ ((ModuleHomoComp f g) +Hom (ModuleHomoComp f h))
      ModulePreAddLinear {M} {N} {S} {f} {g} {h} = ModuleHomo≡ (funExt (λ x → refl))

      ModulePostAddLinear : {M N S : Module R} → {f g : ModuleHomomorphism R M N} → {h : ModuleHomomorphism R N S} →
                            ModuleHomoComp (f +Hom g) h ≡ ((ModuleHomoComp f h) +Hom (ModuleHomoComp g h))
      ModulePostAddLinear {M} {N} {S} {f} {g} {h} = ModuleHomo≡ (funExt (λ x → ModuleHomomorphism.linear h
                                                      (ModuleHomomorphism.h f x) (ModuleHomomorphism.h g x)))

RModHasAllBinDirSums : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → BinDirectSum (RMod {R = R}) M N
RModHasAllBinDirSums {R = R} M N =
  binDirSum (RModIsPreAdditive R)
            (productOfModules M N)
            (BinaryCoProduct.pA (ProductIsBinaryCoProductNonTrunc R M N))
            (BinaryCoProduct.pB (ProductIsBinaryCoProductNonTrunc R M N))
            (BinaryProduct.pA (ProductIsBinaryProductNonTrunc R M N))
            (BinaryProduct.pB (ProductIsBinaryProductNonTrunc R M N))
            (ModuleHomo≡ (funExt (λ m → refl)))
            (ModuleHomo≡ (funExt (λ n → refl)))
            (ModuleHomo≡ (funExt (λ (m , n) →
              (((m , 0N)) +Prod ((0M , n))) ≡⟨ Σ≡ (ModuleZeroRight {M = M} m) (ModuleZeroLeft {M = N} n) ⟩
              (m , n) ∎)))
    where
      0M = Module.0m M
      0N = Module.0m N
      _+Prod_ = productOfModules+ M N
