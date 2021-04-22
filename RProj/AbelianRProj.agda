{-# OPTIONS --cubical #-}

module ThesisWork.RProj.AbelianRProj where

open import Cubical.Foundations.Prelude
--open import ThesisWork.HelpFunctions
--open import Cubical.Data.Sigma.Base
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
--open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
--open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
--open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
--open import ThesisWork.BasicCategoryTheory.Limits.Kernel
--open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import ThesisWork.RModules.CommutativeRing
--open import Cubical.Algebra.Ring.Base
--open import Cubical.Algebra.Semigroup.Base
--open import Cubical.Algebra.Monoid.Base
--open import Cubical.Algebra.Group.Base
--open import Cubical.Algebra.AbGroup.Base
--open import Cubical.Algebra.Module.Base
--open import ThesisWork.RModules.RModuleHomomorphism
open import ThesisWork.RModules.RModuleHomomorphismProperties
open import ThesisWork.RModules.RModule
--open import ThesisWork.RModules.RMod
--open import Cubical.Foundations.Structure
--open import ThesisWork.CompatibilityCode
--open import ThesisWork.SetSigmaType
--open import Agda.Builtin.Cubical.HCompU
--open import Cubical.Core.Primitives renaming
--  (_[_≡_] to _[_≡_]P)

--open import Cubical.HITs.SetQuotients.Base
--open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.PropositionalTruncation.Base
--open import ThesisWork.RModules.RModuleProperties
--open import ThesisWork.SetQuotientHelp
--open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
--open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
--open import Cubical.HITs.PropositionalTruncation.Properties renaming
--  (elim to elimHprop ;
--   elim2 to elim2Hprop ;
--   elim3 to elim3Hprop ;
--   rec to recHprop ;
--   rec2 to rec2Hprop )

--open import Cubical.Foundations.Isomorphism
--open import Cubical.Foundations.Univalence
--open import Cubical.Relation.Binary.Base
--open import ThesisWork.RModules.MonicToInjective
open import ThesisWork.RModules.RModProperties
open import ThesisWork.AbelianCategory.Abelian
open import ThesisWork.RProj.RProj
open import ThesisWork.RProj.ProjModule
open import ThesisWork.RProj.Projective
open import ThesisWork.RProj.FinitelyGeneratedModule
open import Cubical.Data.Nat.Base
open import Cubical.Data.Vec.Base
open import ThesisWork.RProj.ProjModuleHomo

--RProjHasZero : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasZeroObject (RProj R)
--RProjHasZero R = (Module→ProjModule (zeroModule R) isProjectiveZero isFinGenZero) ,CatWithZero
--                   ((λ B → (projModuleHomo (λ * → ProjModule.0m B) (λ * * → sym (ModuleZeroRight {M = ProjModule→Module B}
--                   (ProjModule.0m B))) λ r * → sym (ModuleMulPresZero {M = ProjModule→Module B} r)) ,
--                   λ hom → ProjModuleHomo≡ (funExt (λ * → sym (
--                     ProjectiveModuleHomomorphism.h hom * ≡⟨ {!!} ⟩
--                     ProjectiveModuleHomomorphism.h hom * ≡⟨ {!!} ⟩
--                     ProjModule.0m B ∎)))) ,Zero {!!})
--  where
--    _⋆Z_ = Module._⋆_ (zeroModule R)

--    isProjectiveZero : isProjectiveModule R (zeroModule R)
--    isProjectiveZero {E} f e eSurj = zeroModuleisInitialObject R E
--    isFinGenZero : isFinitelyGenerated (zeroModule R)
--    isFinGenZero = ∣ (suc zero , * ∷ [] , λ * → ((CommutativeRingStr.1r (snd R)) ∷ []) ,
--                       (sumGenerators R (zeroModule R) (* ∷ []) ((CommutativeRingStr.1r (snd R)) ∷ []) ≡⟨ refl ⟩
--                       ((CommutativeRingStr.1r (snd R)) ⋆Z *) ≡⟨ ModuleLId {M = zeroModule R} * ⟩
--                       * ∎)) ∣
