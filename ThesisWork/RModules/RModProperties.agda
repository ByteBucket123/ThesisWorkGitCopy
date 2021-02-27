{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModProperties where

open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
open import Cubical.Data.Sigma.Base
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
open import ThesisWork.RModules.CommutativeRing
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Module.Base
open import ThesisWork.RModules.RModuleHomomorphism
open import ThesisWork.RModules.RModuleHomomorphismProperties
open import ThesisWork.RModules.RModule
open import ThesisWork.RModules.RMod
open import Cubical.Foundations.Structure

--*********************************************** hasZeroObject (RMod R) *******************************************************

data oneElemSet {ℓ : Level} : Set ℓ where
  * : oneElemSet

isPropOneElem : {ℓ : Level} → isProp (oneElemSet {ℓ})
isPropOneElem * * = refl

helpIdentity : {ℓ : Level} → (ε : oneElemSet {ℓ}) → (_·_ : oneElemSet → oneElemSet → oneElemSet) →
               (x : oneElemSet) → ((* · *) ≡ *) → ((* · *) ≡ *) → (x · ε ≡ x) × (ε · x ≡ x)
helpIdentity * _·_ * p q = p , q

zeroModule : {ℓ : Level} (R : CommutativeRing {ℓ}) → Module R
zeroModule R =
  moduleConst oneElemSet * (λ x y → *) (λ x → *) (λ r x → *)
  (isModule
    (ismodule
      (isabgroup
        (isgroup
          (ismonoid
            (issemigroup
              (isProp→isSet isPropOneElem)
              λ x y z → refl)
            λ x → helpIdentity * ((λ x y → *)) x refl refl)
          λ x → refl , refl)
        λ x y → refl)
      (λ r s x → refl)
      (λ r s x → refl)
      (λ r x y → refl)
      (isPropOneElem *)))

FuncToZeroModuleIsPropHelp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) →
                             (h k : (ModuleHomomorphism R (zeroModule R) M)) → (x : ⟨ zeroModule R ⟩M) →
                             ModuleHomomorphism.h h x ≡ ModuleHomomorphism.h k x
FuncToZeroModuleIsPropHelp M h k * = (ModuleHomomorphismPreserveZero h) ∙ (sym (ModuleHomomorphismPreserveZero k))

FuncToZeroModuleIsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) →
                         isProp (ModuleHomomorphism R (zeroModule R) M)
FuncToZeroModuleIsProp M h k = ModuleHomo≡ (funExt (FuncToZeroModuleIsPropHelp M h k))

--zeroModuleisInitialObject : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isInitialObject (RMod R) (zeroModule R)
--zeroModuleisInitialObject R module = (λ x → Module.0m module) , FuncToZeroModuleIsProp

--zeroModuleisTerminalObject : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isTerminalObject (RMod R) (zeroModule R)
--zeroModuleisTerminalObject R module = (λ x → *) , funExt (λ x → refl)

--hasZeroObjectRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasZeroObject (RMod R)
--hasZeroObjectRMod R = (zeroModule R) ,CatWithZero ((zeroModuleisInitialObject R) ,Zero (zeroModuleisTerminalObject R))

--******************************************** hasAllBinaryProducts (RMod R) ***********************************************

-- productOfModulesZero : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModulesZero M N = Module.0m M , Module.0m N

-- productOfModules+ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x y : ⟨ M ⟩M × ⟨ N ⟩M) → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModules+ M N (x₁ , x₂) (y₁ , y₂) = ((M Module.+ x₁) y₁) , ((N Module.+ x₂) y₂)

-- productOfModules- : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ M ⟩M × ⟨ N ⟩M → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModules- M N (x₁ , x₂) = ((Module.- M) x₁) , ((Module.- N) x₂)

-- productOfModules⋆ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ R ⟩ → ⟨ M ⟩M × ⟨ N ⟩M → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModules⋆ M N r (x₁ , x₂) = ((M Module.⋆ r) x₁) , ((N Module.⋆ r) x₂)

-- productOfModulesIsSet : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (⟨ M ⟩M × ⟨ N ⟩M)
-- productOfModulesIsSet M N x y p q = {!!}

-- productOfModulesAsso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x y z : ⟨ M ⟩M × ⟨ N ⟩M) →
--       productOfModules+ M N x (productOfModules+ M N y z) ≡
--       productOfModules+ M N (productOfModules+ M N x y) z
-- productOfModulesAsso M N (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) = Σ≡ (Module+Isasso {M = M} x₁ y₁ z₁) (Module+Isasso {M = N} x₂ y₂ z₂)

-- productOfModulesZeroRight : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
--                             (productOfModules+ M N x (productOfModulesZero M N) ≡ x)
-- productOfModulesZeroRight M N (x₁ , x₂) = Σ≡ (ModuleZeroRight {M = M} x₁) (ModuleZeroRight {M = N} x₂)

-- productOfModulesZeroLeft : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
--                             (productOfModules+ M N (productOfModulesZero M N) x ≡ x)
-- productOfModulesZeroLeft M N (x₁ , x₂) = Σ≡ (ModuleZeroLeft {M = M} x₁) (ModuleZeroLeft {M = N} x₂)

-- productOfModulesInvRight : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
--                             productOfModules+ M N x (productOfModules- M N x) ≡ productOfModulesZero M N
-- productOfModulesInvRight M N (x₁ , x₂) = Σ≡ (ModuleInvRight {M = M} x₁) (ModuleInvRight {M = N} x₂)

-- productOfModulesInvLeft : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
--                             productOfModules+ M N (productOfModules- M N x) x ≡ productOfModulesZero M N
-- productOfModulesInvLeft M N (x₁ , x₂) = Σ≡ (ModuleInvLeft {M = M} x₁) (ModuleInvLeft {M = N} x₂)

-- productOfModulesAb : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x y : ⟨ M ⟩M × ⟨ N ⟩M) → 
--                       productOfModules+ M N x y ≡ productOfModules+ M N y x
-- productOfModulesAb M N (x₁ , x₂) (y₁ , y₂) = Σ≡ (ModuleIsAb {M = M} x₁ y₁) (ModuleIsAb {M = N} x₂ y₂)

-- productOfModules·Isasso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (r s : ⟨ R ⟩) →
--                           (x : ⟨ M ⟩M × ⟨ N ⟩M) →
--                           productOfModules⋆ M N (((snd R) CommutativeRingStr.· r) s) x ≡
--                           productOfModules⋆ M N r (productOfModules⋆ M N s x)
-- productOfModules·Isasso M N r s (x₁ , x₂) = Σ≡ (Module·Isasso {M = M} r s x₁) (Module·Isasso {M = N} r s x₂)

-- productOfModulesLDist : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (r s : ⟨ R ⟩) →
--                           (x : ⟨ M ⟩M × ⟨ N ⟩M) →
--                           productOfModules⋆ M N (((snd R) CommutativeRingStr.+ r) s) x ≡
--                           productOfModules+ M N (productOfModules⋆ M N r x) (productOfModules⋆ M N s x)
-- productOfModulesLDist M N r s (x₁ , x₂) = Σ≡ (ModuleLDist {M = M} r s x₁) (ModuleLDist {M = N} r s x₂)

-- productOfModulesRDist : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (r : ⟨ R ⟩) →
--                         (x y : ⟨ M ⟩M × ⟨ N ⟩M) →
--                         productOfModules⋆ M N r (productOfModules+ M N x y) ≡
--                         productOfModules+ M N (productOfModules⋆ M N r x) (productOfModules⋆ M N r y)
-- productOfModulesRDist M N r (x₁ , x₂) (y₁ , y₂)= Σ≡ (ModuleRDist {M = M} r x₁ y₁) (ModuleRDist {M = N} r x₂ y₂)

-- productOfModulesLId : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) →
--                       productOfModules⋆ M N (CommutativeRingStr.1r (snd R)) x ≡ x
-- productOfModulesLId  M N (x₁ , x₂) = Σ≡ (ModuleLId {M = M} x₁) (ModuleLId {M = N} x₂)

-- productOfModules : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → Module R
-- productOfModules M N =
--   moduleConst
--     (⟨ M ⟩M × ⟨ N ⟩M)
--     (productOfModulesZero M N)
--     (productOfModules+ M N)
--     (productOfModules- M N)
--     (productOfModules⋆ M N)
--     (isModule
--       (ismodule
--         (isabgroup
--           (isgroup
--             (ismonoid
--               (issemigroup
--                 (productOfModulesIsSet M N)
--                 (productOfModulesAsso M N))
--               λ x → (productOfModulesZeroRight M N x) , (productOfModulesZeroLeft M N x))
--             λ x → productOfModulesInvRight M N x , productOfModulesInvLeft M N x)
--           (productOfModulesAb M N))
--         (productOfModules·Isasso M N)
--         (productOfModulesLDist M N)
--         (productOfModulesRDist M N)
--         (productOfModulesLId M N)))

-- prodHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N Z : Module R} → ModuleHomomorphism R Z M → ModuleHomomorphism R Z N
--            → ModuleHomomorphism R Z (productOfModules M N)
-- prodHomo h k = moduleHomo (λ z → (ModuleHomomorphism.h h z) , (ModuleHomomorphism.h k z))
--   (λ x y → Σ≡ (ModuleHomomorphism.linear h x y) (ModuleHomomorphism.linear k x y))
--   (λ r x → Σ≡ (ModuleHomomorphism.scalar h r x) (ModuleHomomorphism.scalar k r x))

-- --ProductIsBinaryProduct : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A B A×B : ob (RMod R)) → isBinaryProduct (RMod R) A B A×B
-- --ProductIsBinaryProduct R A B A×B = | BinProd A×B fst snd prodHomo (ModuleHomo≡ refl) (ModuleHomo≡ refl)
-- --  λ f g h fsth≡f sndh≡g → Σ≡
-- --    (ModuleHomo≡ (sym fsth≡f))
-- --    (ModuleHomo≡ (sym sndh≡g))
-- --  , refl |

-- --hasAllBinaryProductsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllBinaryProducts (RMod R)
-- --hasAllBinaryProductsRMod R A B = | λ A B → productOfModules M N , ? |
