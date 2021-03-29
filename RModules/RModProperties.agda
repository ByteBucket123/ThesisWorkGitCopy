{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModProperties where

--open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
open import Cubical.Data.Sigma.Base
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
open import ThesisWork.BasicCategoryTheory.Limits.Kernel
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
open import ThesisWork.CompatibilityCode
open import ThesisWork.SetSigmaType
open import Agda.Builtin.Cubical.HCompU
open import Cubical.Core.Primitives
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.PropositionalTruncation.Base
open import ThesisWork.RModules.RModuleProperties
open import ThesisWork.SetQuotientHelp

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

-- --zeroModuleisInitialObject : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isInitialObject (RMod R) (zeroModule R)
-- --zeroModuleisInitialObject R module = (λ x → Module.0m module) , FuncToZeroModuleIsProp

-- --zeroModuleisTerminalObject : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isTerminalObject (RMod R) (zeroModule R)
-- --zeroModuleisTerminalObject R module = (λ x → *) , funExt (λ x → refl)

-- --hasZeroObjectRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasZeroObject (RMod R)
-- --hasZeroObjectRMod R = (zeroModule R) ,CatWithZero ((zeroModuleisInitialObject R) ,Zero (zeroModuleisTerminalObject R))

-- --******************************************** hasAllBinaryProducts (RMod R) ***********************************************

-- productOfModulesZero : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModulesZero M N = Module.0m M , Module.0m N

-- productOfModules+ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x y : ⟨ M ⟩M × ⟨ N ⟩M) → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModules+ M N (x₁ , x₂) (y₁ , y₂) = ((M Module.+ x₁) y₁) , ((N Module.+ x₂) y₂)

-- productOfModules- : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ M ⟩M × ⟨ N ⟩M → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModules- M N (x₁ , x₂) = ((Module.- M) x₁) , ((Module.- N) x₂)

-- productOfModules⋆ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ R ⟩ → ⟨ M ⟩M × ⟨ N ⟩M → ⟨ M ⟩M × ⟨ N ⟩M
-- productOfModules⋆ M N r (x₁ , x₂) = ((M Module.⋆ r) x₁) , ((N Module.⋆ r) x₂)

-- productOfModulesIsSet : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (⟨ M ⟩M × ⟨ N ⟩M)
-- productOfModulesIsSet M N = isSetΣ (isSetModule M) λ _ → isSetModule N

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
--               λ x → productOfModulesInvRight M N x , productOfModulesInvLeft M N x)
--         (productOfModulesAb M N))
--         (productOfModules·Isasso M N)
--         (productOfModulesLDist M N)
--         (productOfModulesRDist M N)
--         (productOfModulesLId M N)))

-- prodHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N Z : Module R} → ModuleHomomorphism R Z M → ModuleHomomorphism R Z N
--            → ModuleHomomorphism R Z (productOfModules M N)
-- prodHomo h k = moduleHomo (λ z → (ModuleHomomorphism.h h z) , (ModuleHomomorphism.h k z))
--   (λ x y → Σ≡ (ModuleHomomorphism.linear h x y) (ModuleHomomorphism.linear k x y))
--   (λ r x → Σ≡ (ModuleHomomorphism.scalar h r x) (ModuleHomomorphism.scalar k r x))

-- -- --ProductIsBinaryProduct : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A B : ob (RMod R)) → isBinaryProduct (RMod R) A B (productOfModules A B)
-- -- --ProductIsBinaryProduct R A B = | BinProd A×B fst snd prodHomo (ModuleHomo≡ refl) (ModuleHomo≡ refl)
-- -- --  λ f g h fsth≡f sndh≡g → Σ≡
-- -- --    (ModuleHomo≡ (sym fsth≡f))
-- -- --    (ModuleHomo≡ (sym sndh≡g))
-- -- --  , refl |
-- --  where
-- --    A×B = productOfModules A B

-- -- --hasAllBinaryProductsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllBinaryProducts (RMod R)
-- -- --hasAllBinaryProductsRMod R A B = | productOfModules M N , ProductIsBinaryProduct R A B |

-- --******************************************** hasAllBinaryCoProducts (RMod R) ***********************************************


-- coProdHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N Z : Module R} → ModuleHomomorphism R M Z → ModuleHomomorphism R N Z
--            → ModuleHomomorphism R (productOfModules M N) Z
-- coProdHomo {R = R} {M = M} {N = N} {Z = Z} h k =
--   moduleHomo (λ (a , b) → (f a) +Z (g b))
--              (λ (x₁ , x₂) (y₁ , y₂) →
--              (f (x₁ +M y₁) +Z g (x₂ +N y₂))                 ≡⟨ cong (λ x → x +Z g (x₂ +N y₂)) (ModuleHomomorphism.linear h x₁ y₁) ⟩
--              (((f x₁) +Z (f y₁)) +Z g (x₂ +N y₂))           ≡⟨ cong (λ x → ((f x₁) +Z (f y₁)) +Z x) (ModuleHomomorphism.linear k x₂ y₂) ⟩
--              (((f x₁) +Z (f y₁)) +Z (g x₂ +Z g y₂))         ≡⟨ sym (assoZ (f x₁) (f y₁) (g x₂ +Z g y₂)) ⟩
--              ((f x₁) +Z ((f y₁) +Z (g x₂ +Z g y₂)))         ≡⟨ cong (λ x → (f x₁) +Z x) (assoZ (f y₁) (g x₂) (g y₂)) ⟩
--              (((f x₁) +Z (((f y₁) +Z (g x₂)) +Z g y₂)))     ≡⟨ cong (λ x → f x₁ +Z (x +Z g y₂)) (comm+Z (f y₁) (g x₂)) ⟩
--              ((((f x₁) +Z (((g x₂) +Z (f y₁)) +Z g y₂))))   ≡⟨ cong (λ x → f x₁ +Z x) (sym (assoZ (g x₂) (f y₁) (g y₂))) ⟩
--              (((((f x₁) +Z ((g x₂) +Z ((f y₁) +Z g y₂)))))) ≡⟨ assoZ (f x₁) (g x₂) ((f y₁) +Z (g y₂)) ⟩
--              ((f x₁ +Z g x₂) +Z ((f y₁) +Z (g y₂))) ∎
--              )
--              λ r (x₁ , x₂) →
--              ((f (r ⋆M x₁)) +Z g (r ⋆N x₂))   ≡⟨ cong (λ x → x +Z g (r ⋆N x₂)) (ModuleHomomorphism.scalar h r x₁) ⟩
--              ((r ⋆Z (f x₁)) +Z g (r ⋆N x₂))   ≡⟨ cong (λ x → (r ⋆Z (f x₁)) +Z  x) (ModuleHomomorphism.scalar k r x₂) ⟩
--              ((r ⋆Z (f x₁)) +Z (r ⋆Z (g x₂))) ≡⟨ sym (ModuleRDist {M = Z} r (f x₁) (g x₂)) ⟩
--              (r ⋆Z ((f x₁) +Z (g x₂))) ∎
--   where
--     _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
--     x +M y = (M Module.+ x) y
--     _+N_ : ⟨ N ⟩M → ⟨ N ⟩M → ⟨ N ⟩M
--     x +N y = (N Module.+ x) y
--     _+Z_ : ⟨ Z ⟩M → ⟨ Z ⟩M → ⟨ Z ⟩M
--     x +Z y = (Z Module.+ x) y
--     _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
--     r ⋆M x = (M Module.⋆ r) x
--     _⋆N_ : ⟨ R ⟩ → ⟨ N ⟩M → ⟨ N ⟩M
--     r ⋆N x = (N Module.⋆ r) x
--     _⋆Z_ : ⟨ R ⟩ → ⟨ Z ⟩M → ⟨ Z ⟩M
--     r ⋆Z x = (Z Module.⋆ r) x
--     f = ModuleHomomorphism.h h
--     g = ModuleHomomorphism.h k
--     assoZ = Module+Isasso {M = Z}
--     comm+Z = ModuleIsAb {M = Z}

-- --moduleHomo (λ z → (ModuleHomomorphism.h h z) , (ModuleHomomorphism.h k z))
-- --  (λ x y → Σ≡ (ModuleHomomorphism.linear h x y) (ModuleHomomorphism.linear k x y))
-- --  (λ r x → Σ≡ (ModuleHomomorphism.scalar h r x) (ModuleHomomorphism.scalar k r x))

-- HelpCoProdUnique : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N Z : Module R} → (k : ModuleHomomorphism R M Z) → (u : ModuleHomomorphism R N Z) → (h : ModuleHomomorphism R (productOfModules M N) Z) →
--                    (λ a → ModuleHomomorphism.h h (a , Module.0m N)) ≡ ModuleHomomorphism.h k → (λ b → ModuleHomomorphism.h h (Module.0m M , b)) ≡ ModuleHomomorphism.h u →
--                    (λ a → ModuleHomomorphism.h (coProdHomo k u) (a , Module.0m N)) ≡ ModuleHomomorphism.h k → (λ b → ModuleHomomorphism.h (coProdHomo k u) (Module.0m M , b)) ≡ ModuleHomomorphism.h u →
--                    coProdHomo k u ≡ h
-- HelpCoProdUnique {M = M} {N = N} {Z = Z} k u h ha0=k h0b=u f×ga0=k f×g0b=u = ModuleHomo≡ (funExt (λ x →
--   f×g x                          ≡⟨ cong f×g (Σ≡ (sym (ModuleZeroRight {M = M} (fst x))) (sym (ModuleZeroLeft {M = N} (snd x)))) ⟩
--   f×g (pA x +P pB x)             ≡⟨ ModuleHomomorphism.linear (coProdHomo k u) (pA x) (pB x) ⟩
--   ((f×g (pA x)) +Z (f×g (pB x))) ≡⟨ cong₂ _+Z_ (funExt⁻ f×ga0=k (fst x) ∙ sym (funExt⁻ ha0=k (fst x))) ((funExt⁻ f×g0b=u (snd x)) ∙ (sym (funExt⁻ h0b=u (snd x)))) ⟩
--   ((h' (pA x)) +Z (h' (pB x)))   ≡⟨ sym (ModuleHomomorphism.linear h (pA x) (pB x)) ⟩
--   h' ((pA x) +P (pB x))          ≡⟨ cong h' (Σ≡ (ModuleZeroRight {M = M} (fst x)) (ModuleZeroLeft {M = N} (snd x))) ⟩
--   h' x ∎
--   ))
--     where
--       f = ModuleHomomorphism.h k
--       g = ModuleHomomorphism.h u
--       h' = ModuleHomomorphism.h h
--       f×g = ModuleHomomorphism.h (coProdHomo k u)
--       _+P_ : ⟨ productOfModules M N ⟩M → ⟨ productOfModules M N ⟩M → ⟨ productOfModules M N ⟩M
--       x +P y = (productOfModules M N Module.+ x) y
--       _+Z_ : ⟨ Z ⟩M → ⟨ Z ⟩M → ⟨ Z ⟩M
--       x +Z y = (Z Module.+ x) y
--       pA : (x : ⟨ productOfModules M N ⟩M) → ⟨ productOfModules M N ⟩M
--       pA x = fst x , Module.0m N
--       pB : (x : ⟨ productOfModules M N ⟩M) → ⟨ productOfModules M N ⟩M
--       pB x = Module.0m M , snd x


-- --    uni : {Z : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A Z) →
-- --          (g : Precategory.hom (UnivalentCategory.cat C) B Z) → (h : Precategory.hom (UnivalentCategory.cat C) A×B Z) →
-- --          Precategory.seq (UnivalentCategory.cat C) pA h ≡ f → Precategory.seq (UnivalentCategory.cat C) pB h ≡ g →
-- --          < f × g > ≡ h

-- -- --ProductIsBinaryCoProduct : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A B : ob (RMod R)) → isBinaryCoProduct (RMod R) A B (productOfModules A B)
-- -- --ProductIsBinaryCoProduct R A B = | BinCoProd A×B (λ a → a , Module.0m B ) (λ b → Module.0m A , b) coProdHomo pAcomp pBComp
-- --                                      (λ k u h ha0=k h0b=u → HelpCoProdUnique k u h ha0=k h0b=u (pAcomp k u) (pBcomp k u) |
-- --  where
-- --    A×B = productOfModules A B
-- --    pAcomp = (λ f g → funExt (λ m → ModuleHomomorphismAddHomZero m f g))
-- --    pBcomp = (λ f g → funExt (λ n → ModuleHomomorphismAddHomZeroSym n f g))


-- -- --hasAllBinaryCoProductsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllBinaryProducts (RMod R)
-- -- --hasAllBinaryCoProductsRMod R A B = | λ A B → productOfModules M N , ? |


--******************************************** hasAllKernels (RMod R) ***********************************************

HelpFiber≡ : ∀ {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → isSet B → {f : A → B} → {y : B} → {u v : Helpers.fiber f y} → fst u ≡ fst v → u ≡ v
HelpFiber≡ setB {f = f} {y = y} {u = u} {v = v} fstEq = Σ≡ fstEq (isProp→PathP (λ i → setB (f (fstEq i)) y) (snd u) (snd v))
    

makeKernelObjRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} → (f : Precategory.hom (RModPreCat R) A B) → Precategory.ob (RModPreCat R)
makeKernelObjRMod {ℓ = ℓ} R {A = A} {B = B} f =
  moduleConst KObj 0K _+K_ -K_ _⋆K_
  (isModule
    (ismodule
      (isabgroup
        (isgroup
          (ismonoid
            (issemigroup
              (isSetΣ (isSetModule A) (λ a → isProp→isSet (isSetModule B (f' a) 0B)))
              λ (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) → HelpFiber≡B (Module+Isasso {M = A} a₁ a₂ a₃))
            λ (a , b) → HelpFiber≡B (ModuleZeroRight {M = A} a) ,
                        HelpFiber≡B (ModuleZeroLeft {M = A} a))
          λ (a , b) → HelpFiber≡B (ModuleInvRight {M = A} a) ,
                      HelpFiber≡B (ModuleInvLeft {M = A} a) )
        λ (a₁ , b₁) (a₂ , b₂) → HelpFiber≡B (ModuleIsAb {M = A} a₁ a₂))
      (λ r s (a , b) → HelpFiber≡B (Module·Isasso {M = A} r  s a))
      (λ r s (a , b) → HelpFiber≡B (ModuleLDist {M = A} r s a))
      (λ r (a₁ , b₁) (a₂ , b₂) → HelpFiber≡B (ModuleRDist {M = A} r a₁ a₂))
      λ (a , b) → HelpFiber≡B (ModuleLId {M = A} a)))
    where
      f' = ModuleHomomorphism.h f
      _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
      x +A y = (A Module.+ x) y
      _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
      x +B y = (B Module.+ x) y
      0B = Module.0m B
      -A_ : ⟨ A ⟩M → ⟨ A ⟩M
      -A x = (Module.- A) x
      -B_ : ⟨ B ⟩M → ⟨ B ⟩M
      -B x = (Module.- B) x
      _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
      r ⋆A x = (A Module.⋆ r) x
      _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
      r ⋆B x = (B Module.⋆ r) x
      
      KObj : Type ℓ
      KObj = Helpers.fiber (ModuleHomomorphism.h f) (Module.0m B)
      0K = Module.0m A , ModuleHomomorphismPreserveZero f

      _+K_ : KObj → KObj → KObj
      (a₁ , b₁) +K (a₂ , b₂) = (a₁ +A a₂) ,
                               (f' (a₁ +A a₂)        ≡⟨ ModuleHomomorphism.linear f a₁ a₂ ⟩
                               ((f' a₁) +B (f' a₂)) ≡⟨ cong₂ _+B_ b₁ b₂ ⟩
                               (0B +B 0B)           ≡⟨ ModuleZeroRight {M = B} 0B ⟩
                               0B ∎)

      -K_ : KObj → KObj
      -K (a , b) = (-A a) , (
                   f' (-A a)   ≡⟨ ModuleHomomorphismLinSub a f ⟩
                   (-B (f' a)) ≡⟨ cong -B_ b ⟩
                   (-B 0B)     ≡⟨ ModuleSubPresZero {M = B} ⟩
                   0B ∎
                   )

      _⋆K_ : ⟨ R ⟩ → KObj → KObj
      r ⋆K (a , b) =(r ⋆A a) , (
                    f' (r ⋆A a)   ≡⟨ ModuleHomomorphism.scalar f r a ⟩
                    (r ⋆B (f' a)) ≡⟨ cong (λ x → r ⋆B x) b ⟩
                    (r ⋆B 0B)    ≡⟨ ModuleMulPresZero {M = B} r ⟩
                    0B ∎
                    )

      HelpFiber≡B : {f : ⟨ A ⟩M → ⟨ B ⟩M} → {y : ⟨ B ⟩M} → {u v : Helpers.fiber f y} → fst u ≡ fst v → u ≡ v
      HelpFiber≡B = HelpFiber≡ (isSetModule B) 
      
--hasAllKernelsRMod  : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllKernels (RMod R)
--hasAllKernelsRMod R {A} {B} f = | makeKernelObjRMod f ,  kernelConst fst (funExt snd) (λ h hf=0 →
--  moduleHomo (λ x → ModuleHomomorphism.h h x, funExt⁻ hf=0 x)
--             (λ x y → HelpFiber≡ (isSetModule B) (ModuleHomomorphism.linear h x y))
--             (λ r x → HelpFiber≡ (isSetModule B) (ModuleHomomorphism.scalar h x y)) , refl)
--  (λ D g h gker=hker → funExt (λ x → gker=hker x) )) |

--******************************************** hasAllCoKernels (RMod R) ***********************************************

coKernelRel : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
                      (f : Precategory.hom (RModPreCat R) A B) → (b b' : ⟨ B ⟩M) → Type ℓ
coKernelRel R {A} {B} f b b' = Σ[ a ∈  ⟨ A ⟩M ] b' ≡ b +B f' a
    where
      f' = ModuleHomomorphism.h f
      _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
      x +B y = (B Module.+ x) y

coKernelPropRel : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
                      (f : Precategory.hom (RModPreCat R) A B) → (b b' : ⟨ B ⟩M) → Type ℓ
coKernelPropRel R {A} {B} f b b' = ∥ (coKernelRel R f b b') ∥

--elimProp2 : ((x y : A / R ) → isProp (C x y))
--          → ((a b : A) → C [ a ] [ b ])
--          → (x y : A / R)
--          → C x y

--elim : {B : A / R → Type ℓ}
--     → ((x : A / R) → isSet (B x))
--     → (f : (a : A) → (B [ a ]))
--     → ((a b : A) (r : R a b) → PathP (λ i → B (eq/ a b r i)) (f a) (f b))
--     → (x : A / R)
--     → B x

makeCoKernelObjRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
                      (f : Precategory.hom (RModPreCat R) A B) → Precategory.ob (RModPreCat R)
makeCoKernelObjRMod {ℓ} R {A} {B} f =
  moduleConst coKObj 0coK _+coK_ -coK_ _⋆coK_
  (isModule
    (ismodule
      (isabgroup
        (isgroup
          (ismonoid
            (issemigroup
              squash/
              {!!})
--λ a b c → elim {!!} (λ a →
--                           elim {!!} (λ b →
--                             elim {!!} (λ c → [ a ] +coK ([ b ] +coK [ c ]) ≡ ([ a ] +coK [ b ]) +coK [ c ]) {!!} c)
--                           {!!} b)
--                         {!!} a
            {!!})
          {!!})
        {!!})
      {!!}
      {!!}
      {!!}
      {!!}))
    where
      f' = ModuleHomomorphism.h f
      0A = Module.0m A
      0B = Module.0m B
      _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
      x +B y = (B Module.+ x) y
      -A_ : ⟨ A ⟩M → ⟨ A ⟩M
      -A x = (Module.- A) x
      -B_ : ⟨ B ⟩M → ⟨ B ⟩M
      -B x = (Module.- B) x
      _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
      r ⋆B a = (B Module.⋆ r) a 
      _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
      r ⋆A a = (A Module.⋆ r) a 
      
      coKObj : Type ℓ
      coKObj = ⟨ B ⟩M / coKernelRel R f
      0coK = [ 0B ]
      _+coK_ : coKObj → coKObj → coKObj
      _+coK_ = rec2 squash/ (λ a b → [ a +B b ])
               (λ a b c Rab → eq/ (a +B c) (b +B c)((fst Rab) ,
                 (b +B c                    ≡⟨ cong (λ x → x +B c) (snd Rab) ⟩
                 ((a +B f' (fst Rab)) +B c) ≡⟨ sym(Module+Isasso {M = B} a (f' (fst Rab)) c) ⟩
                 (a +B (f' (fst Rab) +B c)) ≡⟨ cong (λ x → a +B x) (ModuleIsAb {M = B} (f' (fst Rab)) c) ⟩
                 (a +B (c +B f' (fst Rab))) ≡⟨ Module+Isasso {M = B} a c (f' (fst Rab)) ⟩
                 ((a +B c) +B f' (fst Rab)) ∎)))
               λ a b c Rbc → eq/ (a +B b) (a +B c) ((fst Rbc) ,
                 ((a +B c) ≡⟨ cong (λ x → a +B x) (snd Rbc) ⟩
                 (a +B (b +B f' (fst Rbc))) ≡⟨ Module+Isasso {M = B} a b (f' (fst Rbc)) ⟩
                  ((a +B b) +B f' (fst Rbc)) ∎))
      -coK_ : coKObj → coKObj
      -coK_ = rec squash/ (λ a → [ -B a ])
                  λ a b Rab → eq/ (-B a) (-B b) ((-A fst Rab) ,
                    ((-B b)                       ≡⟨  cong (λ x → -B x) (snd Rab) ⟩
                    (-B (a +B f' (fst Rab)))      ≡⟨  AbgroupInvDist {G = LeftModule→AbGroup (Module→LeftModule B)}
                                                        a (f' (fst Rab)) ⟩
                    ((-B a) +B (-B f' (fst Rab))) ≡⟨  cong (λ x → (-B a) +B x) (sym (ModuleHomomorphismLinSub {M = A} {N = B}
                                                                                  (fst Rab) f)) ⟩
                    ((-B a) +B f' (-A fst Rab)) ∎))
      _⋆coK_ : ⟨ R ⟩ → coKObj → coKObj
      _⋆coK_ = λ r → rec squash/ (λ a → [ r ⋆B a ]) λ a b Rab → eq/ (r ⋆B a) (r ⋆B b) ((r ⋆A fst Rab) ,
                 ((r ⋆B b)                         ≡⟨ cong (λ x → r ⋆B x) (snd Rab) ⟩
                 (r ⋆B (a +B f' (fst Rab)))        ≡⟨ ModuleRDist {M = B} r a (f' (fst Rab)) ⟩
                 ((r ⋆B a) +B (r ⋆B f' (fst Rab))) ≡⟨ cong (λ x → (r ⋆B a) +B  x) (sym (ModuleHomomorphism.scalar f r (fst Rab))) ⟩
                 ((r ⋆B a) +B f' (r ⋆A fst Rab)) ∎))

      AssocoK : (x y z : coKObj) → (x +coK (y +coK z)) ≡ ((x +coK y) +coK z)
      AssocoK = elim3 (λ x y z p q → isProp→isSet (squash/ _ _) p q)
                      (λ x y z → eq/ (x +B (y +B z)) ((x +B y) +B z) (0A ,
                        (((x +B y) +B z)        ≡⟨ sym (Module+Isasso {M = B} x y z) ⟩
                        (x +B (y +B z))         ≡⟨ sym (ModuleZeroRight {M = B} (x +B (y +B z))) ⟩
                        ((x +B (y +B z)) +B 0B) ≡⟨ cong (λ t → (x +B (y +B z)) +B t) (sym (ModuleHomomorphismPreserveZero f)) ⟩
                        ((x +B (y +B z)) +B (f' 0A)) ∎)))
                      (λ a b c d r → {!!})
--                        PathPSetl {B = λ _ _ _ → A / R}
--                          {B1 = λ a b c → a +coK (b +coK c)} {B2 = λ a b c → (a +coK b) +coK c}
--                          (λ x y z → squash/) (eq/ a b r) [ c ] [ d ]
--                            (eq/ (a +B (c +B d)) ((a +B c) +B d)
--                            (0A ,
--                              (((a +B c) +B d) ≡⟨ (λ i → Module+Isasso a c d (~ i)) ⟩
--                              (a +B (c +B d)) ≡⟨ (λ i → ModuleZeroRight (a +B (c +B d)) (~ i)) ⟩
--                              ((a +B (c +B d)) +B 0B) ≡⟨
--                              (λ i → (a +B (c +B d)) +B ModuleHomomorphismPreserveZero f (~ i)) ⟩
--                              ((a +B (c +B d)) +B f' 0A) ∎)))
--                            (eq/ (b +B (c +B d)) ((b +B c) +B d)
--                              (0A ,
--                              (((b +B c) +B d) ≡⟨ (λ i → Module+Isasso b c d (~ i)) ⟩
--                              (b +B (c +B d)) ≡⟨ (λ i → ModuleZeroRight (b +B (c +B d)) (~ i)) ⟩
--                              ((b +B (c +B d)) +B 0B) ≡⟨
--                              (λ i → (b +B (c +B d)) +B ModuleHomomorphismPreserveZero f (~ i)) ⟩
--                              ((b +B (c +B d)) +B f' 0A) ∎))))
                      {!!} {!!}
--      AssocoK [ a ] [ b ] [ c ] = eq/ (a +B (b +B c)) ((a +B b) +B c) (0A ,
--                               (((a +B b) +B c) ≡⟨ sym (Module+Isasso {M = B} a b c) ⟩
--                                (a +B (b +B c)) ≡⟨ sym(ModuleZeroRight {M = B} (a +B (b +B c))) ⟩
--                                ((a +B (b +B c)) +B 0B) ≡⟨ cong (λ x → (a +B (b +B c)) +B x) (sym (
--                                                           ModuleHomomorphismPreserveZero f)) ⟩
--                               ((a +B (b +B c)) +B f' 0A) ∎))
--      AssocoK [ a ] [ b ] (eq/ c c' r i) = {!!}
--      AssocoK [ a ] [ b ] (squash/ c c' p q i j) = {!!}
--      AssocoK [ a ] (eq/ b b' r i) c = {!!}
--      AssocoK [ a ] (squash/ b b' p q i j) c = {!!}
--      AssocoK (eq/ a b₁ r i) b c = {!!}
--      AssocoK (squash/ a a₁ p q i i₁) b c = {!!}

--Bad attempt, but I don't know how to do excluding subsets without propositional logic...
--CoKRModTest : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} → (f : Precategory.hom (RModPreCat R) A B) → Type {!!}
--CoKRModTest {ℓ} R {A} {B} f = Σ (Type ℓ) λ B* → Σ B* (λ b* → Σ ⟨ B ⟩M (λ b → PathP _ b b*)) × (Σ B* (λ b0* → PathP _ b0* (Module.0m B))) × isContr (Σ B* (λ b* → Σ ⟨ A ⟩M λ a → PathP _ (ModuleHomomorphism.h f a) b*))

--**************************************************************** Monics are kernels ***********************************************************************

--monicsAreKernelsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B S : Precategory.ob (RModPreCat R)} → (k : Precategory.hom (RModPreCat R) S A) → isMonic C k →
--                       ∥ Σ (Precategory.hom (RModPreCat R) A B) (λ f → isKernel (RMod R) AbHasZero f k) ∥
--monicsAreKernelsRMod R k kMon = | |
