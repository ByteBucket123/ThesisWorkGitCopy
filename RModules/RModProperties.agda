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
open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import ThesisWork.RModules.CommutativeRing
open import Cubical.Algebra.Ring.Base
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
open import Cubical.Core.Primitives renaming
  (_[_≡_] to _[_≡_]P)

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.PropositionalTruncation.Base
open import ThesisWork.RModules.RModuleProperties
open import ThesisWork.SetQuotientHelp
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import Cubical.HITs.PropositionalTruncation.Properties renaming
  (elim to elimHprop ;
   elim2 to elim2Hprop ;
   elim3 to elim3Hprop ;
   rec to recHprop ;
   rec2 to rec2Hprop )

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Binary.Base

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

zeroModuleisInitialObject : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isInitialObject RMod (zeroModule R)
zeroModuleisInitialObject R M = h , FuncToZeroModuleIsProp M h
  where
    0M =  Module.0m M
    h = moduleHomo (λ x → 0M)
                   (λ x y → sym (ModuleZeroRight {M = M} 0M))
                   (λ r x → sym (ModuleMulPresZero {M = M} r))

zeroModuleisTerminalObject : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isTerminalObject RMod (zeroModule R)
zeroModuleisTerminalObject {ℓ} R M = h , λ k → ModuleHomo≡ (funExt (λ x → isPropOneElem * (ModuleHomomorphism.h k x)))
  where
    h = moduleHomo (λ x → *)
                   (λ x y → sym (ModuleZeroRight {M = zeroModule R} *))
                   (λ r x → sym (ModuleMulPresZero {M = zeroModule R} r))

hasZeroObjectRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasZeroObject (RMod {R = R})
hasZeroObjectRMod R = (zeroModule R) ,CatWithZero ((zeroModuleisInitialObject R) ,Zero (zeroModuleisTerminalObject R))

--******************************************** hasAllBinaryProducts (RMod R) ***********************************************

productOfModulesZero : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ M ⟩M × ⟨ N ⟩M
productOfModulesZero M N = Module.0m M , Module.0m N

productOfModules+ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x y : ⟨ M ⟩M × ⟨ N ⟩M) → ⟨ M ⟩M × ⟨ N ⟩M
productOfModules+ M N (x₁ , x₂) (y₁ , y₂) = ((M Module.+ x₁) y₁) , ((N Module.+ x₂) y₂)

productOfModules- : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ M ⟩M × ⟨ N ⟩M → ⟨ M ⟩M × ⟨ N ⟩M
productOfModules- M N (x₁ , x₂) = ((Module.- M) x₁) , ((Module.- N) x₂)

productOfModules⋆ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → ⟨ R ⟩ → ⟨ M ⟩M × ⟨ N ⟩M → ⟨ M ⟩M × ⟨ N ⟩M
productOfModules⋆ M N r (x₁ , x₂) = ((M Module.⋆ r) x₁) , ((N Module.⋆ r) x₂)

productOfModulesIsSet : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (⟨ M ⟩M × ⟨ N ⟩M)
productOfModulesIsSet M N = isSetΣ (isSetModule M) λ _ → isSetModule N

productOfModulesAsso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x y z : ⟨ M ⟩M × ⟨ N ⟩M) →
      productOfModules+ M N x (productOfModules+ M N y z) ≡
      productOfModules+ M N (productOfModules+ M N x y) z
productOfModulesAsso M N (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) = Σ≡ (Module+Isasso {M = M} x₁ y₁ z₁) (Module+Isasso {M = N} x₂ y₂ z₂)

productOfModulesZeroRight : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
                            (productOfModules+ M N x (productOfModulesZero M N) ≡ x)
productOfModulesZeroRight M N (x₁ , x₂) = Σ≡ (ModuleZeroRight {M = M} x₁) (ModuleZeroRight {M = N} x₂)

productOfModulesZeroLeft : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
                           (productOfModules+ M N (productOfModulesZero M N) x ≡ x)
productOfModulesZeroLeft M N (x₁ , x₂) = Σ≡ (ModuleZeroLeft {M = M} x₁) (ModuleZeroLeft {M = N} x₂)

productOfModulesInvRight : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
                           productOfModules+ M N x (productOfModules- M N x) ≡ productOfModulesZero M N
productOfModulesInvRight M N (x₁ , x₂) = Σ≡ (ModuleInvRight {M = M} x₁) (ModuleInvRight {M = N} x₂)

productOfModulesInvLeft : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) → 
                          productOfModules+ M N (productOfModules- M N x) x ≡ productOfModulesZero M N
productOfModulesInvLeft M N (x₁ , x₂) = Σ≡ (ModuleInvLeft {M = M} x₁) (ModuleInvLeft {M = N} x₂)

productOfModulesAb : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x y : ⟨ M ⟩M × ⟨ N ⟩M) → 
                     productOfModules+ M N x y ≡ productOfModules+ M N y x
productOfModulesAb M N (x₁ , x₂) (y₁ , y₂) = Σ≡ (ModuleIsAb {M = M} x₁ y₁) (ModuleIsAb {M = N} x₂ y₂)

productOfModules·Isasso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (r s : ⟨ R ⟩) →
                          (x : ⟨ M ⟩M × ⟨ N ⟩M) →
                          productOfModules⋆ M N (((snd R) CommutativeRingStr.· r) s) x ≡
                          productOfModules⋆ M N r (productOfModules⋆ M N s x)
productOfModules·Isasso M N r s (x₁ , x₂) = Σ≡ (Module·Isasso {M = M} r s x₁) (Module·Isasso {M = N} r s x₂)

productOfModulesLDist : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (r s : ⟨ R ⟩) →
                        (x : ⟨ M ⟩M × ⟨ N ⟩M) →
                        productOfModules⋆ M N (((snd R) CommutativeRingStr.+ r) s) x ≡
                        productOfModules+ M N (productOfModules⋆ M N r x) (productOfModules⋆ M N s x)
productOfModulesLDist M N r s (x₁ , x₂) = Σ≡ (ModuleLDist {M = M} r s x₁) (ModuleLDist {M = N} r s x₂)

productOfModulesRDist : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (r : ⟨ R ⟩) →
                        (x y : ⟨ M ⟩M × ⟨ N ⟩M) →
                        productOfModules⋆ M N r (productOfModules+ M N x y) ≡
                        productOfModules+ M N (productOfModules⋆ M N r x) (productOfModules⋆ M N r y)
productOfModulesRDist M N r (x₁ , x₂) (y₁ , y₂)= Σ≡ (ModuleRDist {M = M} r x₁ y₁) (ModuleRDist {M = N} r x₂ y₂)

productOfModulesLId : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → (x : ⟨ M ⟩M × ⟨ N ⟩M) →
                      productOfModules⋆ M N (CommutativeRingStr.1r (snd R)) x ≡ x
productOfModulesLId  M N (x₁ , x₂) = Σ≡ (ModuleLId {M = M} x₁) (ModuleLId {M = N} x₂)

productOfModules : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → Module R
productOfModules M N =
  moduleConst
    (⟨ M ⟩M × ⟨ N ⟩M)
    (productOfModulesZero M N)
    (productOfModules+ M N)
    (productOfModules- M N)
    (productOfModules⋆ M N)
    (isModule
      (ismodule
        (isabgroup
          (isgroup
            (ismonoid
              (issemigroup
                (productOfModulesIsSet M N)
                (productOfModulesAsso M N))
              λ x → (productOfModulesZeroRight M N x) , (productOfModulesZeroLeft M N x))
              λ x → productOfModulesInvRight M N x , productOfModulesInvLeft M N x)
        (productOfModulesAb M N))
        (productOfModules·Isasso M N)
        (productOfModulesLDist M N)
        (productOfModulesRDist M N)
        (productOfModulesLId M N)))

prodHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N Z : Module R} → ModuleHomomorphism R Z M → ModuleHomomorphism R Z N
           → ModuleHomomorphism R Z (productOfModules M N)
prodHomo h k = moduleHomo (λ z → (ModuleHomomorphism.h h z) , (ModuleHomomorphism.h k z))
  (λ x y → Σ≡ (ModuleHomomorphism.linear h x y) (ModuleHomomorphism.linear k x y))
  (λ r x → Σ≡ (ModuleHomomorphism.scalar h r x) (ModuleHomomorphism.scalar k r x))

ProductIsBinaryProduct : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A B : Precategory.ob (UnivalentCategory.cat (RMod {R = R}))) →
                         isBinaryProduct (RMod {R = R}) A B (productOfModules A B)
ProductIsBinaryProduct R A B =
  ∣ ((BinProd A×B
              fstHomo
              sndHomo
              prodHomo
              (λ f g → ModuleHomo≡ refl)
              (λ f g → ModuleHomo≡ refl)
              λ f g h fsth=f sndh=g →
                ModuleHomo≡ (funExt (λ x → Σ≡
                  (sym λ i → ModuleHomomorphism.h (fsth=f i) x)
                  (sym (λ i → ModuleHomomorphism.h (sndh=g i) x))))) ,
     refl) ∣
  where
   A×B = productOfModules A B
   fstHomo = moduleHomo fst (λ x y → refl) λ r x → refl
   sndHomo = moduleHomo snd (λ x y → refl) λ r x → refl

hasAllBinaryProductsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllBinaryProducts (RMod {R = R})
hasAllBinaryProductsRMod R A B = ∣ ((productOfModules A B) , (ProductIsBinaryProduct R A B)) ∣

--******************************************** hasAllBinaryCoProducts (RMod R) ***********************************************

coProdHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N Z : Module R} → ModuleHomomorphism R M Z → ModuleHomomorphism R N Z
           → ModuleHomomorphism R (productOfModules M N) Z
coProdHomo {R = R} {M = M} {N = N} {Z = Z} h k =
  moduleHomo (λ (a , b) → (f a) +Z (g b))
             (λ (x₁ , x₂) (y₁ , y₂) →
               (f (x₁ +M y₁) +Z g (x₂ +N y₂))                 ≡⟨ cong (λ x → x +Z g (x₂ +N y₂))
                                                                   (ModuleHomomorphism.linear h x₁ y₁) ⟩
               (((f x₁) +Z (f y₁)) +Z g (x₂ +N y₂))           ≡⟨ cong (λ x → ((f x₁) +Z (f y₁)) +Z x)
                                                                   (ModuleHomomorphism.linear k x₂ y₂) ⟩
               (((f x₁) +Z (f y₁)) +Z (g x₂ +Z g y₂))         ≡⟨ sym (assoZ (f x₁) (f y₁) (g x₂ +Z g y₂)) ⟩
               ((f x₁) +Z ((f y₁) +Z (g x₂ +Z g y₂)))         ≡⟨ cong (λ x → (f x₁) +Z x) (assoZ (f y₁) (g x₂) (g y₂)) ⟩
               (((f x₁) +Z (((f y₁) +Z (g x₂)) +Z g y₂)))     ≡⟨ cong (λ x → f x₁ +Z (x +Z g y₂)) (comm+Z (f y₁) (g x₂)) ⟩
               ((((f x₁) +Z (((g x₂) +Z (f y₁)) +Z g y₂))))   ≡⟨ cong (λ x → f x₁ +Z x) (sym (assoZ (g x₂) (f y₁) (g y₂))) ⟩
               (((((f x₁) +Z ((g x₂) +Z ((f y₁) +Z g y₂)))))) ≡⟨ assoZ (f x₁) (g x₂) ((f y₁) +Z (g y₂)) ⟩
               ((f x₁ +Z g x₂) +Z ((f y₁) +Z (g y₂))) ∎)
             λ r (x₁ , x₂) →
               ((f (r ⋆M x₁)) +Z g (r ⋆N x₂))   ≡⟨ cong (λ x → x +Z g (r ⋆N x₂)) (ModuleHomomorphism.scalar h r x₁) ⟩
               ((r ⋆Z (f x₁)) +Z g (r ⋆N x₂))   ≡⟨ cong (λ x → (r ⋆Z (f x₁)) +Z  x) (ModuleHomomorphism.scalar k r x₂) ⟩
               ((r ⋆Z (f x₁)) +Z (r ⋆Z (g x₂))) ≡⟨ sym (ModuleRDist {M = Z} r (f x₁) (g x₂)) ⟩
               (r ⋆Z ((f x₁) +Z (g x₂))) ∎
   where
     _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
     x +M y = (M Module.+ x) y
     _+N_ : ⟨ N ⟩M → ⟨ N ⟩M → ⟨ N ⟩M
     x +N y = (N Module.+ x) y
     _+Z_ : ⟨ Z ⟩M → ⟨ Z ⟩M → ⟨ Z ⟩M
     x +Z y = (Z Module.+ x) y
     _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
     r ⋆M x = (M Module.⋆ r) x
     _⋆N_ : ⟨ R ⟩ → ⟨ N ⟩M → ⟨ N ⟩M
     r ⋆N x = (N Module.⋆ r) x
     _⋆Z_ : ⟨ R ⟩ → ⟨ Z ⟩M → ⟨ Z ⟩M
     r ⋆Z x = (Z Module.⋆ r) x
     f = ModuleHomomorphism.h h
     g = ModuleHomomorphism.h k
     assoZ = Module+Isasso {M = Z}
     comm+Z = ModuleIsAb {M = Z}

-- --moduleHomo (λ z → (ModuleHomomorphism.h h z) , (ModuleHomomorphism.h k z))
-- --  (λ x y → Σ≡ (ModuleHomomorphism.linear h x y) (ModuleHomomorphism.linear k x y))
-- --  (λ r x → Σ≡ (ModuleHomomorphism.scalar h r x) (ModuleHomomorphism.scalar k r x))

HelpCoProdUnique : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N Z : Module R} → (k : ModuleHomomorphism R M Z) →
                   (u : ModuleHomomorphism R N Z) → (h : ModuleHomomorphism R (productOfModules M N) Z) →
                   (λ a → ModuleHomomorphism.h h (a , Module.0m N)) ≡ ModuleHomomorphism.h k →
                   (λ b → ModuleHomomorphism.h h (Module.0m M , b)) ≡ ModuleHomomorphism.h u →
                   (λ a → ModuleHomomorphism.h (coProdHomo k u) (a , Module.0m N)) ≡ ModuleHomomorphism.h k →
                   (λ b → ModuleHomomorphism.h (coProdHomo k u) (Module.0m M , b)) ≡ ModuleHomomorphism.h u →
                   coProdHomo k u ≡ h
HelpCoProdUnique {M = M} {N = N} {Z = Z} k u h ha0=k h0b=u f×ga0=k f×g0b=u =
  ModuleHomo≡ (funExt (λ x →
    f×g x                          ≡⟨ cong f×g (Σ≡ (sym (ModuleZeroRight {M = M} (fst x)))
                                                   (sym (ModuleZeroLeft {M = N} (snd x)))) ⟩
    f×g (pA x +P pB x)             ≡⟨ ModuleHomomorphism.linear (coProdHomo k u) (pA x) (pB x) ⟩
    ((f×g (pA x)) +Z (f×g (pB x))) ≡⟨ cong₂ _+Z_ (funExt⁻ f×ga0=k (fst x) ∙ sym (funExt⁻ ha0=k (fst x)))
                                                 ((funExt⁻ f×g0b=u (snd x)) ∙ (sym (funExt⁻ h0b=u (snd x)))) ⟩
    ((h' (pA x)) +Z (h' (pB x)))   ≡⟨ sym (ModuleHomomorphism.linear h (pA x) (pB x)) ⟩
    h' ((pA x) +P (pB x))          ≡⟨ cong h' (Σ≡ (ModuleZeroRight {M = M} (fst x)) (ModuleZeroLeft {M = N} (snd x))) ⟩
    h' x ∎))
      where
        f = ModuleHomomorphism.h k
        g = ModuleHomomorphism.h u
        h' = ModuleHomomorphism.h h
        f×g = ModuleHomomorphism.h (coProdHomo k u)
        _+P_ : ⟨ productOfModules M N ⟩M → ⟨ productOfModules M N ⟩M → ⟨ productOfModules M N ⟩M
        x +P y = (productOfModules M N Module.+ x) y
        _+Z_ : ⟨ Z ⟩M → ⟨ Z ⟩M → ⟨ Z ⟩M
        x +Z y = (Z Module.+ x) y
        pA : (x : ⟨ productOfModules M N ⟩M) → ⟨ productOfModules M N ⟩M
        pA x = fst x , Module.0m N
        pB : (x : ⟨ productOfModules M N ⟩M) → ⟨ productOfModules M N ⟩M
        pB x = Module.0m M , snd x

-- --    uni : {Z : Precategory.ob (UnivalentCategory.cat C)} → (f : Precategory.hom (UnivalentCategory.cat C) A Z) →
-- --          (g : Precategory.hom (UnivalentCategory.cat C) B Z) → (h : Precategory.hom (UnivalentCategory.cat C) A×B Z) →
-- --          Precategory.seq (UnivalentCategory.cat C) pA h ≡ f → Precategory.seq (UnivalentCategory.cat C) pB h ≡ g →
-- --          < f × g > ≡ h

ProductIsBinaryCoProduct : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A B : Precategory.ob (UnivalentCategory.cat (RMod {R = R}))) →
                           isBinaryCoProduct RMod A B (productOfModules A B)
ProductIsBinaryCoProduct R A B =
  ∣ (BinCoProd A×B pA pB coProdHomo pAcomp pBcomp 
      λ k u h ha0=k h0b=u →
        HelpCoProdUnique k u h (λ i → ModuleHomomorphism.h (ha0=k i))
                               (λ i → ModuleHomomorphism.h (h0b=u i))
                               (λ i → ModuleHomomorphism.h (pAcomp k u i))
                                λ i → ModuleHomomorphism.h (pBcomp k u i)) ,
    refl ∣
    where
      A×B = productOfModules A B
      pA : ModuleHomomorphism R A A×B
      pA = moduleHomo (λ x → x , (Module.0m B))
                      (λ x y → sym (Σ≡ refl (ModuleZeroRight {M = B} (Module.0m B))))
                      λ r x → sym (Σ≡ refl (ModuleMulPresZero {M = B} r)) 
      pB : ModuleHomomorphism R B A×B
      pB = moduleHomo (λ x → (Module.0m A) , x)
                      (λ x y → Σ≡ (sym (ModuleZeroRight {M = A} (Module.0m A))) refl)
                      λ r x → Σ≡ (sym (ModuleMulPresZero {M = A} r)) refl
      pAcomp : {Z : Module R} → (f : ModuleHomomorphism R A Z) → (g : ModuleHomomorphism R B Z) →
               ModuleHomoComp pA (coProdHomo f g) ≡ f
      pAcomp f g = ModuleHomo≡ (funExt (λ x → ModuleHomomorphismAddHomZero x f g))
      pBcomp : {Z : Module R} → (f : ModuleHomomorphism R A Z) → (g : ModuleHomomorphism R B Z) →
               ModuleHomoComp pB (coProdHomo f g) ≡ g
      pBcomp f g = ModuleHomo≡ (funExt (λ x → ModuleHomomorphismAddHomZeroSym x f g))

hasAllBinaryCoProductsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllBinaryCoProducts (RMod {R = R})
hasAllBinaryCoProductsRMod R A B = ∣ (productOfModules A B) , ProductIsBinaryCoProduct R A B  ∣


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
      
hasAllKernelsRMod  : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllKernels (RMod {R = R}) (hasZeroObjectRMod R)
hasAllKernelsRMod R {A} {B} f =
  ∣ ((makeKernelObjRMod R f) ,
      (kernelConst fstHomo
        (ModuleHomo≡ (funExt snd))
        (λ h hf=0 →
          (moduleHomo (λ x → (ModuleHomomorphism.h h x) , λ i → ModuleHomomorphism.h (hf=0 i) x)
                      (λ x y → HelpFiber≡ (isSetModule B) (ModuleHomomorphism.linear h x y))
                       λ r x → HelpFiber≡ (isSetModule B) (ModuleHomomorphism.scalar h r x)) ,
            ModuleHomo≡ refl)
        λ D g h gker=hker → ModuleHomo≡ (funExt (λ x → HelpFiber≡ (isSetModule B)
          (funExt⁻ (λ i → ModuleHomomorphism.h (gker=hker i)) x))))) ∣
    where
      fstHomo = moduleHomo fst (λ x y → refl) λ r x → refl
--      sndHomo = moduleHomo snd (λ x y → refl) λ r x → refl
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

--MonicToInj : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
--             (f : Precategory.hom (RModPreCat R) A B) → (isMonic (RMod {R = R}) f) → (a a' : ⟨ A ⟩M) →
--             ModuleHomomorphism.h f a ≡ ModuleHomomorphism.h f a' → a ≡ a'
--MonicToInj R {A} {B} f monf a a' fa=fa' =
--  a ≡⟨ idaa' ⟩
--  a' ∎
--  where
--    f' = ModuleHomomorphism.h f
--    id = Precategory.idn (RModPreCat R)
--    idaa' : ModuleHomomorphism.h (id A) a ≡ ModuleHomomorphism.h (id A) a'
--    idaa' =
--      ModuleHomomorphism.h (id A) a ≡⟨ {!!} ⟩
--      ModuleHomomorphism.h (id A) a' ∎

--coKernelRelMonicProp : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
--                      (f : Precategory.hom (RModPreCat R) A B) → (isMonic (RMod {R = R}) f) → (b b' : ⟨ B ⟩M) →
--                      isProp (coKernelRel R f b b')
--coKernelRelMonicProp = {!!}

coKernelRelisEquiv : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
                     (f : Precategory.hom (RModPreCat R) A B) → BinaryRelation.isEquivRel (coKernelRel R f)
coKernelRelisEquiv R {A} {B} f =
  BinaryRelation.equivRel (λ b →
                             0A , (b        ≡⟨ sym (ModuleZeroRight {M = B} b) ⟩
                                  (b +B 0B) ≡⟨ cong (λ x → b +B x) (sym (ModuleHomomorphismPreserveZero f)) ⟩
                                  (b +B f' 0A) ∎))
                          (λ b b' (a , b'=b+fa) →
                            (-A a) , (b                         ≡⟨ sym (ModuleZeroRight {M = B} b) ⟩
                                     (b +B 0B)                  ≡⟨ cong (λ x → b +B x) (sym (ModuleInvRight {M = B} (f' a))) ⟩
                                     (b +B (f' a +B (-B f' a))) ≡⟨ Module+Isasso {M = B} b (f' a) (-B (f' a)) ⟩
                                     ((b +B f' a) +B (-B f' a)) ≡⟨ cong₂ (λ x y → x +B y) (sym b'=b+fa) (sym (ModuleHomomorphismLinSub a f)) ⟩
                                     (b' +B f' (-A a)) ∎))
                          λ b b' b'' (a , b'=b+fa) (a' , b''=b'+fa') →
                            (a +A a') , (b''                   ≡⟨ b''=b'+fa' ⟩
                                        (b' +B f' a')          ≡⟨ cong (λ x → x +B f' a') b'=b+fa ⟩
                                        ((b +B f' a) +B f' a') ≡⟨ sym (Module+Isasso {M = B} b (f' a) (f' a')) ⟩
                                        (b +B (f' a +B f' a')) ≡⟨ cong (λ x → b +B x) (sym (ModuleHomomorphism.linear f a a')) ⟩
                                        (b +B f' (a +A a')) ∎)
  where
    f' = ModuleHomomorphism.h f
    0A = Module.0m A
    0B = Module.0m B
    _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
    x +A y = (A Module.+ x) y
    _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
    x +B y = (B Module.+ x) y
    -A_ : ⟨ A ⟩M → ⟨ A ⟩M
    -A x = (Module.- A) x
    -B_ : ⟨ B ⟩M → ⟨ B ⟩M
    -B x = (Module.- B) x


coKernelPropRelisEquiv : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
                     (f : Precategory.hom (RModPreCat R) A B) → BinaryRelation.isEquivRel (coKernelPropRel R f)
coKernelPropRelisEquiv R {A} {B} f =
  BinaryRelation.equivRel (λ x → ∣ (BinaryRelation.isEquivRel.reflexive (coKernelRelisEquiv R f) x) ∣)
                          (λ x y → map (BinaryRelation.isEquivRel.symmetric (coKernelRelisEquiv R f) x y) )
                          λ x y z → map2 (BinaryRelation.isEquivRel.transitive (coKernelRelisEquiv R f) x y z)

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
              AssocoK)
              add0coK)
          addInvcoK)
        abcoK)
      multAssoccoK
      LDistcoK
      RDistcoK
      LIdcoK))
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
      _+R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
      r +R s = (snd (CommutativeRing→Ring R) RingStr.+ r) s
      _·R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
      r ·R s = (snd (CommutativeRing→Ring R) RingStr.· r) s
      1R = RingStr.1r (snd (CommutativeRing→Ring R))
      
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
                      (λ a b c d r → toPathP (squash/ _ _ _ _))
                      (λ a b c d r → toPathP (squash/ _ _ _ _))
                      λ a b c d r → toPathP (squash/ _ _ _ _)

      add0coK : (x : coKObj) → ((x +coK 0coK) ≡ x) × ((0coK +coK x) ≡ x)
      add0coK x = (elim {B = λ x → x +coK 0coK ≡ x}
                     (λ y → isProp→isSet (squash/ _ _))
                     (λ b → eq/ _ _ (0A ,
                       (b        ≡⟨ sym (ModuleZeroRight {M = B} b) ⟩
                       (b +B 0B) ≡⟨ cong₂ (λ x y → x +B y) (sym (ModuleZeroRight {M = B} b))
                         (sym (ModuleHomomorphismPreserveZero f)) ⟩
                       ((b +B 0B) +B f' 0A ) ∎)))
                     (λ a b r → toPathP (squash/ _ _ _ _)) x) ,
                  elim {B = λ x → 0coK +coK x ≡ x}
                    (λ y → isProp→isSet (squash/ _ _))
                    (λ b → eq/ _ _ (0A ,
                      (b        ≡⟨ sym (ModuleZeroRight {M = B} b) ⟩
                      (b +B 0B) ≡⟨ cong₂ _+B_ (sym (ModuleZeroLeft {M = B} b))
                        (sym (ModuleHomomorphismPreserveZero f)) ⟩
                      ((0B +B b) +B f' 0A) ∎)))
                    (λ a b r → toPathP (squash/ _ _ _ _)) x

      addInvcoK : (x : coKObj) → ((x +coK (-coK x)) ≡ 0coK) × (((-coK x) +coK x) ≡ 0coK)
      addInvcoK x = elim {B = λ x → x +coK (-coK x) ≡ 0coK}
                      (λ y → isProp→isSet (squash/ _ _))
                      (λ b → eq/ _ _ (0A ,
                        (0B        ≡⟨ sym (ModuleZeroRight {M = B} 0B) ⟩
                        (0B +B 0B) ≡⟨ cong₂ _+B_ (sym (ModuleInvRight {M = B} b))
                          (sym (ModuleHomomorphismPreserveZero f)) ⟩
                        ((b +B (-B b)) +B f' 0A) ∎)))
                      (λ a b r → toPathP (squash/ _ _ _ _)) x ,
                    elim {B = λ x → (-coK x) +coK x ≡ 0coK}
                      (λ y → isProp→isSet (squash/ _ _))
                      (λ b → eq/ _ _ (0A ,
                        (0B        ≡⟨ sym (ModuleZeroRight {M = B} 0B) ⟩
                        (0B +B 0B) ≡⟨ cong₂ _+B_ (sym (ModuleInvLeft {M = B} b))
                          (sym (ModuleHomomorphismPreserveZero f)) ⟩
                        (((-B b) +B b) +B f' 0A) ∎)))
                      (λ a b r → toPathP (squash/ _ _ _ _)) x

      abcoK : (x y : coKObj) → (x +coK y) ≡ (y +coK x)
      abcoK x y = elim2 {B = λ x y → x +coK y ≡ y +coK x}
                             (λ x y → isProp→isSet (squash/ _ _))
                             (λ a b → eq/ _ _ (0A ,
                               ((b +B a)        ≡⟨ sym (ModuleZeroRight {M = B} (b +B a)) ⟩
                               ((b +B a) +B 0B) ≡⟨ cong₂ _+B_ (ModuleIsAb {M = B} b a) (sym (ModuleHomomorphismPreserveZero f)) ⟩
                               ((a +B b) +B f' 0A) ∎)))
                             (λ a b c r → toPathP (squash/ _ _ _ _))
                             (λ a b c r → toPathP (squash/ _ _ _ _)) x y

      multAssoccoK : (r s : ⟨ CommutativeRing→Ring R ⟩) → (x : coKObj) →
                      ((r ·R s) ⋆coK x) ≡ (r ⋆coK (s ⋆coK x))
      multAssoccoK r s = elim (λ x → isProp→isSet (squash/ _ _))
                              (λ b → eq/ _ _ (0A ,
                                ((r ⋆B (s ⋆B b))        ≡⟨ sym (ModuleZeroRight {M = B} ((r ⋆B (s ⋆B b)))) ⟩
                                ((r ⋆B (s ⋆B b)) +B 0B) ≡⟨ cong₂ _+B_ (sym (Module·Isasso {M = B} r s b))
                                  (sym (ModuleHomomorphismPreserveZero f)) ⟩
                                (((r ·R s) ⋆B b) +B f' 0A) ∎)))
                              λ a b r → toPathP (squash/ _ _ _ _)

      LDistcoK : (r s : ⟨ CommutativeRing→Ring R ⟩) → (x : coKObj) →
                   ((r +R s) ⋆coK x) ≡ ((r ⋆coK x) +coK (s ⋆coK x))
      LDistcoK r s = elim (λ x → isProp→isSet (squash/ _ _))
                          (λ b → eq/ _ _ (0A ,
                            (((r ⋆B b) +B (s ⋆B b))        ≡⟨ sym (ModuleZeroRight {M = B} ((r ⋆B b) +B (s ⋆B b))) ⟩
                            (((r ⋆B b) +B (s ⋆B b)) +B 0B) ≡⟨ cong₂ _+B_
                              (sym (ModuleLDist {M = B} r s b))
                              (sym (ModuleHomomorphismPreserveZero f)) ⟩
                            (((r +R s) ⋆B b) +B (f' 0A)) ∎)))
                          λ a b r → toPathP (squash/ _ _ _ _)

      RDistcoK : (r : ⟨ CommutativeRing→Ring R ⟩) (x y : coKObj) → (r ⋆coK (x +coK y)) ≡ ((r ⋆coK x) +coK (r ⋆coK y))
      RDistcoK r = elim2 (λ x y → isProp→isSet (squash/ _ _))
                         (λ a b → eq/ _ _ (0A ,
                           (((r ⋆B a) +B (r ⋆B b))        ≡⟨ sym (ModuleZeroRight {M = B} ((r ⋆B a) +B (r ⋆B b))) ⟩
                           (((r ⋆B a) +B (r ⋆B b)) +B 0B) ≡⟨ cong₂ _+B_ (sym (ModuleRDist {M = B} r a b))
                             (sym (ModuleHomomorphismPreserveZero f)) ⟩
                           ((r ⋆B (a +B b)) +B f' 0A) ∎)))
                         (λ a b c r → toPathP (squash/ _ _ _ _))
                          λ a b c r → toPathP (squash/ _ _ _ _)

      LIdcoK : (x : coKObj) → (RingStr.1r (snd (CommutativeRing→Ring R)) ⋆coK x) ≡ x
      LIdcoK = elim (λ x → isProp→isSet (squash/ _ _))
                    (λ a → eq/ _ _ (0A ,
                      (a        ≡⟨ sym (ModuleZeroRight {M = B} a) ⟩
                      (a +B 0B) ≡⟨ cong₂ _+B_ (sym (ModuleLId {M = B} a))
                        (sym (ModuleHomomorphismPreserveZero f)) ⟩
                      ((1R ⋆B a) +B f' 0A) ∎)))
                     λ a b r → toPathP (squash/ _ _ _ _)

hasAllCoKernelsRMod  : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllCoKernels (RMod {R = R}) (hasZeroObjectRMod R)
hasAllCoKernelsRMod R {A} {B} f =
  ∣ (makeCoKernelObjRMod R f) ,
    coKernelConst incHomo
                  (ModuleHomo≡ (funExt (λ x → eq/ _ _ ((-A x) ,
                    (0B              ≡⟨ sym (ModuleHomomorphismPreserveZero f) ⟩
                    f' 0A            ≡⟨ cong f' (sym (ModuleInvRight {M = A} x)) ⟩
                    f' (x +A (-A x)) ≡⟨ ModuleHomomorphism.linear f x (-A x) ⟩
                    (f' x +B f' (-A x)) ∎)))))
                  (λ {D} h fh=0 →
                    (moduleHomo (rec (isSetModule D) (ModuleHomomorphism.h h)
                                  (λ a b r →
                                    ModuleHomomorphism.h h a
                                      ≡⟨ sym (ModuleZeroRight {M = D} (ModuleHomomorphism.h h a)) ⟩
                                    (D Module.+ (ModuleHomomorphism.h h a)) (Module.0m D)
                                      ≡⟨ cong (D Module.+ (ModuleHomomorphism.h h a)) (
                                        sym (λ i → ModuleHomomorphism.h (fh=0 i) (fst r))) ⟩
                                    (D Module.+ (ModuleHomomorphism.h h a)) (ModuleHomomorphism.h h (f' (fst r)))
                                      ≡⟨ sym (ModuleHomomorphism.linear h a (f' (fst r))) ⟩
                                    ModuleHomomorphism.h h (a +B f' (fst r))
                                      ≡⟨ cong (ModuleHomomorphism.h h) (sym (snd r)) ⟩
                                    ModuleHomomorphism.h h b ∎))
                                (elim2 (λ x y → isProp→isSet (isSetModule D _ _))
                                       (ModuleHomomorphism.linear h)
                                       (λ a b c r → toPathP (isSetModule D _ _ _ _))
                                        λ a b c r → toPathP (isSetModule D _ _ _ _))
                                λ r → elim (λ x → isProp→isSet (isSetModule D _ _))
                                           (ModuleHomomorphism.scalar h r)
                                           λ a b r → toPathP (isSetModule D _ _ _ _)) ,
                    ModuleHomo≡ (funExt (λ x → refl)))
                  (λ D h g inch=incg → ModuleHomo≡ (funExt (elim (λ x → isProp→isSet (isSetModule D _ _))
                                                            (λ a → λ i → ModuleHomomorphism.h (inch=incg i) a)
                                                            λ a b r → toPathP (isSetModule D _ _ _ _)))) ∣
  where
    f' = ModuleHomomorphism.h f
    0A = Module.0m A
    0B = Module.0m B
    _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
    x +B y = (B Module.+ x) y
    _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
    x +A y = (A Module.+ x) y
    -A_ : ⟨ A ⟩M → ⟨ A ⟩M
    -A x = (Module.- A) x
    -B_ : ⟨ B ⟩M → ⟨ B ⟩M
    -B x = (Module.- B) x
    _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
    r ⋆B a = (B Module.⋆ r) a 
    _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
    r ⋆A a = (A Module.⋆ r) a
    _+R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
    r +R s = (snd (CommutativeRing→Ring R) RingStr.+ r) s
    _·R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
    r ·R s = (snd (CommutativeRing→Ring R) RingStr.· r) s
    1R = RingStr.1r (snd (CommutativeRing→Ring R))

    incHomo : ModuleHomomorphism R B (makeCoKernelObjRMod R f)
    incHomo =
      moduleHomo [_]
                 (λ x y → eq/ _ _ (0A ,
                   ((x +B y)        ≡⟨ sym (ModuleZeroRight {M = B} (x +B y)) ⟩
                   ((x +B y) +B 0B) ≡⟨ cong (λ z → (x +B y) +B z) (sym (ModuleHomomorphismPreserveZero f)) ⟩
                   ((x +B y) +B (f' 0A)) ∎)))
                  λ r x → eq/ _ _ (0A ,
                    ((r ⋆B x)        ≡⟨ sym (ModuleZeroRight {M = B} (r ⋆B x)) ⟩
                    ((r ⋆B x) +B 0B) ≡⟨ cong (λ z → (r ⋆B x) +B z) (sym (ModuleHomomorphismPreserveZero f)) ⟩
                    ((r ⋆B x) +B (f' 0A)) ∎))

--TODO : FIX
hasAllCoKernelsRModNonTrunk  : {ℓ : Level} → (R : CommutativeRing {ℓ}) →
                               {A B : Precategory.ob (RModPreCat R)} → (f : Precategory.hom (RModPreCat R) A B) →
                               Σ (Precategory.ob (RModPreCat R)) (λ S → CoKernel (RMod {R = R}) {S = S} (hasZeroObjectRMod R) f)
hasAllCoKernelsRModNonTrunk R {A} {B} f =
  (makeCoKernelObjRMod R f) ,
    coKernelConst incHomo
                  (ModuleHomo≡ (funExt (λ x → eq/ _ _ ((-A x) ,
                    (0B              ≡⟨ sym (ModuleHomomorphismPreserveZero f) ⟩
                    f' 0A            ≡⟨ cong f' (sym (ModuleInvRight {M = A} x)) ⟩
                    f' (x +A (-A x)) ≡⟨ ModuleHomomorphism.linear f x (-A x) ⟩
                    (f' x +B f' (-A x)) ∎)))))
                  (λ {D} h fh=0 →
                    (moduleHomo (rec (isSetModule D) (ModuleHomomorphism.h h)
                                  (λ a b r →
                                    ModuleHomomorphism.h h a
                                      ≡⟨ sym (ModuleZeroRight {M = D} (ModuleHomomorphism.h h a)) ⟩
                                    (D Module.+ (ModuleHomomorphism.h h a)) (Module.0m D)
                                      ≡⟨ cong (D Module.+ (ModuleHomomorphism.h h a)) (
                                        sym (λ i → ModuleHomomorphism.h (fh=0 i) (fst r))) ⟩
                                    (D Module.+ (ModuleHomomorphism.h h a)) (ModuleHomomorphism.h h (f' (fst r)))
                                      ≡⟨ sym (ModuleHomomorphism.linear h a (f' (fst r))) ⟩
                                    ModuleHomomorphism.h h (a +B f' (fst r))
                                      ≡⟨ cong (ModuleHomomorphism.h h) (sym (snd r)) ⟩
                                    ModuleHomomorphism.h h b ∎))
                                (elim2 (λ x y → isProp→isSet (isSetModule D _ _))
                                       (ModuleHomomorphism.linear h)
                                       (λ a b c r → toPathP (isSetModule D _ _ _ _))
                                        λ a b c r → toPathP (isSetModule D _ _ _ _))
                                λ r → elim (λ x → isProp→isSet (isSetModule D _ _))
                                           (ModuleHomomorphism.scalar h r)
                                           λ a b r → toPathP (isSetModule D _ _ _ _)) ,
                    ModuleHomo≡ (funExt (λ x → refl)))
                  (λ D h g inch=incg → ModuleHomo≡ (funExt (elim (λ x → isProp→isSet (isSetModule D _ _))
                                                            (λ a → λ i → ModuleHomomorphism.h (inch=incg i) a)
                                                            λ a b r → toPathP (isSetModule D _ _ _ _))))
  where
    f' = ModuleHomomorphism.h f
    0A = Module.0m A
    0B = Module.0m B
    _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
    x +B y = (B Module.+ x) y
    _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
    x +A y = (A Module.+ x) y
    -A_ : ⟨ A ⟩M → ⟨ A ⟩M
    -A x = (Module.- A) x
    -B_ : ⟨ B ⟩M → ⟨ B ⟩M
    -B x = (Module.- B) x
    _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
    r ⋆B a = (B Module.⋆ r) a 
    _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
    r ⋆A a = (A Module.⋆ r) a
    _+R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
    r +R s = (snd (CommutativeRing→Ring R) RingStr.+ r) s
    _·R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
    r ·R s = (snd (CommutativeRing→Ring R) RingStr.· r) s
    1R = RingStr.1r (snd (CommutativeRing→Ring R))

    incHomo : ModuleHomomorphism R B (makeCoKernelObjRMod R f)
    incHomo =
      moduleHomo [_]
                 (λ x y → eq/ _ _ (0A ,
                   ((x +B y)        ≡⟨ sym (ModuleZeroRight {M = B} (x +B y)) ⟩
                   ((x +B y) +B 0B) ≡⟨ cong (λ z → (x +B y) +B z) (sym (ModuleHomomorphismPreserveZero f)) ⟩
                   ((x +B y) +B (f' 0A)) ∎)))
                  λ r x → eq/ _ _ (0A ,
                    ((r ⋆B x)        ≡⟨ sym (ModuleZeroRight {M = B} (r ⋆B x)) ⟩
                    ((r ⋆B x) +B 0B) ≡⟨ cong (λ z → (r ⋆B x) +B z) (sym (ModuleHomomorphismPreserveZero f)) ⟩
                    ((r ⋆B x) +B (f' 0A)) ∎))

--**************************************************************** Monics are kernels ***********************************************************************

PostCompMonicPreserveKernel : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} →
                              {A B S D : Precategory.ob (UnivalentCategory.cat C)} →
                              (k : Precategory.hom (UnivalentCategory.cat C) S A) →
                              (f : Precategory.hom (UnivalentCategory.cat C) A B) →
                              (m : Precategory.hom (UnivalentCategory.cat C) B D) →
                              (hasZero : hasZeroObject C) →
                              isMonic C m → isKernel C hasZero f k →
                              isKernel C hasZero (Precategory.seq (UnivalentCategory.cat C) f m) k
PostCompMonicPreserveKernel {C = C} {A} {B} {S} {D} k f m hasZero mMon kfKer =
  kernelConst k
              ((k ∘ (f ∘ m)) ≡⟨ sym (Precategory.seq-α (UnivalentCategory.cat C) k f m) ⟩
              ((k ∘ f) ∘ m)  ≡⟨ cong (λ x → x ∘ m) ((cong (λ x → x ∘ f) (sym (snd kfKer))) ∙
                                                    Kernel.kerComp (fst kfKer)) ⟩
              ((0a S B) ∘ m) ≡⟨ ZeroArrowCompRight C hasZero m ⟩
              0a S D ∎)
              (λ {E} h hfm=0 →
                transport (cong (λ x → Σ (Precategory.hom (UnivalentCategory.cat C) E S)
                                         (λ h' → Precategory.seq (UnivalentCategory.cat C) h' x ≡ h))
                          (snd kfKer))
                          (Kernel.kerFactors (fst kfKer) h
                            (mMon E (Precategory.seq (UnivalentCategory.cat C) h f) (0a E B)
                              (((h ∘ f) ∘ m) ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) h f m ⟩
                              (h ∘ (f ∘ m))  ≡⟨ hfm=0 ⟩
                              0a E D         ≡⟨ sym (ZeroArrowCompRight C hasZero m) ⟩
                              ((0a E B) ∘ m) ∎))))
              (transport (cong (isMonic C) (snd kfKer)) (Kernel.kerFactorsUnique (fst kfKer))) ,
  refl
    where
      _∘_ : {A B D : Precategory.ob (UnivalentCategory.cat C)} → Precategory.hom (UnivalentCategory.cat C) A B →
            Precategory.hom (UnivalentCategory.cat C) B D → Precategory.hom (UnivalentCategory.cat C) A D
      f ∘ g = Precategory.seq (UnivalentCategory.cat C) f g
      0a : (A B : Precategory.ob (UnivalentCategory.cat C))  → Precategory.hom (UnivalentCategory.cat C) A B
      0a A B = ZeroArrow.f (getZeroArrow C {A = A} {B = B} hasZero)

PostcompIsoPreserveKernel : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} →
                            {A B S A' : Precategory.ob (UnivalentCategory.cat C)} →
                            (k : Precategory.hom (UnivalentCategory.cat C) S A) →
                            (f : Precategory.hom (UnivalentCategory.cat C) A B) →
                            (catIso : CatIso {C = UnivalentCategory.cat C} A A') → 
                            (hasZero : hasZeroObject C) → isKernel C hasZero f k →
                            isKernel C hasZero (Precategory.seq (UnivalentCategory.cat C) (CatIso.h⁻¹ catIso) f)
                                               (Precategory.seq (UnivalentCategory.cat C) k (CatIso.h catIso))
PostcompIsoPreserveKernel {C = C} {A} {B} {S} {A'} k f catIso hasZero fkKer =
  (kernelConst (Precategory.seq (UnivalentCategory.cat C) k i)
    (((k ∘ i) ∘ (i⁻¹ ∘ f)) ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) k i (i⁻¹ ∘ f) ⟩
    (k ∘ (i ∘ (i⁻¹ ∘ f)))  ≡⟨ cong (λ x → k ∘ x) (sym (Precategory.seq-α (UnivalentCategory.cat C) i i⁻¹ f)) ⟩
    (k ∘ ((i ∘ i⁻¹) ∘ f))  ≡⟨ cong (λ x → k ∘ (x ∘ f)) (CatIso.ret catIso) ⟩
    (k ∘ (id A ∘ f))       ≡⟨ cong (λ x → k ∘ x) (Precategory.seq-λ (UnivalentCategory.cat C) f) ⟩
    (k ∘ f)                ≡⟨ transport (cong (λ x → x ∘ f ≡ 0a S B) (snd fkKer))
                                        (Kernel.kerComp (fst fkKer)) ⟩
    0a S B ∎)
    (λ {E} h hi⁻¹f=0 →
      transport (cong (λ x → Σ (Precategory.hom (UnivalentCategory.cat C) E S)
                                λ h' → Precategory.seq (UnivalentCategory.cat C) h'
                                       (Precategory.seq (UnivalentCategory.cat C) x i) ≡ h)
                      (snd fkKer))
                (h'' h hi⁻¹f=0 ,
                ((h'' h hi⁻¹f=0 ∘ ((Kernel.ker (fst fkKer)) ∘ i))  ≡⟨ sym (Precategory.seq-α (UnivalentCategory.cat C)
                                                                        (h'' h hi⁻¹f=0) (Kernel.ker (fst fkKer)) i) ⟩
                (((h'' h hi⁻¹f=0) ∘ (Kernel.ker (fst fkKer))) ∘ i) ≡⟨ cong (λ x → x ∘ i) (snd (h''Help h hi⁻¹f=0)) ⟩
                ((h ∘ i⁻¹) ∘ i)                                    ≡⟨ Precategory.seq-α (UnivalentCategory.cat C)
                                                                        h i⁻¹ i ⟩
                (h ∘ (i⁻¹ ∘ i))                                    ≡⟨ cong (λ x → h ∘ x) (CatIso.sec catIso) ⟩
                (h ∘ id A')                                        ≡⟨ Precategory.seq-ρ (UnivalentCategory.cat C) h ⟩
                h ∎)))
    λ E g h gki=hki → Kernel.kerFactorsUnique (fst fkKer) E g h (
      (g ∘ (Kernel.ker (fst fkKer))) ≡⟨ cong (λ x → g ∘ x) (snd fkKer) ⟩
      (g ∘ k)                        ≡⟨ sym (Precategory.seq-ρ (UnivalentCategory.cat C) (g ∘ k)) ⟩
      ((g ∘ k) ∘ (id A))             ≡⟨ cong (λ x → (g ∘ k) ∘ x) (sym (CatIso.ret catIso)) ⟩
      ((g ∘ k) ∘ (i ∘ i⁻¹))          ≡⟨ sym (Precategory.seq-α (UnivalentCategory.cat C) (g ∘ k) i i⁻¹) ⟩
      (((g ∘ k) ∘ i) ∘ i⁻¹)          ≡⟨ cong (λ x → x ∘ i⁻¹) (Precategory.seq-α (UnivalentCategory.cat C) g k i) ⟩
      ((g ∘ (k ∘ i)) ∘ i⁻¹)          ≡⟨ cong (λ x → x ∘ i⁻¹) gki=hki ⟩
      ((h ∘ (k ∘ i)) ∘ i⁻¹)          ≡⟨ cong (λ x → x ∘ i⁻¹) (sym (Precategory.seq-α (UnivalentCategory.cat C) h k i)) ⟩
      (((h ∘ k) ∘ i) ∘ i⁻¹)          ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) (h ∘ k) i i⁻¹ ⟩
      ((h ∘ k) ∘ (i ∘ i⁻¹))          ≡⟨ cong (λ x → (h ∘ k) ∘ x) (CatIso.ret catIso) ⟩
      ((h ∘ k) ∘ (id A))             ≡⟨ Precategory.seq-ρ (UnivalentCategory.cat C) (h ∘ k) ⟩
      (h ∘ k)                        ≡⟨ cong (λ x → h ∘ x) (sym (snd fkKer)) ⟩
      (h ∘ (Kernel.ker (fst fkKer))) ∎)) ,
  refl
    where
      _∘_ : {A B D : Precategory.ob (UnivalentCategory.cat C)} → Precategory.hom (UnivalentCategory.cat C) A B →
            Precategory.hom (UnivalentCategory.cat C) B D → Precategory.hom (UnivalentCategory.cat C) A D
      f ∘ g = Precategory.seq (UnivalentCategory.cat C) f g
      0a : (A B : Precategory.ob (UnivalentCategory.cat C))  → Precategory.hom (UnivalentCategory.cat C) A B
      0a A B = ZeroArrow.f (getZeroArrow C {A = A} {B = B} hasZero)
      i = CatIso.h catIso
      i⁻¹ = CatIso.h⁻¹ catIso
      id = Precategory.idn (UnivalentCategory.cat C)
      h''Help : {E : Precategory.ob (UnivalentCategory.cat C)} → (h : Precategory.hom (UnivalentCategory.cat C) E A') →
            (h ∘ (i⁻¹ ∘ f) ≡ 0a E B) → Σ (Precategory.hom (UnivalentCategory.cat C) E S)
                                         (λ h' → (h' ∘ (Kernel.ker (fst fkKer))) ≡ (h ∘ i⁻¹))
      h''Help {E} h hi⁻¹f=0 =
        Kernel.kerFactors (fst fkKer) (h ∘ i⁻¹)
                  (((h ∘ i⁻¹) ∘ f) ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) h i⁻¹ f ⟩
                  (h ∘ (i⁻¹ ∘ f))  ≡⟨ hi⁻¹f=0 ⟩
                  0a E B ∎)
      h'' : {E : Precategory.ob (UnivalentCategory.cat C)} → (h : Precategory.hom (UnivalentCategory.cat C) E A') →
            (h ∘ (i⁻¹ ∘ f) ≡ 0a E B) → Precategory.hom (UnivalentCategory.cat C) E S
      h'' {E} h hi⁻¹f=0 = fst (h''Help h hi⁻¹f=0)

PrecompIsoPreserveKernel :{ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} →
                          {A B S S' : Precategory.ob (UnivalentCategory.cat C)} →
                          (k : Precategory.hom (UnivalentCategory.cat C) S A) →
                          (f : Precategory.hom (UnivalentCategory.cat C) A B) →
                          (catIso : CatIso {C = UnivalentCategory.cat C} S' S) → 
                          (hasZero : hasZeroObject C) → isKernel C hasZero f k →
                          isKernel C hasZero f (Precategory.seq (UnivalentCategory.cat C) (CatIso.h catIso) k)
PrecompIsoPreserveKernel {C = C} {A} {B} {S} {S'} k f catIso hasZero fkKer =
  (kernelConst (i ∘ k)
               (((i ∘ k) ∘ f) ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) i k f ⟩
               (i ∘ (k ∘ f))  ≡⟨ cong (λ x → i ∘ (x ∘ f)) (sym (snd fkKer)) ⟩
               (i ∘ (k' ∘ f)) ≡⟨ cong (λ x → i ∘ x) (Kernel.kerComp (fst fkKer)) ⟩
               (i ∘ 0a S B)   ≡⟨ ZeroArrowCompLeft C hasZero i ⟩
               0a S' B ∎)
               (λ {E} h hf=0 →
                 transport (cong (λ x → Σ (Precategory.hom (UnivalentCategory.cat C) E S')
                                          (λ h' → Precategory.seq (UnivalentCategory.cat C) h' (i ∘ x) ≡ h))
                                 (snd fkKer))
                           (h'' h hf=0 , snd (h''Help h hf=0)))
               λ E g h gik=hik →
                 g               ≡⟨ sym (Precategory.seq-ρ (UnivalentCategory.cat C) g ) ⟩
                 (g ∘ id S')     ≡⟨ cong (λ x → g ∘ x) (sym (CatIso.ret catIso)) ⟩
                 (g ∘ (i ∘ i⁻¹)) ≡⟨ sym (Precategory.seq-α (UnivalentCategory.cat C) g i i⁻¹) ⟩
                 ((g ∘ i) ∘ i⁻¹) ≡⟨ cong (λ x → x ∘ i⁻¹) (Kernel.kerFactorsUnique (fst fkKer) E (g ∘ i) (h ∘ i)
                                         (((g ∘ i) ∘ k') ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) g i k' ⟩
                                         (g ∘ (i ∘ k'))  ≡⟨ transport (cong (λ x → g ∘ (i ∘ x) ≡ h ∘ (i ∘ x))
                                                                            (sym (snd fkKer)))
                                                                      gik=hik ⟩
                                         (h ∘ (i ∘ k'))  ≡⟨ sym (Precategory.seq-α (UnivalentCategory.cat C) h i k') ⟩
                                         ((h ∘ i) ∘ k') ∎)) ⟩
                 ((h ∘ i) ∘ i⁻¹) ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) h i i⁻¹ ⟩
                 (h ∘ (i ∘ i⁻¹)) ≡⟨ cong (λ x → h ∘ x) (CatIso.ret catIso) ⟩
                 (h ∘ (id S'))   ≡⟨ Precategory.seq-ρ (UnivalentCategory.cat C) h ⟩
                 h ∎) ,
  refl
    where
      _∘_ : {A B D : Precategory.ob (UnivalentCategory.cat C)} → Precategory.hom (UnivalentCategory.cat C) A B →
            Precategory.hom (UnivalentCategory.cat C) B D → Precategory.hom (UnivalentCategory.cat C) A D
      f ∘ g = Precategory.seq (UnivalentCategory.cat C) f g
      0a : (A B : Precategory.ob (UnivalentCategory.cat C))  → Precategory.hom (UnivalentCategory.cat C) A B
      0a A B = ZeroArrow.f (getZeroArrow C {A = A} {B = B} hasZero)
      i = CatIso.h catIso
      i⁻¹ = CatIso.h⁻¹ catIso
      id = Precategory.idn (UnivalentCategory.cat C)
      k' = Kernel.ker (fst fkKer)
      h''Help' : {E : Precategory.ob (UnivalentCategory.cat C)} → (h : Precategory.hom (UnivalentCategory.cat C) E A) →
            (h ∘ f ≡ 0a E B) → Σ (Precategory.hom (UnivalentCategory.cat C) E S)
                                         (λ h' → (h' ∘ k') ≡ h)
      h''Help' h hf=0 = Kernel.kerFactors (fst fkKer) h hf=0
      h''Help : {E : Precategory.ob (UnivalentCategory.cat C)} → (h : Precategory.hom (UnivalentCategory.cat C) E A) →
            (h ∘ f ≡ 0a E B) → Σ (Precategory.hom (UnivalentCategory.cat C) E S')
                                         (λ h' → (h' ∘ (i ∘ k')) ≡ h)
      h''Help {E} h hf=0 =
        ((fst (h''Help' h hf=0)) ∘ i⁻¹) ,
        (((fst (h''Help' h hf=0) ∘ i⁻¹) ∘ (i ∘ k'))  ≡⟨ Precategory.seq-α (UnivalentCategory.cat C)
                                                         (fst (h''Help' h hf=0)) i⁻¹ (i ∘ k') ⟩
        ((fst (h''Help' h hf=0)) ∘ (i⁻¹ ∘ (i ∘ k'))) ≡⟨ cong (λ x → fst (h''Help' h hf=0) ∘ x)
                                                             (sym (Precategory.seq-α (UnivalentCategory.cat C)
                                                               i⁻¹ i k')) ⟩
        ((fst (h''Help' h hf=0)) ∘ ((i⁻¹ ∘ i) ∘ k')) ≡⟨ cong (λ x → fst (h''Help' h hf=0) ∘ (x ∘ k')) (CatIso.sec catIso) ⟩
        ((fst (h''Help' h hf=0)) ∘ ((id S) ∘ k'))    ≡⟨ cong (λ x → fst (h''Help' h hf=0) ∘ x )
                                                             (Precategory.seq-λ (UnivalentCategory.cat C) k') ⟩
        ((fst (h''Help' h hf=0)) ∘ k')               ≡⟨ snd (h''Help' h hf=0) ⟩
        h ∎)
      h'' : {E : Precategory.ob (UnivalentCategory.cat C)} → (h : Precategory.hom (UnivalentCategory.cat C) E A) →
            (h ∘ f ≡ 0a E B) → Precategory.hom (UnivalentCategory.cat C) E S'
      h'' {E} h hf=0 = fst (h''Help h hf=0)

Σ2DepIso : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {C : A → B → Type ℓ''} →
           Iso (Σ A (λ a → Σ B (C a))) (Σ (Σ A (λ _ → B)) (λ (a , b) → C a b))
Σ2DepIso =
  iso (λ (a , (b , c)) → (a , b) , c)
      (λ ((a , b) , c) → (a , (b , c)))
      (λ z → refl)
      (λ z → refl)

Σ2DepHelp : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {C : A → B → Type ℓ''} →
            (Σ A (λ a → Σ B (C a))) ≡ (Σ (Σ A (λ _ → B)) (λ (a , b) → C a b))
Σ2DepHelp = ua (isoToEquiv Σ2DepIso)         

Σ2Dep : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {C : A → B → Type ℓ''} →
        {x y : Σ A (λ a → Σ B (C a))} →
        (p : fst x ≡ fst y) →
        (q : fst (snd x) ≡ fst (snd y)) →
        (λ i → C (p i) (q i)) [ snd (snd x) ≡ snd (snd y) ]P → 
        x ≡ y
Σ2Dep {x = x} {y = y} p q r = isoFunInjective Σ2DepIso x y (Σ≡ (Σ≡ p q) r)

ImHom : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
        (f : Precategory.hom (RModPreCat R) A B) → Precategory.ob (RModPreCat R)
ImHom R {A} {B} f =
  moduleConst (Σ ⟨ B ⟩M λ b → Helpers.fiber f' b) (0B , 0A , ModuleHomomorphismPreserveZero f) _+Im_ -Im_ _⋆Im_
    (isModule
      (ismodule
        (isabgroup
          (isgroup
            (ismonoid
              (issemigroup
                (isSetΣ (isSetModule B) (λ b → isSetΣ (isSetModule A) (λ b → isProp→isSet (isSetModule B _ _))))
                λ (b , a , fa=b) (b' , a' , fa'=b') (b'' , a'' , fa''=b'') →
                  Σ2Dep (Module+Isasso {M = B} b b' b'') (Module+Isasso {M = A} a a' a'') (toPathP (isSetModule B _ _ _ _)))
              λ (b , a , fa=b) → (Σ2Dep (ModuleZeroRight {M = B} b) (ModuleZeroRight {M = A} a) (toPathP (isSetModule B _ _ _ _))) ,
                                  Σ2Dep (ModuleZeroLeft {M = B} b) (ModuleZeroLeft {M = A} a) (toPathP (isSetModule B _ _ _ _)))
            λ (b , a , fa=b) → (Σ2Dep (ModuleInvRight {M = B} b) (ModuleInvRight {M = A} a) (toPathP (isSetModule B _ _ _ _))) ,
                               (Σ2Dep (ModuleInvLeft {M = B} b ) (ModuleInvLeft {M = A} a) (toPathP (isSetModule B _ _ _ _))))
          λ (b , a , fa=b) (b' , a' , fa'=b') → Σ2Dep (ModuleIsAb {M = B} b b') (ModuleIsAb {M = A} a a') (toPathP (isSetModule B _ _ _ _)))
        (λ r s (b , a , fa=b) → Σ2Dep (Module·Isasso {M = B} r s b) (Module·Isasso {M = A} r s a) (toPathP (isSetModule B _ _ _ _)))
        (λ r s (b , a , fa=b) → Σ2Dep (ModuleLDist {M = B} r s b) (ModuleLDist {M = A} r s a) (toPathP (isSetModule B _ _ _ _)))
        (λ r (b , a , fa=b) (b' , a' , fa'=b') → Σ2Dep (ModuleRDist {M = B} r b b') (ModuleRDist {M = A} r a a') (toPathP (isSetModule B _ _ _ _)))
        λ (b , a , fa=b) → Σ2Dep (ModuleLId {M = B} b) (ModuleLId {M = A} a) (toPathP (isSetModule B _ _ _ _))))
  where
    f' = ModuleHomomorphism.h f
    0B = Module.0m B
    0A = Module.0m A
    _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
    x +B y = (B Module.+ x) y
    _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
    x +A y = (A Module.+ x) y
    -A_ : ⟨ A ⟩M → ⟨ A ⟩M
    -A x = (Module.- A) x
    -B_ : ⟨ B ⟩M → ⟨ B ⟩M
    -B x = (Module.- B) x
    _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
    r ⋆B a = (B Module.⋆ r) a 
    _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
    r ⋆A a = (A Module.⋆ r) a
    _+R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
    r +R s = (snd (CommutativeRing→Ring R) RingStr.+ r) s
    _·R_ : ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩ → ⟨ CommutativeRing→Ring R ⟩
    r ·R s = (snd (CommutativeRing→Ring R) RingStr.· r) s
    1R = RingStr.1r (snd (CommutativeRing→Ring R))
    _+Im_ : (a b : Σ ⟨ B ⟩M (λ b → Helpers.fiber f' b)) → Σ ⟨ B ⟩M (λ b → Helpers.fiber f' b)
    (b , a , fa=b) +Im (b' , a' , fa'=b') = (b +B b') , ((a +A a') , transport (cong (λ x → f' (a +A a') ≡ (x +B b')) fa=b)
                                                                    (transport (cong (λ y → f' (a +A a') ≡ (f' a +B y)) fa'=b')
                                                                      (ModuleHomomorphism.linear f a a')))
    -Im_ : Σ ⟨ B ⟩M (λ b → Helpers.fiber f' b) → Σ ⟨ B ⟩M (λ b → Helpers.fiber f' b)
    -Im (b , a , fa=b) = (-B b) , (-A a) , (transport (cong (λ x → f' (-A a) ≡ -B x) fa=b) (ModuleHomomorphismLinSub a f))
    _⋆Im_ : ⟨ R ⟩ → Σ ⟨ B ⟩M (λ b → Helpers.fiber f' b) → Σ ⟨ B ⟩M (λ b → Helpers.fiber f' b)
    r ⋆Im (b , a , fa=b) = (r ⋆B b) , ((r ⋆A a) , (transport (cong (λ x → f' (r ⋆A a) ≡ (r ⋆B x)) fa=b)
                                                     (ModuleHomomorphism.scalar f r a)))

--mapProp : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} →
--          (isProp B) → (A → B) → (∥ A ∥ → B)
--mapProp propB f = {!!} {!map!}

eqFunHProp : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → ∥ A ∥ → (A → ∥ B ∥) → ∥ (A → B) ∥
eqFunHProp |a| f = recHprop propTruncIsProp (λ a → recHprop propTruncIsProp (λ b → ∣ (λ a → b) ∣) (f a)) |a| --rec propTruncIsProp f p
eqFunHPropDep : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → ∥ A ∥ → ((a : A) → ∥ B a ∥) → ∥ ((a : A) → B a) ∥
eqFunHPropDep {A = A} {B} |a| f = recHprop propTruncIsProp (λ a → {!!}) |a|
  where
    help : A → ∥ ((a : A) → ∥ B a ∥ ) ∥ → ∥ ((a : A) → B a) ∥
    help a = map {!!}

monicsAreKernelsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A S : Precategory.ob (RModPreCat R)} →
                       (k : Precategory.hom (RModPreCat R) S A) → isMonic (RMod {R = R}) k →
                       ∥ Σ (Precategory.ob (RModPreCat R))
                           (λ B → Σ (Precategory.hom (RModPreCat R) A B)
                                    (λ f → isKernel (RMod {R = R}) (hasZeroObjectRMod R) f k)) ∥
monicsAreKernelsRMod R {A} {S} k kMon =
  map (λ kcoK → fst kcoK , (CoKernel.coKer (snd kcoK)) ,
    transport (cong (isKernel (RMod {R = R}) (hasZeroObjectRMod R) (CoKernel.coKer (snd kcoK))) incImk∘toImk=k)
              (PrecompIsoPreserveKernel incImk (CoKernel.coKer (snd kcoK)) CatIsoImk (hasZeroObjectRMod R) (incImkKer kcoK)))
      (hasAllCoKernelsRMod R k)
  where
    k' = ModuleHomomorphism.h k
    _∘_ = Precategory.seq (RModPreCat R)
    0a : (A B : Precategory.ob (RModPreCat R))  → Precategory.hom (RModPreCat R) A B
    0a A B = ZeroArrow.f (getZeroArrow (RMod {R = R}) {A = A} {B = B} (hasZeroObjectRMod R))
    id = Precategory.idn (RModPreCat R)
    toImk : Precategory.hom (RModPreCat R) S (ImHom R k)
    toImk = moduleHomo (λ s → k' s , s , refl)
                       (λ s r → Σ2Dep (ModuleHomomorphism.linear k s r) refl (toPathP (isSetModule A _ _ _ _)))
                       λ r s → Σ2Dep (ModuleHomomorphism.scalar k r s) refl (toPathP (isSetModule A _ _ _ _))
    fromImk : Precategory.hom (RModPreCat R) (ImHom R k) S
    fromImk = moduleHomo (λ (a , s , ks=a) → s)
                         (λ (a , s , ks=a) (a' , s' , ks'=a') → refl)
                         λ r (a , s , ks=a) → refl
    CatIsoImk : CatIso {C = RModPreCat R} S (ImHom R k)
    CatIsoImk = catiso toImk fromImk
                       (ModuleHomo≡ (funExt (λ (a , s , ks=a) → Σ2Dep ks=a refl (toPathP (isSetModule A _ _ _ _)))))
                       (ModuleHomo≡ refl)
    incImk : Precategory.hom (RModPreCat R) (ImHom R k) A
    incImk = moduleHomo (λ (a , s , ks=a) → a)
                        (λ x y → refl)
                        (λ x y → refl)
    incImk∘toImk=k : (toImk ∘ incImk) ≡ k
    incImk∘toImk=k = ModuleHomo≡ refl
    incImkKer : (kcoK : Σ (Module R) (λ v → CoKernel RMod (hasZeroObjectRMod R) k)) → isKernel (RMod {R = R}) (hasZeroObjectRMod R) (CoKernel.coKer (snd kcoK)) incImk
    incImkKer kcoK =
      (kernelConst incImk
                   ((incImk ∘ (CoKernel.coKer (snd kcoK)))                      ≡⟨ sym (Precategory.seq-λ (RModPreCat R) (incImk ∘ (CoKernel.coKer (snd kcoK)))) ⟩
                   ((id (ImHom R k)) ∘ (incImk ∘ (CoKernel.coKer (snd kcoK))))  ≡⟨ cong (λ x → x ∘ (incImk ∘ (CoKernel.coKer (snd kcoK)))) (sym (CatIso.sec CatIsoImk)) ⟩
                   ((fromImk ∘ toImk) ∘ (incImk ∘ (CoKernel.coKer (snd kcoK)))) ≡⟨ Precategory.seq-α (RModPreCat R) fromImk toImk (incImk ∘ (CoKernel.coKer (snd kcoK))) ⟩
                   (fromImk ∘ (toImk ∘ (incImk ∘ (CoKernel.coKer (snd kcoK))))) ≡⟨ cong (λ x → fromImk ∘ x) (sym (Precategory.seq-α (RModPreCat R) toImk incImk (CoKernel.coKer (snd kcoK)))) ⟩
                   (fromImk ∘ ((toImk ∘ incImk) ∘ (CoKernel.coKer (snd kcoK)))) ≡⟨ cong (λ x → fromImk ∘ (x ∘ CoKernel.coKer (snd kcoK))) incImk∘toImk=k ⟩
                   (fromImk ∘ (k ∘ (CoKernel.coKer (snd kcoK))))                ≡⟨ cong (λ x → fromImk ∘ x) (CoKernel.coKerComp (snd kcoK)) ⟩
                   (fromImk ∘ 0a S (fst kcoK))                                  ≡⟨ ZeroArrowCompLeft (RMod {R = R}) (hasZeroObjectRMod R) fromImk ⟩
                    0a (ImHom R k) (fst kcoK) ∎)
                   (λ {E} h hcoK=0 →
                     {!!})
                   {!!}) ,
      refl
    getRel : (x y : ⟨ A ⟩M) → [ x ] ≡ [ y ] → ∥ coKernelRel R k x y ∥
    getRel = effective (λ a b → propTruncIsProp) (coKernelPropRelisEquiv R k)
    eqTrans : (x y : ⟨ A ⟩M) → Path (⟨ A ⟩M / coKernelRel R k) [ x ] [ y ] → Path (⟨ A ⟩M / (λ x y → ∥ coKernelRel R k x y ∥)) [ x ] [ y ]
    eqTrans x y Pathxy = λ i → Iso.fun truncRelIso (Pathxy i)
    h'Help : {E : Module R} → (h : ModuleHomomorphism R E A) → h ∘ CoKernel.coKer (snd (hasAllCoKernelsRModNonTrunk R k)) ≡ 0a E (makeCoKernelObjRMod R k) →
         (isMonic (RMod {R = R}) incImk) → Σ (ModuleHomomorphism R E (ImHom R k)) (λ h' → h' ∘ incImk ≡ h)
    h'Help {E} h hcok=0 monInc =
      recHprop (λ g g' → Σ≡ (monInc E (fst g) (fst g') (((fst g) ∘ incImk) ≡⟨ snd g ⟩
                                                       h                   ≡⟨ sym (snd g') ⟩ 
                                                       (fst g' ∘ incImk) ∎)) (toPathP (isSetModuleHomo E A _ _ _ _)))
               (λ f →
                 (moduleHomo {!λ e !}
                             {!!}
                             {!!}) ,
                 {!!}) {!!}
--               (getRel (ModuleHomomorphism.h h e) (ModuleHomomorphism.h (0a E A) e)
--      (eqTrans (ModuleHomomorphism.h h e) (ModuleHomomorphism.h (0a E A) e) λ i → ModuleHomomorphism.h (hcok=0 i) e))


--**************************************************************** Epic are coKernels *********************************************

PreCompEpicPreserveCoKernel : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} →
                             {A B S D : Precategory.ob (UnivalentCategory.cat C)} →
                             (c : Precategory.hom (UnivalentCategory.cat C) B S) →
                             (f : Precategory.hom (UnivalentCategory.cat C) A B) →
                             (e : Precategory.hom (UnivalentCategory.cat C) D A) →
                             (hasZero : hasZeroObject C) →
                             isEpic C e → isCoKernel C hasZero f c →
                             isCoKernel C hasZero (Precategory.seq (UnivalentCategory.cat C) e f) c
PreCompEpicPreserveCoKernel {C = C} {A} {B} {S} {D} c f e hasZero eEpic fcCok =
  (coKernelConst c
                 (((e ∘ f) ∘ c) ≡⟨ Precategory.seq-α (UnivalentCategory.cat C) e f c ⟩
                 (e ∘ (f ∘ c))  ≡⟨ cong (λ x → e ∘ x) ((cong (λ x → f ∘ x) (sym (snd fcCok))) ∙
                                                       (CoKernel.coKerComp (fst fcCok))) ⟩
                 (e ∘ (0a A S)) ≡⟨ ZeroArrowCompLeft C hasZero e ⟩
                 0a D S ∎)
                 (λ {E} h hfe=0 →
                   transport (cong (λ x → Σ (Precategory.hom (UnivalentCategory.cat C) S E)
                                            (λ h' → Precategory.seq (UnivalentCategory.cat C) x h' ≡ h))
                                   (snd fcCok))
                             (CoKernel.coKerFactors (fst fcCok) h
                               (eEpic E (Precategory.seq (UnivalentCategory.cat C) f h) (0a A E)
                                 ((e ∘ (f ∘ h)) ≡⟨ sym (Precategory.seq-α (UnivalentCategory.cat C) e f h) ⟩
                                 ((e ∘ f) ∘ h)  ≡⟨ hfe=0 ⟩
                                 0a D E         ≡⟨ sym (ZeroArrowCompLeft C hasZero e) ⟩
                                 (e ∘ (0a A E)) ∎))))
                 (transport (cong (isEpic C) (snd fcCok)) (CoKernel.coKerFactorsUnique (fst fcCok)))) ,
  refl
    where
      _∘_ : {A B D : Precategory.ob (UnivalentCategory.cat C)} → Precategory.hom (UnivalentCategory.cat C) A B →
            Precategory.hom (UnivalentCategory.cat C) B D → Precategory.hom (UnivalentCategory.cat C) A D
      f ∘ g = Precategory.seq (UnivalentCategory.cat C) f g
      0a : (A B : Precategory.ob (UnivalentCategory.cat C))  → Precategory.hom (UnivalentCategory.cat C) A B
      0a A B = ZeroArrow.f (getZeroArrow C {A = A} {B = B} hasZero)

--epicsAreCokernelsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B S : Precategory.ob (RModPreCat R)} →
--                        (k : Precategory.hom (RModPreCat R) B S) → isEpic (RMod {R = R}) k →
--                        ∥ (Σ (Precategory.hom (RModPreCat R) A B) (λ f → isCoKernel (RMod {R = R}) (hasZeroObjectRMod R) f k)) ∥
--epicsAreCokernelsRMod R k kEpic = ∣ ({!!} , {!!}) ∣

--Hint proof:
--https://uu.diva-portal.org/smash/get/diva2:1063166/FULLTEXT01.pdf
