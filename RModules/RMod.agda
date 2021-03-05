{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RMod where

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
open import ThesisWork.RModules.RModuleHomomorphism
open import ThesisWork.RModules.CommutativeRing
open import ThesisWork.RModules.RModule
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import ThesisWork.CompatibilityCode


RModPreCat : {ℓ : Level} → (R : CommutativeRing {ℓ}) → Precategory (ℓ-suc ℓ) ℓ
RModPreCat R = record {ob = Module R ;
                       hom = λ M N → ModuleHomomorphism R M N ;
                       idn = λ x → ModuleHomoId ;
                       seq = ModuleHomoComp ;
                       seq-λ = ModuleHomoIdLeftComp ;
                       seq-ρ = ModuleHomoIdRightComp ;
                       seq-α = λ f g h → sym (ModuleHomoCompAsso f g h)}

RModIsCategory : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isCategory (RModPreCat R)
RModIsCategory R = record {homIsSet = λ {M} {N} → isSetModuleHomo M N}

--******************************************** isUnivalent ***********************************************************

CatIso→Section : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     {x y : Precategory.ob (RModPreCat R)} →
                     (catIso : CatIso {C = (RModPreCat R)} x y) →
                     section (ModuleHomomorphism.h (CatIso.h catIso)) (ModuleHomomorphism.h (CatIso.h⁻¹ catIso))
CatIso→Section (catiso h h⁻¹ sec ret) x i = ModuleHomomorphism.h (sec i) x

CatIso→Retract : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     {x y : Precategory.ob (RModPreCat R)} →
                     (catIso : CatIso {C = (RModPreCat R)} x y) →
                     retract (ModuleHomomorphism.h (CatIso.h catIso)) (ModuleHomomorphism.h (CatIso.h⁻¹ catIso))
CatIso→Retract (catiso h h⁻¹ sec ret) x i = ModuleHomomorphism.h (ret i) x

CatIso→IsoModules : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     {x y : Precategory.ob (RModPreCat R)} →
                     (CatIso {C = (RModPreCat R)} x y) → Iso ⟨ x ⟩M ⟨ y ⟩M
CatIso→IsoModules catIso@(catiso h h⁻¹ sec ret) = record {fun = ModuleHomomorphism.h h ;
                                                          inv = ModuleHomomorphism.h h⁻¹ ;
                                                          rightInv = (CatIso→Section catIso) ;
                                                          leftInv = CatIso→Retract catIso }

CatIso→EquivModules : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     {x y : Precategory.ob (RModPreCat R)} →
                     (CatIso {C = (RModPreCat R)} x y) → ⟨ x ⟩M ≃ ⟨ y ⟩M
CatIso→EquivModules catIso = isoToEquiv (CatIso→IsoModules catIso)

CatIso→ModuleEquiv : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     {x y : Precategory.ob (RModPreCat R)} →
                     (CatIso {C = (RModPreCat R)} x y) → (ModuleEquiv x y)
CatIso→ModuleEquiv catIso = record { e = CatIso→EquivModules catIso ;
                                     isHom+ = ModuleHomomorphism.linear (CatIso.h catIso) ;
                                     comm⋆ = ModuleHomomorphism.scalar (CatIso.h catIso) }

ModuleEquiv→CatIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     {x y : Precategory.ob (RModPreCat R)} →
                     (ModuleEquiv x y) → (CatIso {C = (RModPreCat R)} x y)
ModuleEquiv→CatIso modEq@(moduleIso e isHom+ comm⋆) =
  record { h = moduleHomo (equivFun e) isHom+ comm⋆ ; 
           h⁻¹ = moduleHomo (equivFun (invEquiv e)) (isHom+Flip modEq) (comm⋆Flip modEq) ;
           sec = ModuleHomo≡ (funExt (λ x → modEq→RightCompId modEq x)) ;
           ret = ModuleHomo≡ (funExt (λ x → modEq→LeftCompId modEq x))}

CatIso→EquivIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                       {x y : Precategory.ob (RModPreCat R)} → (z : ModuleEquiv x y) → 
                       CatIso→EquivModules (ModuleEquiv→CatIso z) ≡ ModuleEquiv.e z
CatIso→EquivIso z = equivEq (funExt (λ x → refl))
--  CatIso→EquivModules (ModuleEquiv→CatIso z) .fst x                          ≡⟨ refl ⟩
--  isoToEquiv (CatIso→IsoModules (ModuleEquiv→CatIso z)) .fst x               ≡⟨ refl ⟩
--  Iso.fun (CatIso→IsoModules (ModuleEquiv→CatIso z)) x                       ≡⟨ refl ⟩
--  ModuleHomomorphism.h (CatIso.h (ModuleEquiv→CatIso z)) x                   ≡⟨ refl ⟩
--  (equivFun (ModuleEquiv.e z)) x                                             ≡⟨ refl ⟩
--  (fst (ModuleEquiv.e z)) x ∎)) 

-- CatIso→EquivModules (ModuleEquiv→CatIso z) .fst x ≡ ModuleEquiv.e z .fst x

Equiv→CatIsoIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                       {x y : Precategory.ob (RModPreCat R)} → (z : CatIso x y) → 
                       moduleHomo (equivFun (invEquiv (CatIso→EquivModules z)))
      (isHom+Flip {M = x} {N = y}
       (moduleIso (CatIso→EquivModules z)
        (ModuleHomomorphism.linear (CatIso.h z))
        (ModuleHomomorphism.scalar (CatIso.h z))))
      (comm⋆Flip {M = x} {N = y}
       (moduleIso (CatIso→EquivModules z)
        (ModuleHomomorphism.linear (CatIso.h z))
        (ModuleHomomorphism.scalar (CatIso.h z))))
      ≡ CatIso.h⁻¹ z
Equiv→CatIsoIso z = ModuleHomo≡ refl



IsoCatIsoModuleEquiv : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                       {x y : Precategory.ob (RModPreCat R)} →
                       Iso (CatIso {C = (RModPreCat R)} x y) (ModuleEquiv x y)
IsoCatIsoModuleEquiv {R = R}  = record {fun = CatIso→ModuleEquiv ;
                                        inv = ModuleEquiv→CatIso ;
                                        rightInv = λ z → ModuleEquiv≡ (CatIso→EquivIso z) ;
                                        leftInv = λ z → CatIsoCat≡ (RModIsCategory R) refl (Equiv→CatIsoIso z)}

CatIso≃ModuleEquiv : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     {x y : Precategory.ob (RModPreCat R)} →
                     CatIso {C = (RModPreCat R)} x y ≃ ModuleEquiv x y
CatIso≃ModuleEquiv = isoToEquiv IsoCatIsoModuleEquiv

RModIsUnivalentHelp : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     (x y : Precategory.ob (RModPreCat R)) →
                     CatIso {C = (RModPreCat R)} x y ≃ (x ≡ y)
RModIsUnivalentHelp {R = R} x y =
  CatIso {C = (RModPreCat R)} x y                    ≃⟨ CatIso≃ModuleEquiv ⟩
  ModuleEquiv x y                                      ≃⟨ ModulePath ⟩
  (x ≡ y) ■

-- RModIsUnivalent2 : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (x y : Precategory.ob RModPreCat R) → isEquiv (pathToIso {C = RModPreCat R} x y)
-- RModIsUnivalent2 {R = R} x y = equivIsEquiv (isoToEquiv (
--   record {
--   fun = pathToIso {C = RModPreCat R} x y ;
--   inv = equivFun (RModIsUnivalentHelp x y) ;
--   rightInv = λ z → {!!} ;
--   leftInv = λ z → {!!}
--   }))

-- RModIsUnivalent : {ℓ : Level} → {R : CommutativeRing {ℓ}} → isUnivalent (RModPreCat R)
-- RModIsUnivalent = record {univ = λ x y → RModIsUnivalent2 x y}


--TODO: This proof is almost done. What is left to do is to prove (isSet A → isSet B → isSet (Σ A B)) and use it on module to prove isSet (module R) (first must create Σ type from the record type of module and prove equivalence.)
--RModIsUnivalentAlt : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
--                     ((x y : Precategory.ob (RModPreCat R)) →
--                    CatIso {C = (RModPreCat R)} x y ≃ (x ≡ y)) →
--                     (x : Precategory.ob (RModPreCat R)) → isContr (Σ (Precategory.ob (RModPreCat R)) (λ y →  x ≡ y))
--RModIsUnivalentAlt catIsoEq x = (x , refl) , (λ y → Σ≡ (snd y) (isProp→PathP (λ i → {!!}) refl (snd y)))
