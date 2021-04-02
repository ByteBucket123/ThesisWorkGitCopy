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
open import ThesisWork.UnivalentFormulations
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence


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

--RModIsUnivalentAlt : {ℓ : Level} → {R : CommutativeRing {ℓ}} → isUnivalentAlt (RModPreCat R)
--RModIsUnivalentAlt = {!!}

--RModIsUnivalent : {ℓ : Level} → {R : CommutativeRing {ℓ}} → isUnivalent (RModPreCat R)
--RModIsUnivalent = {!!}

--******************************************************** Test lift hom ******************************************************

RModPreCatLift : {ℓ : Level} → (R : CommutativeRing {ℓ}) → Precategory (ℓ-suc ℓ) (ℓ-suc ℓ)
RModPreCatLift R = record {ob = Module R ;
                           hom = λ M N → Lift (ModuleHomomorphism R M N) ;
                           idn = λ x → lift ModuleHomoId ;
                           seq = λ f g → liftFun2 ModuleHomoComp f g ;
                           seq-λ = λ f → liftExt (ModuleHomoIdLeftComp (lower f)) ;
                           seq-ρ = λ f → liftExt (ModuleHomoIdRightComp (lower f)) ;
                           seq-α = λ f g h → liftExt (sym (ModuleHomoCompAsso (lower f) (lower g) (lower h))) }

RModLiftCatIsoIso : {ℓ : Level} → (R : CommutativeRing {ℓ}) →
                    {x y : Precategory.ob (RModPreCat R)} →
                    Iso (CatIso {C = (RModPreCat R)} x y) (CatIso {C = (RModPreCatLift R)} x y)
RModLiftCatIsoIso R =
  iso (λ x → catiso (lift (CatIso.h x))
                    (lift (CatIso.h⁻¹ x))
                    (liftExt (CatIso.sec x))
                    (liftExt (CatIso.ret x)))
      (λ x → catiso (lower (CatIso.h x))
                    (lower (CatIso.h⁻¹ x))
                    (lowerExt (CatIso.sec x))
                    (lowerExt (CatIso.ret x)))
      (λ z → refl)
       λ z → refl

RModLiftIsUnivalentHelp : {ℓ : Level} → {R : CommutativeRing {ℓ}} →
                     (x y : Precategory.ob (RModPreCatLift R)) →
                     CatIso {C = (RModPreCatLift R)} x y ≃ (x ≡ y)
RModLiftIsUnivalentHelp {R = R} x y = compEquiv (isoToEquiv (invIso (RModLiftCatIsoIso R))) (RModIsUnivalentHelp x y) 

RModLiftIsUnivalentAlt : {ℓ : Level} → {R : CommutativeRing {ℓ}} → isUnivalentAlt (RModPreCatLift R)
RModLiftIsUnivalentAlt = isoEquivToUnivalentAlt λ x y → invEquiv (RModLiftIsUnivalentHelp x y)

RModLiftIsUnivalent : {ℓ : Level} → {R : CommutativeRing {ℓ}} → isUnivalent (RModPreCatLift R)
RModLiftIsUnivalent = univalentAlt→ _ RModLiftIsUnivalentAlt

RModLiftCatIsoIso' : {ℓ : Level} → (R : CommutativeRing {ℓ}) →
                    {x y : Precategory.ob (RModPreCat R)} →
                    Iso (Lift {ℓ} {ℓ-suc ℓ} (CatIso {C = (RModPreCat R)} x y)) (CatIso {C = (RModPreCatLift R)} x y)
RModLiftCatIsoIso' R =
  iso (λ (lift a) → Iso.fun (RModLiftCatIsoIso R) a)
      (λ b → lift (Iso.inv (RModLiftCatIsoIso R) b))
      (λ z → refl)
       λ z → refl

--isContr (Σ (ob C) (λ y → CatIso {C = C} x y))
RModIsUnivalentAltHelp : {ℓ : Level} → (R : CommutativeRing {ℓ}) →
                         {x y : Precategory.ob (RModPreCat R)} →
                         Iso (Lift {ℓ-suc ℓ} {ℓ-suc (ℓ-suc ℓ)} (Σ (ob (RModPreCat R)) (λ y → CatIso {C = (RModPreCat R)} x y)))
                             (Σ (ob (RModPreCatLift R)) (λ y → CatIso {C = (RModPreCatLift R)} x y))
RModIsUnivalentAltHelp R {x} =
  iso (λ (lift (ob , a)) →      ob , (Iso.fun (RModLiftCatIsoIso R) a))
      (λ       (ob , b) → lift (ob , Iso.inv (RModLiftCatIsoIso R) b))
      (λ z → refl)
       λ z → refl

RModIsUnivalentAltHelp2 : {ℓ : Level} → (R : CommutativeRing {ℓ}) →
                         {x y : Precategory.ob (RModPreCat R)} →
                         Iso (Lift {ℓ-suc ℓ} {ℓ} (Σ (ob (RModPreCat R)) (λ y → CatIso {C = (RModPreCat R)} x y)))
                             (Σ (ob (RModPreCatLift R)) (λ y → CatIso {C = (RModPreCatLift R)} x y))
RModIsUnivalentAltHelp2 R {x} =
  iso (λ (lift (ob , a)) →      ob , (Iso.fun (RModLiftCatIsoIso R) a))
      (λ       (ob , b) → lift (ob , Iso.inv (RModLiftCatIsoIso R) b))
      (λ z → refl)
       λ z → refl

RModIsUnivalentAlt : {ℓ : Level} → {R : CommutativeRing {ℓ}} → isUnivalentAlt (RModPreCat R)
RModIsUnivalentAlt {R = R} =
  record {univ = λ x → (x , (idCatIso x)) , λ z → isProp→PathP (λ i → isPropΣCatIso' {y = fst z}) (x , (idCatIso x)) z}
--  Σ≡ (equivFun (RModIsUnivalentHelp x (fst z)) (snd z))
--     (isProp→PathP (λ i → isPropCatIso) (idCatIso x) (snd z))}
  where
    liftIsUni = RModLiftIsUnivalent
--    liftCatIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {x y : Precategory.ob (RModPreCat R)} →
--                 CatIso {C = (RModPreCat R)} x y → CatIso {C = (RModPreCatLift R)} x y
--    liftCatIso {R = R} a = Iso.fun (RModLiftCatIsoIso R) a
    isPropΣCatIso' : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {x y : Precategory.ob (RModPreCat R)} →
                    isProp (Σ (ob (RModPreCat R)) (λ y → CatIso {C = (RModPreCat R)} x y))
    isPropΣCatIso' {R = R} {x} {y} a b =
      lowerExt (isContr→isProp (
        transport (cong isContr (sym (ua (isoToEquiv (RModIsUnivalentAltHelp2 R {y = y})))))
        (isUnivalentAlt.univ RModLiftIsUnivalentAlt x)) (lift a) (lift b))
    
--  isPropCatIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {x y : Precategory.ob (RModPreCat R)} →
--                   isProp (CatIso {C = (RModPreCat R)} x y)
--  isPropCatIso a b = lowerExt (isContr→isProp {!!} (lift a) (lift b))

RModIsUnivalent : {ℓ : Level} → {R : CommutativeRing {ℓ}} → isUnivalent (RModPreCat R)
RModIsUnivalent {R = R} = univalentAlt→ (RModPreCat R) RModIsUnivalentAlt

RMod : {ℓ : Level} → {R : CommutativeRing {ℓ}} → UnivalentCategory (ℓ-suc ℓ) ℓ
RMod {R = R} = record {cat   = RModPreCat R ;
                       isCat = RModIsCategory R ;
                       isUni = RModIsUnivalent}
