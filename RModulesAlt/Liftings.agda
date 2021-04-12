{-# OPTIONS --cubical #-}

module ThesisWork.RModulesAlt.Liftings where

open import ThesisWork.RModules.CommutativeRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import ThesisWork.UnivalentFormulations
open import Cubical.Algebra.Ring.Base 
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Data.Sigma.Properties
open import ThesisWork.RModules.RModule
open import Cubical.Algebra.Module.Base

--************************************************************** Lift Abgebra *********************************************************************************

--************************************************************** SemiGroup ************************************************************************************

LiftSemiGroup : {ℓ ℓ' : Level} → {R : Type ℓ} → {_+_ : R → R → R} → 
                IsSemigroup _+_ → 
                IsSemigroup {A = Lift {j = ℓ'} R} (λ (lift x) (lift y) → lift (x + y))
LiftSemiGroup semiGroup =
  issemigroup (λ (lift x) (lift y) p q i j → lift (IsSemigroup.is-set semiGroup x y (λ i → lower (p i)) (λ i → lower (q i)) i j))
               λ (lift x) (lift y) (lift z) → liftExt (IsSemigroup.assoc semiGroup x y z)

LowerLiftSemiGroup : {ℓ ℓ' : Level} → {R : Type ℓ} → {_+_ : R → R → R} → 
                     IsSemigroup {A = Lift {j = ℓ'} R} (λ (lift x) (lift y) → lift (x + y)) →
                     IsSemigroup _+_
LowerLiftSemiGroup liftsemiGroup =
  issemigroup (λ x y p q i j → lower (IsSemigroup.is-set liftsemiGroup (lift x) (lift y) (λ i → lift (p i)) (λ i → lift (q i)) i j))
              λ x y z → lowerExt (IsSemigroup.assoc liftsemiGroup (lift x) (lift y) (lift z))

LiftSemiGroupIso : {ℓ ℓ' : Level} → {R : Type ℓ} → {_+_ : R → R → R} → 
                   Iso (IsSemigroup _+_) 
                   (IsSemigroup {A = Lift {j = ℓ'} R} (λ (lift x) (lift y) → lift (x + y)))
LiftSemiGroupIso = iso LiftSemiGroup
                       LowerLiftSemiGroup
                       (λ z → refl)
                        λ z → refl

--********************************************************************* Monoid ************************************************************************************

LiftMonoid : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → 
             IsMonoid 0r _+_ → 
             IsMonoid (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y))
LiftMonoid mon =
  ismonoid (LiftSemiGroup (IsMonoid.isSemigroup mon))
           λ (lift x) → (liftExt (fst (IsMonoid.identity mon x))) , (liftExt (snd (IsMonoid.identity mon x)))

LowerLiftMonoid : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → 
                  IsMonoid (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)) →
                  IsMonoid 0r _+_
LowerLiftMonoid liftmonoid =
  ismonoid (LowerLiftSemiGroup (IsMonoid.isSemigroup liftmonoid))
           (λ x → (lowerExt (fst (IsMonoid.identity liftmonoid (lift x)))) , lowerExt (snd (IsMonoid.identity liftmonoid (lift x))))

LiftMonoidIso : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → 
                Iso (IsMonoid 0r _+_) (IsMonoid (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)))
LiftMonoidIso = iso LiftMonoid LowerLiftMonoid (λ z → refl) λ z → refl

--********************************************************************** Group *****************************************************************************************

LiftGroup : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → { -_ : R → R} →
            IsGroup 0r _+_ -_ → 
            IsGroup (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x))
LiftGroup group =
  isgroup (LiftMonoid (IsGroup.isMonoid group))
          λ (lift x) → (liftExt (fst (IsGroup.inverse group x))) , (liftExt (snd (IsGroup.inverse group x)))

LowerLiftGroup : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → { -_ : R → R} →
                 IsGroup (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) →
                 IsGroup 0r _+_ -_
LowerLiftGroup liftGroup =
  isgroup (LowerLiftMonoid (IsGroup.isMonoid liftGroup))
          (λ x → (lowerExt (fst (IsGroup.inverse liftGroup (lift x)))) , (lowerExt (snd (IsGroup.inverse liftGroup (lift x)))))

LiftGroupIso : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → { -_ : R → R} →
               Iso (IsGroup 0r _+_ -_) (IsGroup (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)))
LiftGroupIso = iso LiftGroup LowerLiftGroup (λ z → refl) (λ z → refl)

--************************************************************************ AbGroup ****************************************************************************************

LiftAbGroup : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → { -_ : R → R} →
              IsAbGroup 0r _+_ -_ → 
              IsAbGroup (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x))
LiftAbGroup abGroup =
  isabgroup (LiftGroup (IsAbGroup.isGroup abGroup))
            λ (lift x) (lift y) → liftExt (IsAbGroup.comm abGroup x y)

LowerLiftAbGroup : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → { -_ : R → R} →
                   IsAbGroup (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) →
                   IsAbGroup 0r _+_ -_
LowerLiftAbGroup liftAbGroup =
  isabgroup (LowerLiftGroup (IsAbGroup.isGroup liftAbGroup))
            (λ x y → lowerExt (IsAbGroup.comm liftAbGroup (lift x) (lift y)))

LiftAbGroupIso : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r : R} → {_+_ : R → R → R} → { -_ : R → R} →
                 Iso (IsAbGroup 0r _+_ -_) (IsAbGroup (lift {j = ℓ'} 0r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)))
LiftAbGroupIso = iso LiftAbGroup LowerLiftAbGroup (λ z → refl) (λ z → refl)

--************************************************************************* Ring ********************************************************************************************

LiftIsRing : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r 1r : R} → {_+_ _·_ : R → R → R} → { -_ : R → R} →
             IsRing 0r 1r _+_ _·_ -_ → 
             IsRing (lift {j = ℓ'} 0r) (lift 1r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) (lift y) → lift (x · y)) (λ (lift x) → lift (- x))
LiftIsRing ring =
  isring (LiftAbGroup (IsRing.+IsAbGroup ring))
         (LiftMonoid (IsRing.·IsMonoid ring))
         (λ (lift x) (lift y) (lift z) → (liftExt (fst (IsRing.dist ring x y z))) , liftExt (snd (IsRing.dist ring x y z)))

LowerLiftIsRing : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r 1r : R} → {_+_ _·_ : R → R → R} → { -_ : R → R} →
                  IsRing (lift {j = ℓ'} 0r) (lift 1r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) (lift y) → lift (x · y)) (λ (lift x) → lift (- x)) →
                  IsRing 0r 1r _+_ _·_ -_
LowerLiftIsRing liftRing =
  isring (LowerLiftAbGroup (IsRing.+IsAbGroup liftRing))
         (LowerLiftMonoid (IsRing.·IsMonoid liftRing))
         (λ x y z → (lowerExt (fst (IsRing.dist liftRing (lift x) (lift y) (lift z)))) , lowerExt (snd (IsRing.dist liftRing (lift x) (lift y) (lift z))))
         
LiftIsRingIso : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r 1r : R} → {_+_ _·_ : R → R → R} → { -_ : R → R} →
                Iso (IsRing 0r 1r _+_ _·_ -_) (IsRing (lift {j = ℓ'} 0r) (lift 1r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) (lift y) → lift (x · y)) (λ (lift x) → lift (- x)))
LiftIsRingIso = iso LiftIsRing LowerLiftIsRing (λ z → refl) (λ z → refl)

--********************************************************************* CommRing *************************************************************************************************

LiftIsCommutativeRing : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r 1r : R} → {_+_ _·_ : R → R → R} → { -_ : R → R} →
                        IsCommutativeRing 0r 1r _+_ _·_ -_ → 
                        IsCommutativeRing (lift {j = ℓ'} 0r) (lift 1r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) (lift y) → lift (x · y)) (λ (lift x) → lift (- x))
LiftIsCommutativeRing commRing =
  isring (LiftIsRing (IsCommutativeRing.isRing commRing))
         (λ (lift x) (lift y) → liftExt (IsCommutativeRing.commute commRing x y))

LowerLiftIsCommutativeRing : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r 1r : R} → {_+_ _·_ : R → R → R} → { -_ : R → R} →
                             IsCommutativeRing (lift {j = ℓ'} 0r) (lift 1r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) (lift y) → lift (x · y)) (λ (lift x) → lift (- x)) →
                             IsCommutativeRing 0r 1r _+_ _·_ -_
LowerLiftIsCommutativeRing liftCommRing =
  isring (LowerLiftIsRing (IsCommutativeRing.isRing liftCommRing))
         (λ x y → lowerExt (IsCommutativeRing.commute liftCommRing (lift x) (lift y)))

LiftIsCommutativeRingIso : {ℓ ℓ' : Level} → {R : Type ℓ} → {0r 1r : R} → {_+_ _·_ : R → R → R} → { -_ : R → R} →
                           Iso (IsCommutativeRing 0r 1r _+_ _·_ -_)
                               (IsCommutativeRing (lift {j = ℓ'} 0r) (lift 1r) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) (lift y) → lift (x · y)) (λ (lift x) → lift (- x)))
LiftIsCommutativeRingIso = iso LiftIsCommutativeRing LowerLiftIsCommutativeRing (λ z → refl) (λ z → refl)

--************************************************************************** LiftCommRing **********************************************************************************************************

LiftCommutativeRingStr : {ℓ ℓ' : Level} → (A : Type ℓ) → (CommutativeRingStr A) → CommutativeRingStr (Lift {j = ℓ'} A)
LiftCommutativeRingStr {ℓ' = ℓ'} A str =
  comRingStr (lift 0r)
             (lift 1r)
             (λ (lift x) (lift y) → lift (x + y))
             (λ (lift x) (lift y) → lift (x · y))
             (λ (lift x) → lift (- x))
             (LiftIsCommutativeRing {ℓ' = ℓ'} (CommutativeRingStr.isCommutativeRing str))
  where
    0r = CommutativeRingStr.0r str
    1r = CommutativeRingStr.1r str
    _+_ = CommutativeRingStr._+_ str
    _·_ = CommutativeRingStr._·_ str
    -_ = CommutativeRingStr.-_ str

LowerLiftCommutativeRingStr : {ℓ ℓ' : Level} → (A : Type ℓ)  → CommutativeRingStr (Lift {j = ℓ'} A) → (CommutativeRingStr A)
LowerLiftCommutativeRingStr A liftStr =
  comRingStr (lower 0r)
             (lower 1r)
             (λ x y → lower ((lift x) + (lift y)))
             (λ x y → lower ((lift x) · (lift y)))
             (λ x → lower (- (lift x)))
             (LowerLiftIsCommutativeRing (CommutativeRingStr.isCommutativeRing liftStr))
  where
    0r = CommutativeRingStr.0r liftStr
    1r = CommutativeRingStr.1r liftStr
    _+_ = CommutativeRingStr._+_ liftStr
    _·_ = CommutativeRingStr._·_ liftStr
    -_ = CommutativeRingStr.-_ liftStr

LiftCommutativeRingStrIso : {ℓ ℓ' : Level} → (A : Type ℓ) → Iso (CommutativeRingStr A) (CommutativeRingStr (Lift {j = ℓ'} A))
LiftCommutativeRingStrIso A = iso (LiftCommutativeRingStr A) (LowerLiftCommutativeRingStr A) (λ z → refl) (λ z → refl)

LiftCommutativeRing :  {ℓ ℓ' : Level} → (CommutativeRing {ℓ}) → CommutativeRing {ℓ-max ℓ ℓ'}
LiftCommutativeRing {ℓ} {ℓ'} (Type , str) =
  (Lift {j = ℓ'} Type) , LiftCommutativeRingStr Type str

--****************************************************************** Lift Module *************************************************************************************

LiftIsLeftModule :  {ℓ ℓ' : Level} → (R : CommutativeRing {ℓ}) → {M : Type ℓ} → {0m : M} → {_+_ : M → M → M} → { -_ : M → M} → {_⋆_ : ⟨ R ⟩ → M → M} → 
                    IsLeftModule (CommutativeRing→Ring R) 0m _+_ -_ _⋆_ →
                    IsLeftModule (CommutativeRing→Ring (LiftCommutativeRing {ℓ' = ℓ'}R)) (lift {j = ℓ'} 0m) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) (λ (lift x) (lift y) → lift (x ⋆ y))
LiftIsLeftModule R isLeft =
  ismodule (LiftAbGroup (IsLeftModule.+-isAbGroup isLeft))
           (λ (lift r) (lift s) (lift x) → liftExt (IsLeftModule.⋆-assoc isLeft r s x))
           (λ (lift r) (lift s) (lift x) → liftExt (IsLeftModule.⋆-ldist isLeft r s x))
           (λ (lift r) (lift x) (lift y) → liftExt (IsLeftModule.⋆-rdist isLeft r x y))
           λ (lift x) → liftExt (IsLeftModule.⋆-lid isLeft x)

LowerLiftIsLeftModule :  {ℓ ℓ' : Level} → (R : CommutativeRing {ℓ}) → {M : Type ℓ} → {0m : M} → {_+_ : M → M → M} → { -_ : M → M} → {_⋆_ : ⟨ R ⟩ → M → M} → 
                         IsLeftModule (CommutativeRing→Ring (LiftCommutativeRing {ℓ' = ℓ'}R)) (lift {j = ℓ'} 0m) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) (λ (lift x) (lift y) → lift (x ⋆ y)) →
                         IsLeftModule (CommutativeRing→Ring R) 0m _+_ -_ _⋆_
LowerLiftIsLeftModule R liftLeftModule =
  ismodule (LowerLiftAbGroup (IsLeftModule.+-isAbGroup liftLeftModule))
           (λ r s x → lowerExt (IsLeftModule.⋆-assoc liftLeftModule (lift r) (lift s) (lift x)))
           (λ r s x → lowerExt (IsLeftModule.⋆-ldist liftLeftModule (lift r) (lift s) (lift x)))
           (λ r x y → lowerExt (IsLeftModule.⋆-rdist liftLeftModule (lift r) (lift x) (lift y)))
           (λ x → lowerExt (IsLeftModule.⋆-lid liftLeftModule (lift x)))

LiftIsLeftModuleIso :  {ℓ ℓ' : Level} → (R : CommutativeRing {ℓ}) → {M : Type ℓ} → {0m : M} → {_+_ : M → M → M} → { -_ : M → M} → {_⋆_ : ⟨ R ⟩ → M → M} → 
                       Iso (IsLeftModule (CommutativeRing→Ring R) 0m _+_ -_ _⋆_)
                       (IsLeftModule (CommutativeRing→Ring (LiftCommutativeRing {ℓ' = ℓ'}R)) (lift {j = ℓ'} 0m) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) (λ (lift x) (lift y) → lift (x ⋆ y)))
LiftIsLeftModuleIso R = iso (LiftIsLeftModule R) (LowerLiftIsLeftModule R) (λ z → refl) (λ z → refl)


LiftIsModule :  {ℓ ℓ' : Level} → (R : CommutativeRing {ℓ}) → {M : Type ℓ} → {0m : M} → {_+_ : M → M → M} → { -_ : M → M} → {_⋆_ : ⟨ R ⟩ → M → M} → 
                IsModule R 0m _+_ -_ _⋆_ →
                IsModule (LiftCommutativeRing {ℓ' = ℓ'}  R) (lift {j = ℓ'} 0m) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) (λ (lift x) (lift y) → lift (x ⋆ y))
LiftIsModule R isMod =
  isModule (LiftIsLeftModule R (IsModule.isLeftModule isMod))
               
LowerLiftIsModule :  {ℓ ℓ' : Level} → (R : CommutativeRing {ℓ}) → {M : Type ℓ} → {0m : M} → {_+_ : M → M → M} → { -_ : M → M} → {_⋆_ : ⟨ R ⟩ → M → M} → 
                     IsModule (LiftCommutativeRing {ℓ' = ℓ'}  R) (lift {j = ℓ'} 0m) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) (λ (lift x) (lift y) → lift (x ⋆ y)) →
                     IsModule R 0m _+_ -_ _⋆_
LowerLiftIsModule R liftIsMod =
  isModule (LowerLiftIsLeftModule R (IsModule.isLeftModule liftIsMod))
                     
LiftIsModuleIso :  {ℓ ℓ' : Level} → (R : CommutativeRing {ℓ}) → {M : Type ℓ} → {0m : M} → {_+_ : M → M → M} → { -_ : M → M} → {_⋆_ : ⟨ R ⟩ → M → M} → 
                   Iso (IsModule R 0m _+_ -_ _⋆_) 
                   (IsModule (LiftCommutativeRing {ℓ' = ℓ'}  R) (lift {j = ℓ'} 0m) (λ (lift x) (lift y) → lift (x + y)) (λ (lift x) → lift (- x)) (λ (lift x) (lift y) → lift (x ⋆ y)))
LiftIsModuleIso R = iso (LiftIsModule R) (LowerLiftIsModule R) (λ z → refl) (λ z → refl)


LiftModule : {ℓ ℓ' : Level} → (R : CommutativeRing {ℓ}) → Module R → Module (LiftCommutativeRing {ℓ' = ℓ'}  R)
LiftModule {ℓ} {ℓ'} R (moduleConst Carrier 0m _+_ -_ _⋆_ isMod) =
  moduleConst (Lift {j = ℓ'} Carrier)
              (lift 0m)
              (λ (lift x) (lift y) → lift (x + y))
              (λ (lift x) → lift (- x))
              (λ (lift r) (lift x) → lift (r ⋆ x))
              (LiftIsModule R isMod)

--LiftCommutativeRingEq : {ℓ ℓ' : Level} → Iso (CommutativeRing {ℓ}) (Σ (CommutativeRing {ℓ-max ℓ ℓ'}) (λ R → Σ (Type ℓ) (λ type → fst R ≡ Lift {j = ℓ'} type)))
--LiftCommutativeRingEq = iso (λ R → (LiftCommutativeRing R) , ((fst R) , refl))
--                            (λ (R , type , fstR=type) → type , (LowerLiftCommutativeRingStr type (transport (cong CommutativeRingStr fstR=type) (snd R))))
--                            (λ (R , type , fstR=type) → ΣPathP (ΣPathP ({!!} , {!!}) , ΣPathP ({!!} , {!!}))) --ΣPathP ({!!} , refl))
--                             λ z → ΣPathP (refl , {!!})
