{-# OPTIONS --cubical #-}

module ThesisWork.RModules.CommutativeRing where

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

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup

record IsCommutativeRing {ℓ : Level} {R : Type ℓ}
              (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where
  constructor isring
  field
   isRing  : IsRing 0r 1r _+_ _·_ -_
   commute : (x y : R) → x · y ≡ y · x

record CommutativeRingStr {ℓ : Level} (A : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor comRingStr
  field
    0r      : A
    1r      : A
    _+_     : A → A → A
    _·_     : A → A → A
    -_      : A → A
    isCommutativeRing  : IsCommutativeRing 0r 1r _+_ _·_ -_

CommutativeRing : {ℓ : Level} → Type (ℓ-suc ℓ)
CommutativeRing {ℓ} = TypeWithStr ℓ CommutativeRingStr

CommutativeRing→Ring : {ℓ : Level} → CommutativeRing {ℓ} → Ring {ℓ}
CommutativeRing→Ring (A , comRingStr 0r 1r _+_ _·_ -_ isCommutativeRing) = A , ringstr 0r 1r _+_ _·_ -_ (IsCommutativeRing.isRing isCommutativeRing)

CommutativeRingIsSet : {ℓ : Level} → (R : CommutativeRing {ℓ}) → isSet ⟨ R ⟩
CommutativeRingIsSet R = isSetRing (CommutativeRing→Ring R)
