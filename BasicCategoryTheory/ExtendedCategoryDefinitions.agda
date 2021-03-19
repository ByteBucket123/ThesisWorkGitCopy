{-# OPTIONS --cubical #-}

module ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions where

--open import Cubical.Categories.Category
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Agda.Builtin.Cubical.Glue
open import ThesisWork.CompatibilityCode
open import ThesisWork.UnivalentFormulations

record Category (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Precategory ℓ ℓ'
    isCat : isCategory cat

record UnivalentCategory  (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Precategory ℓ ℓ'
    isCat : isCategory cat
    isUni : isUnivalent cat

--*************************** op category **************************************

--Proof _^op preserves isCategory and isUnivalent
opPresCat : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') → (p : isCategory C) → isCategory (C ^op)
opPresCat C CisCat = record {homIsSet = λ {A} {B} → λ x y → λ p q → homIsSet CisCat x y p q }

--TODO
--opPresUni : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') → (p : isUnivalent C) → isUnivalent (C ^op)
--opPresUni C CisUni = record {univ = λ x y → {!!}}

--_^opUnivCat : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → UnivalentCategory ℓ ℓ'
--_^opUnivCat C = record {cat = (UnivalentCategory.cat C) ^op ;
--                        isCat = opPresCat (UnivalentCategory.cat C) (UnivalentCategory.isCat C) ;
--                        isUni = opPresUni (UnivalentCategory.cat C) (UnivalentCategory.isUni C)}
