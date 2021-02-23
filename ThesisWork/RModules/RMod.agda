{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RMod where

open import Cubical.Categories.Category
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

RModPreCat : {ℓ : Level} → (R : Ring {ℓ}) → Precategory (ℓ-suc ℓ) ℓ
RModPreCat R = record {ob = LeftModule R ;
                       hom = λ M N → LeftModuleHomomorphism R M N ;
                       idn = λ x → ModuleHomoId ;
                       seq = ModuleHomoComp ;
                       seq-λ = ModuleHomoIdLeftComp ;
                       seq-ρ = ModuleHomoIdRightComp ;
                       seq-α = λ f g h → sym (ModuleHomoCompAsso f g h)}

-- RModIsCategory : {ℓ : Level} → (R : Ring {ℓ}) → isCategory (RModPreCat R)
-- RModIsCategory R = record {homIsSet = λ {M} {N} → {!!}}
