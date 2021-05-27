{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModAbelian where

open import Cubical.Foundations.Prelude
open import ThesisWork.RModules.CommutativeRing
open import ThesisWork.RModules.RMod

open import ThesisWork.RModules.DirectProofKernels
open import ThesisWork.RModules.RModProperties
open import ThesisWork.AbelianCategory.Abelian

RModisAbelian : {ℓ : Level} → (R : CommutativeRing {ℓ}) → Abelian (RMod {R = R})
RModisAbelian R =
  abeleanCat (hasZeroObjectRMod R)
             (hasAllBinaryProductsRMod R)
             (hasAllBinaryCoProductsRMod R)
             (hasAllKernelsRMod R)
             (hasAllCoKernelsRMod R)
             (monicsAreKernelsRModDirect R)
             (epicsAreCokernelsRMod R)
