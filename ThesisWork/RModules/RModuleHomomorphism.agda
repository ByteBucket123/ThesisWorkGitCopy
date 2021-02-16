{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModuleHomomorphism where

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

record LeftModuleHomomorphism {ℓ : Level} (R : Ring {ℓ}) (M N : LeftModule R) : Type ℓ where
  constructor moduleHomo
  field
    h : ⟨ M ⟩m → ⟨ N ⟩m
    linear : (x y : ⟨ M ⟩m) → h ((M LeftModule.+ x) y) ≡ (N LeftModule.+ (h x)) (h y)
    scalar : (r : ⟨ R ⟩) → (x : ⟨ M ⟩m) → h ((M LeftModule.⋆ r) x) ≡ (N LeftModule.⋆ r) (h x)

--******************************************* Help functions ************************************************

helpModuleHomomorphismLinear : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} →
                               (h : ⟨ M ⟩m → ⟨ N ⟩m) → Type ℓ
helpModuleHomomorphismLinear {ℓ} {R} {M} {N} h = (x y : (LeftModule.Carrier M)) →
                                                 h ((M LeftModule.+ x) y) ≡ (N LeftModule.+ (h x)) (h y)

helpModuleHomomorphismScalar : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} →
                               (h : ⟨ M ⟩m → ⟨ N ⟩m) → Type ℓ
helpModuleHomomorphismScalar {ℓ} {R} {M} {N} h = (r : fst R) → (x : LeftModule.Carrier M) →
                                                 h ((M LeftModule.⋆ r) x) ≡ (N LeftModule.⋆ r) (h x)

LeftModuleHomomorphism≡ : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → {x y : LeftModuleHomomorphism R M N}
                          → (p : LeftModuleHomomorphism.h x ≡ LeftModuleHomomorphism.h y)
                          → (q : (λ i → helpModuleHomomorphismLinear {M = M} {N = N} (p i))
                                 [ LeftModuleHomomorphism.linear x ≡ LeftModuleHomomorphism.linear y ])
                          → (r : (λ i → helpModuleHomomorphismScalar {M = M} {N = N} (p i))
                                 [ LeftModuleHomomorphism.scalar x ≡ LeftModuleHomomorphism.scalar y ])
                          → (x ≡ y)
LeftModuleHomomorphism≡ p q r = cong moduleHomo p <*> q <*> r           

--******************************************* is prop *******************************************************

isLeftModuleHomomorphism : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : ⟨ M ⟩m → ⟨ N ⟩m) → Type ℓ
isLeftModuleHomomorphism {R = R} {M = M} {N = N} h = Σ (LeftModuleHomomorphism R M N)
                                                     λ modHom → (LeftModuleHomomorphism.h modHom) ≡ h

eqHomo : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : ⟨ M ⟩m → ⟨ N ⟩m) →
         (p q : isLeftModuleHomomorphism {M = M} {N = N} h) → LeftModuleHomomorphism.h (fst p) ≡ LeftModuleHomomorphism.h (fst q)
eqHomo h p q = (snd p) ∙ (sym (snd q))

isPropModuleFunc : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → {h k : ⟨ M ⟩m → ⟨ N ⟩m} → isProp (h ≡ k)
isPropModuleFunc {N = N} {h = h} {k = k} p q = liftFunExt (isSetLeftModule N) p q

isLeftModuleHomomorphismIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : ⟨ M ⟩m → ⟨ N ⟩m) →
                                 isProp (isLeftModuleHomomorphism {M = M} {N = N} h)
isLeftModuleHomomorphismIsProp {M = M} {N = N} h p q = Σ≡ (LeftModuleHomomorphism≡
                                                       (eqHomo h p q)
                                                       (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                                                       isSetLeftModule N
                                                       ((((eqHomo h p q)) i) ((M LeftModule.+ x) y))
                                                       ((N LeftModule.+ ((((eqHomo h p q)) i) x)) ((((eqHomo h p q)) i) y))
                                                       (t x y) (s x y))))
                                                       (LeftModuleHomomorphism.linear (fst p))
                                                       (LeftModuleHomomorphism.linear (fst q)))
                                                       (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                                                       isSetLeftModule N
                                                       ((((eqHomo h p q)) i) ((M LeftModule.⋆ r) x))
                                                       ((N LeftModule.⋆ r) ((((eqHomo h p q)) i) x))
                                                       (t r x)
                                                       (s r x))))
                                                       (LeftModuleHomomorphism.scalar (fst p))
                                                       (LeftModuleHomomorphism.scalar (fst q))))
                                                       (isProp→PathP (λ i → isPropModuleFunc {M = M} {N = N})
                                                       (snd p)
                                                       (snd q))
