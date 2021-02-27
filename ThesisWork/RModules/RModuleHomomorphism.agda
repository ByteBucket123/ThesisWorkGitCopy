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
open import ThesisWork.RModules.CommutativeRing
open import ThesisWork.RModules.RModule
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma.Properties

record ModuleHomomorphism {ℓ : Level} (R : CommutativeRing {ℓ}) (M N : Module R) : Type ℓ where
  constructor moduleHomo
  field
    h : ⟨ M ⟩M → ⟨ N ⟩M
    linear : (x y : ⟨ M ⟩M) → h ((M Module.+ x) y) ≡ (N Module.+ (h x)) (h y)
    scalar : (r : ⟨ R ⟩) → (x : ⟨ M ⟩M) → h ((M Module.⋆ r) x) ≡ (N Module.⋆ r) (h x)

--******************************************* Help functions ************************************************

helpModuleHomomorphismLinear : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
                               (h : ⟨ M ⟩M → ⟨ N ⟩M) → Type ℓ
helpModuleHomomorphismLinear {ℓ} {R} {M} {N} h = (x y : ⟨ M ⟩M ) → h ((M Module.+ x) y) ≡ (N Module.+ (h x)) (h y)

helpModuleHomomorphismScalar : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} →
                               (h : ⟨ M ⟩M → ⟨ N ⟩M) → Type ℓ
helpModuleHomomorphismScalar {ℓ} {R} {M} {N} h = (r : fst R) → (x : Module.Carrier M) →
                                                 h ((M Module.⋆ r) x) ≡ (N Module.⋆ r) (h x)

ModuleHomomorphism≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleHomomorphism R M N}
                      → (p : ModuleHomomorphism.h x ≡ ModuleHomomorphism.h y)
                      → (q : (λ i → helpModuleHomomorphismLinear {M = M} {N = N} (p i))
                             [ ModuleHomomorphism.linear x ≡ ModuleHomomorphism.linear y ])
                      → (r : (λ i → helpModuleHomomorphismScalar {M = M} {N = N} (p i))
                             [ ModuleHomomorphism.scalar x ≡ ModuleHomomorphism.scalar y ])
                      → (x ≡ y)
ModuleHomomorphism≡ p q r = cong moduleHomo p <*> q <*> r           

--******************************************* is prop *******************************************************

isModuleHomomorphism : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ⟨ M ⟩M → ⟨ N ⟩M) → Type ℓ
isModuleHomomorphism {R = R} {M = M} {N = N} h = Σ (ModuleHomomorphism R M N)
                                                     λ modHom → (ModuleHomomorphism.h modHom) ≡ h

eqHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ⟨ M ⟩M → ⟨ N ⟩M) →
         (p q : isModuleHomomorphism {M = M} {N = N} h) → ModuleHomomorphism.h (fst p) ≡ ModuleHomomorphism.h (fst q)
eqHomo h p q = (snd p) ∙ (sym (snd q))

isPropModuleFunc : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h k : ⟨ M ⟩M → ⟨ N ⟩M} → isProp (h ≡ k)
isPropModuleFunc {N = N} {h = h} {k = k} = liftFunExt (isSetModule N)

isModuleHomomorphismIsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ⟨ M ⟩M → ⟨ N ⟩M) →
                             isProp (isModuleHomomorphism {M = M} {N = N} h)
isModuleHomomorphismIsProp {M = M} {N = N} h p q = Σ≡ (ModuleHomomorphism≡
                                                       (eqHomo h p q)
                                                       (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                                                       isSetModule N
                                                       ((((eqHomo h p q)) i) ((M Module.+ x) y))
                                                       ((N Module.+ ((((eqHomo h p q)) i) x)) ((((eqHomo h p q)) i) y))
                                                       (t x y) (s x y))))
                                                       (ModuleHomomorphism.linear (fst p))
                                                       (ModuleHomomorphism.linear (fst q)))
                                                       (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                                                       isSetModule N
                                                       ((((eqHomo h p q)) i) ((M Module.⋆ r) x))
                                                       ((N Module.⋆ r) ((((eqHomo h p q)) i) x))
                                                       (t r x)
                                                       (s r x))))
                                                       (ModuleHomomorphism.scalar (fst p))
                                                       (ModuleHomomorphism.scalar (fst q))))
                                                       (isProp→PathP (λ i → isPropModuleFunc {M = M} {N = N})
                                                       (snd p)
                                                       (snd q))

--***************************************** compositions ******************************************************

ModuleHomoComp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N L : Module R} → ModuleHomomorphism R M N →
                 ModuleHomomorphism R N L → ModuleHomomorphism R M L
ModuleHomoComp {M = M} {N = N} {L = L} homoH homoK = record {
  h = λ x → ModuleHomomorphism.h homoK (ModuleHomomorphism.h homoH x)  ;
  linear = λ x y →
  (ModuleHomomorphism.h homoK (ModuleHomomorphism.h homoH (((M Module.+ x) y))))
                                  ≡⟨ cong (ModuleHomomorphism.h homoK) (ModuleHomomorphism.linear homoH x y) ⟩
  ModuleHomomorphism.h homoK ((N Module.+ ModuleHomomorphism.h homoH x) (ModuleHomomorphism.h homoH y))
                                  ≡⟨ ModuleHomomorphism.linear homoK (ModuleHomomorphism.h homoH x) (ModuleHomomorphism.h homoH y) ⟩
  (L Module.+ ModuleHomomorphism.h homoK (ModuleHomomorphism.h homoH x)) (ModuleHomomorphism.h homoK (ModuleHomomorphism.h homoH y)) ∎ ;
  scalar = λ r x →
  ModuleHomomorphism.h homoK (ModuleHomomorphism.h homoH ((M Module.⋆ r) x))
                                  ≡⟨ cong (ModuleHomomorphism.h homoK) (ModuleHomomorphism.scalar homoH r x) ⟩
  (ModuleHomomorphism.h homoK ((N Module.⋆ r) (ModuleHomomorphism.h homoH x)))
                                  ≡⟨ (ModuleHomomorphism.scalar homoK r (ModuleHomomorphism.h homoH x)) ⟩
  ((L Module.⋆ r) (ModuleHomomorphism.h homoK (ModuleHomomorphism.h homoH x)) ∎)}

ModuleHomoId : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M : Module R} → ModuleHomomorphism R M M
ModuleHomoId = record {h = λ x → x ;
                       linear = λ x y → refl ;
                       scalar = λ r x → refl}

ModuleHomoIdLeftComp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ModuleHomomorphism R M N) → 
                       ModuleHomoComp ModuleHomoId h ≡ h
ModuleHomoIdLeftComp {M = M} {N = N} h = ModuleHomomorphism≡ refl
                         (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                         isSetModule N
                         (ModuleHomomorphism.h h ((M Module.+ x) y))
                         ((N Module.+ (ModuleHomomorphism.h h x)) (ModuleHomomorphism.h h y))
                         (t x y)
                         (s x y)
                         )))
                         (ModuleHomomorphism.linear (ModuleHomoComp ModuleHomoId h))
                         (ModuleHomomorphism.linear h))
                         (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                         isSetModule N
                         (ModuleHomomorphism.h h ((M Module.⋆ r) x))
                         ((N Module.⋆ r) (ModuleHomomorphism.h h x))
                         (t r x)
                         (s r x)
                         )))
                         (ModuleHomomorphism.scalar (ModuleHomoComp ModuleHomoId h))
                         (ModuleHomomorphism.scalar h))

ModuleHomoIdRightComp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ModuleHomomorphism R M N) → 
                       ModuleHomoComp h ModuleHomoId ≡ h
ModuleHomoIdRightComp {M = M} {N = N} h = ModuleHomomorphism≡ refl
                                          (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                                          isSetModule N
                                          ((ModuleHomomorphism.h h ((M Module.+ x) y)))
                                          (((N Module.+ (ModuleHomomorphism.h h x)) (ModuleHomomorphism.h h y)))
                                          (t x y)
                                          (s x y)
                                          )))
                                          (ModuleHomomorphism.linear (ModuleHomoComp h ModuleHomoId))
                                          (ModuleHomomorphism.linear h))
                                          (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                                          isSetModule N
                                          (ModuleHomomorphism.h h ((M Module.⋆ r) x))
                                          ((N Module.⋆ r) (ModuleHomomorphism.h h x))
                                          (t r x)
                                          (s r x)
                                          )))
                                          (ModuleHomomorphism.scalar (ModuleHomoComp h ModuleHomoId))
                                          (ModuleHomomorphism.scalar h))

ModuleHomoCompAsso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N L G : Module R} → (h : ModuleHomomorphism R M N) →
                     (k : ModuleHomomorphism R N L) → (f : ModuleHomomorphism R L G) →
                     ModuleHomoComp h (ModuleHomoComp k f) ≡ ModuleHomoComp (ModuleHomoComp h k) f
ModuleHomoCompAsso {M = M} {N = N} {L = L} {G = G} h k f = ModuleHomomorphism≡ refl
                           (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                           isSetModule G
                           (ModuleHomomorphism.h (ModuleHomoComp h (ModuleHomoComp k f)) ((M Module.+ x) y))
                           ((G Module.+ (ModuleHomomorphism.h (ModuleHomoComp (ModuleHomoComp h k) f) x)) (ModuleHomomorphism.h (ModuleHomoComp (ModuleHomoComp h k) f) y))
                           (t x y)
                           (s x y)
                           )))
                           (ModuleHomomorphism.linear (ModuleHomoComp h (ModuleHomoComp k f)))
                           (ModuleHomomorphism.linear (ModuleHomoComp (ModuleHomoComp h k) f)))
                           (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                           isSetModule G
                           (ModuleHomomorphism.h (ModuleHomoComp h (ModuleHomoComp k f)) ((M Module.⋆ r) x))
                           ((G Module.⋆ r) (ModuleHomomorphism.h (ModuleHomoComp (ModuleHomoComp h k) f) x))
                           (t r x)
                           (s r x)
                           )))
                           (ModuleHomomorphism.scalar (ModuleHomoComp h (ModuleHomoComp k f)))
                           (ModuleHomomorphism.scalar (ModuleHomoComp (ModuleHomoComp h k) f)))
--****************************************** Help functions for equivalence ***************************************************

modEq→RightCompId : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (modEq : ModuleEquiv M N) →
                   (x : ⟨ N ⟩M) → equivFun (ModuleEquiv.e modEq) (equivFun (invEquiv (ModuleEquiv.e modEq)) x) ≡ x
modEq→RightCompId {N = N} modEq@(moduleIso e isHom+ comm⋆) x =
  equivFun e (equivFun (invEquiv e) x)                     ≡⟨ refl ⟩
  equivFun (compEquiv (invEquiv e) e) x                    ≡⟨ cong (λ e → equivFun e x) (invEquiv-is-rinv (invEquiv e)) ⟩
  equivFun (idEquiv ⟨ N ⟩M) x                              ≡⟨ refl ⟩ 
  x ∎

modEq→LeftCompId : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (modEq : ModuleEquiv M N) →
                   (x : ⟨ M ⟩M) → equivFun (invEquiv (ModuleEquiv.e modEq)) (equivFun (ModuleEquiv.e modEq) x) ≡ x
modEq→LeftCompId {M = M} modEq@(moduleIso e isHom+ comm⋆) x =
  equivFun (invEquiv e) (equivFun e x)                       ≡⟨ refl ⟩
  equivFun ((compEquiv e (invEquiv e))) x                    ≡⟨ cong (λ e → equivFun e x) (invEquiv-is-linv ((invEquiv e))) ⟩
  equivFun (idEquiv ⟨ M ⟩M) x                                ≡⟨ refl ⟩
  x ∎

isHom+Flip : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (modEq : ModuleEquiv M N) →
             (x y : ⟨ N ⟩M) → equivFun (invEquiv (ModuleEquiv.e modEq)) ((N Module.+ x) y) ≡
             (M Module.+ equivFun (invEquiv (ModuleEquiv.e modEq)) x) (equivFun (invEquiv (ModuleEquiv.e modEq)) y)
isHom+Flip {M = M} {N = N} modEq x y =
  f⁻¹ ((N Module.+ x) y)                                    ≡⟨ cong f⁻¹ (cong₂ (λ x y → (N Module.+ x) y)
                                                               (sym (modEq→RightCompId modEq x))
                                                               (sym (modEq→RightCompId modEq y))) ⟩
  f⁻¹ ((N Module.+ (f (f⁻¹ x))) (f (f⁻¹ y)))                ≡⟨ cong f⁻¹ (sym (ModuleEquiv.isHom+ modEq (f⁻¹ x) (f⁻¹ y))) ⟩
  f⁻¹ (f ((M Module.+ f⁻¹ x) (f⁻¹ y)))                      ≡⟨ modEq→LeftCompId modEq ((M Module.+ f⁻¹ x) (f⁻¹ y)) ⟩
  (M Module.+ f⁻¹ x) (f⁻¹ y) ∎
    where
      f = equivFun (ModuleEquiv.e modEq)
      f⁻¹ = equivFun (invEquiv (ModuleEquiv.e modEq))

comm⋆Flip : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (modEq : ModuleEquiv M N) →
             (r : ⟨ R ⟩) (x : ⟨ N ⟩M) → equivFun (invEquiv (ModuleEquiv.e modEq)) ((N Module.⋆ r) x) ≡
                                        (M Module.⋆ r) (equivFun (invEquiv (ModuleEquiv.e modEq)) x)
comm⋆Flip {M = M} {N = N} modEq r x =
  f⁻¹ ((N Module.⋆ r) x)               ≡⟨ cong (λ y → f⁻¹ ((N Module.⋆ r) y)) (sym  (modEq→RightCompId modEq x)) ⟩
  f⁻¹ ((N Module.⋆ r) (f (f⁻¹ x)))     ≡⟨ cong f⁻¹ (sym (ModuleEquiv.comm⋆ modEq r (f⁻¹ x))) ⟩
  f⁻¹ (f ((M Module.⋆ r) (f⁻¹ x)))     ≡⟨ modEq→LeftCompId modEq ((M Module.⋆ r) (f⁻¹ x)) ⟩
  (M Module.⋆ r) (f⁻¹ x) ∎
    where
      f = equivFun (ModuleEquiv.e modEq)
      f⁻¹ = equivFun (invEquiv (ModuleEquiv.e modEq))

ModuleEquivFlip : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → ModuleEquiv M N → ModuleEquiv N M
ModuleEquivFlip modEq@(moduleIso e isHom+ comm⋆) = record { e = invEquiv e ; isHom+ = isHom+Flip modEq ; comm⋆ = comm⋆Flip modEq }

-- --********************************************** ModuleHomo≡ ******************************************** *********************

ModuleHomoLinearIsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleHomomorphism R M N}
                         → (p : ModuleHomomorphism.h x ≡ ModuleHomomorphism.h y)
                         → (λ i → helpModuleHomomorphismLinear {M = M} {N = N} (p i))
                                 [ ModuleHomomorphism.linear x ≡ ModuleHomomorphism.linear y ]
ModuleHomoLinearIsProp {M = M} {N = N} {x = homoH} {y = homoK} p = isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                           isSetModule N
                           (p i ((M Module.+ x) y) )
                           ((N Module.+ ((p i) x)) ((p i) y))
                           (t x y)
                           (s x y))))
                           (ModuleHomomorphism.linear homoH)
                           (ModuleHomomorphism.linear homoK)

ModuleHomoScalarIsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleHomomorphism R M N}
                         → (p : ModuleHomomorphism.h x ≡ ModuleHomomorphism.h y)
                         → (λ i → helpModuleHomomorphismScalar {M = M} {N = N} (p i))
                            [ ModuleHomomorphism.scalar x ≡ ModuleHomomorphism.scalar y ]
ModuleHomoScalarIsProp {M = M} {N = N} {x = homoH} {y = homoK} p = isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
  isSetModule N
  (p i (((M Module.⋆ r) x)))
  ((N Module.⋆ r) (p i x))
  (t r x)
  (s r x))))
  (ModuleHomomorphism.scalar homoH)
  (ModuleHomomorphism.scalar homoK)

ModuleHomo≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {x y : ModuleHomomorphism R M N}
              → (p : ModuleHomomorphism.h x ≡ ModuleHomomorphism.h y)
              → (x ≡ y)
ModuleHomo≡ {ℓ} {R} {M} {N} {x} {y} p = ModuleHomomorphism≡ p
                                        (ModuleHomoLinearIsProp {x = x} {y = y} p)
                                        (ModuleHomoScalarIsProp {x = x} {y = y} p)

--***************************************************** Σ version **********************************************************

ModuleHomoPropΣ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ⟨ M ⟩M → ⟨ N ⟩M) →
                  helpModuleHomomorphismLinear {M = M} {N = N} h →
                  helpModuleHomomorphismScalar {M = M} {N = N} h → 
                  Σ (helpModuleHomomorphismLinear {M = M} {N = N} h)
              (λ x → helpModuleHomomorphismScalar {M = M} {N = N} h)
ModuleHomoPropΣ h lin scal = lin , scal

ModuleHomoPropΣIsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ⟨ M ⟩M → ⟨ N ⟩M) → isProp (
                        Σ (helpModuleHomomorphismLinear {M = M} {N = N} h)
                    (λ x → helpModuleHomomorphismScalar {M = M} {N = N} h))
ModuleHomoPropΣIsProp {M = M} {N = N} h p q = Σ≡Prop (λ lin → λ t s → funExt (λ r → funExt (λ x →
    isSetModule N
    (h (((M Module.⋆ r) x)))
    ((N Module.⋆ r) (h x))
    (t r x)
    (s r x)
  )))
  (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
    isSetModule N
    (h ((M Module.+ x) y) )
    ((N Module.+ (h x)) (h y))
    (t x y)
    (s x y)
  )))
  (fst p)
  (fst q))

ModuleHomoΣ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (h : ⟨ M ⟩M → ⟨ N ⟩M) →
              (lin : helpModuleHomomorphismLinear {M = M} {N = N} h) →
              (sca : helpModuleHomomorphismScalar {M = M} {N = N} h) → 
              Σ (⟨ M ⟩M → ⟨ N ⟩M) (λ h → Σ (helpModuleHomomorphismLinear {M = M} {N = N} h)
              (λ x → helpModuleHomomorphismScalar {M = M} {N = N} h))
ModuleHomoΣ h lin sca = h , (lin , sca)

ModuleHomoΣShort :  {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h : ⟨ M ⟩M → ⟨ N ⟩M} →
              {lin : helpModuleHomomorphismLinear {M = M} {N = N} h} →
              {sca : helpModuleHomomorphismScalar {M = M} {N = N} h} → Type ℓ
ModuleHomoΣShort {M = M} {N = N} {h = h} {lin = lin} {sca = sca} =
  Σ (⟨ M ⟩M → ⟨ N ⟩M) (λ h → Σ (helpModuleHomomorphismLinear {M = M} {N = N} h)
                               (λ x → helpModuleHomomorphismScalar {M = M} {N = N} h))

ModuleHomoΣ→ModuleHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h : ⟨ M ⟩M → ⟨ N ⟩M} →
              {lin : helpModuleHomomorphismLinear {M = M} {N = N} h} →
              {sca : helpModuleHomomorphismScalar {M = M} {N = N} h} →
              ModuleHomoΣShort {M = M} {N = N} {h = h} {lin = lin} {sca = sca} → ModuleHomomorphism R M N
ModuleHomoΣ→ModuleHomo (h , lin , sca) = moduleHomo h lin sca

ModuleHomo→ModuleHomoΣ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h : ⟨ M ⟩M → ⟨ N ⟩M} →
                         {lin : helpModuleHomomorphismLinear {M = M} {N = N} h} →
                         {sca : helpModuleHomomorphismScalar {M = M} {N = N} h} →
                         ModuleHomomorphism R M N →
                         ModuleHomoΣShort {M = M} {N = N} {h = h} {lin = lin} {sca = sca}
ModuleHomo→ModuleHomoΣ (moduleHomo h linear scalar) = h , (linear , scalar)

ModuleHomoΣIso : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h : ⟨ M ⟩M → ⟨ N ⟩M} →
                 {lin : helpModuleHomomorphismLinear {M = M} {N = N} h} →
                 {sca : helpModuleHomomorphismScalar {M = M} {N = N} h} →
                 Iso (ModuleHomomorphism R M N)
                     (ModuleHomoΣShort {M = M} {N = N} {h = h} {lin = lin} {sca = sca})
ModuleHomoΣIso {h = h} {lin = lin} {sca = sca} =
  record {fun = ModuleHomo→ModuleHomoΣ {h = h} {lin = lin} {sca = sca} ;
          inv = ModuleHomoΣ→ModuleHomo {h = h} {lin = lin} {sca = sca} ;
          rightInv = λ z → refl ;
          leftInv = λ z → refl}

ModuleHomoΣEquiv : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h : ⟨ M ⟩M → ⟨ N ⟩M} →
                 {lin : helpModuleHomomorphismLinear {M = M} {N = N} h} →
                 {sca : helpModuleHomomorphismScalar {M = M} {N = N} h} →
                 (ModuleHomomorphism R M N) ≃
                 (ModuleHomoΣShort {M = M} {N = N} {h = h} {lin = lin} {sca = sca})
ModuleHomoΣEquiv {h = h} {lin = lin} {sca = sca} = isoToEquiv (ModuleHomoΣIso {h = h} {lin = lin} {sca = sca})

--ModuleHomoΣIsSet : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h : ⟨ M ⟩M → ⟨ N ⟩M} →
--                   {lin : helpModuleHomomorphismLinear {M = M} {N = N} h} →
--                   {sca : helpModuleHomomorphismScalar {M = M} {N = N} h} →
--                   isSet (ModuleHomoΣShort {M = M} {N = N} {h = h} {lin = lin} {sca = sca})
--ModuleHomoΣIsSet h k p q i = ×≡Prop {!×≡Prop!} ?

--********************************************************** isSet ****************************************************

-- --isSetModuleHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (ModuleHomomorphism R M N)
-- --isSetModuleHomo M N h k p q i j = {!!}

isSetModuleHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (ModuleHomomorphism R M N)
isSetModuleHomo M N h k p q = cong ModuleHomo≡ p≡qHomo
   where
     p≡qHomo : (λ j → ModuleHomomorphism.h (p j)) ≡ (λ j → ModuleHomomorphism.h (q j))
     p≡qHomo = isPropModuleFunc {M = M} {N = N} (λ j → ModuleHomomorphism.h (p j)) (λ j → ModuleHomomorphism.h (q j))

-- homPath : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → {h k : ModuleHomomorphism R M N}
--           → (p : h ≡ k)  → ModuleHomomorphism.h h ≡ ModuleHomomorphism.h k
-- homPath p j = ModuleHomomorphism.h (p j)

-- isSetModuleHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (ModuleHomomorphism R M N)
-- isSetModuleHomo M N h k p q =
--   p                                       ≡⟨ (λ i → ModuleHomomorphism≡ {x = h} {y = k} (p≡pHomo i) (p≡pLinear i) (p≡pScalar i)) ⟩
--   ModuleHomo≡ {x = h} {y = k} (homPath p) ≡⟨ p≡qMain ⟩
--   ModuleHomo≡ {x = h} {y = k} (homPath q) ≡⟨ (λ i → ModuleHomomorphism≡ (q≡qHomo i) (q≡qLinear i) (q≡qScalar i)) ⟩
--   q ∎
--     where
--       p≡qHomo : homPath p ≡ homPath q
--       p≡qHomo = isPropModuleFunc {M = M} {N = N} (homPath p) (homPath q)

--       p≡qMain : ModuleHomo≡ {x = h} {y = k} (homPath p) ≡ ModuleHomo≡ {x = h} {y = k} (homPath q)
--       p≡qMain = cong (ModuleHomo≡ {x = h} {y = k}) p≡qHomo

--       p≡pHomo : (i : I) → ModuleHomomorphism.h h ≡ ModuleHomomorphism.h k
--       p≡pHomo i = refl i
 
--       p≡pLinear : (i : I) → (λ j → helpModuleHomomorphismLinear {M = M} {N = N} ((refl i) j))
--                             [ ModuleHomomorphism.linear h ≡ ModuleHomomorphism.linear k ]
--       p≡pLinear i = isProp→PathP (λ j → λ t s → funExt (λ x → funExt (λ y →
--         isSetModule N
--         (refl i j (M Module.+ x y))
--         ((N Module.+ (refl i j x)) (refl i j y))
--         (t x y)
--         (s x y)
--         )))
--         (ModuleHomomorphism.linear (p i))
--         (ModuleHomomorphism.linear (ModuleHomo≡ {x = h} {y = k} (homPath p) i))

--       p≡pScalar : (i : I) → (λ j → helpModuleHomomorphismScalar ((refl i)  j))
--                             [ ModuleHomomorphism.scalar h ≡ ModuleHomomorphism.scalar k ]
--       p≡pScalar i = isProp→PathP (λ j → λ t s → funExt (λ r → funExt (λ x →
--         isSetModule N
--         (refl i j ((M Module.⋆ r) x))
--         (((N Module.⋆ r) (refl i j x)))
--         (t r x)
--         (s r x)
--         )))
--         (ModuleHomomorphism.scalar (p i))
--         (ModuleHomomorphism.scalar (ModuleHomo≡ {x = h} {y = k} (homPath p) i))

--       q≡qHomo : (i : I) → ModuleHomomorphism.h h ≡ ModuleHomomorphism.h k
--       q≡qHomo i = refl i

--       q≡qLinear : (i : I) → (λ j → helpModuleHomomorphismLinear ((refl i) j))
--                             [ ModuleHomomorphism.linear h ≡ ModuleHomomorphism.linear k ]
--       q≡qLinear i = isProp→PathP (λ j → λ t s → funExt (λ x → funExt (λ y →
--         isSetModule N
--         (refl i j (M Module.+ x y))
--         ((N Module.+ (refl i j x)) (refl i j y))
--         (t x y)
--         (s x y)
--         )))
--         (ModuleHomomorphism.linear (ModuleHomo≡ {x = h} {y = k} (homPath q) i))
--         (ModuleHomomorphism.linear (q i))

--       q≡qScalar : (i : I) → (λ j → helpModuleHomomorphismScalar ((refl i)  j))
--                             [ ModuleHomomorphism.scalar h ≡ ModuleHomomorphism.scalar k ]
--       q≡qScalar i = isProp→PathP (λ j → λ t s → funExt (λ r → funExt (λ x →
--         isSetModule N
--         (refl i j ((M Module.⋆ r) x))
--         (((N Module.⋆ r) (refl i j x)))
--         (t r x)
--         (s r x)
--         )))
--         (ModuleHomomorphism.scalar (ModuleHomo≡ {x = h} {y = k} (homPath q) i))
--         (ModuleHomomorphism.scalar (q i))

-- --isSetModuleHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (ModuleHomomorphism R M N)
-- --isSetModuleHomo M N h k p q = cong ModuleHomo≡ p≡qHomo
-- --    where
-- --      p≡qHomo : homPath p ≡ homPath q
-- --      p≡qHomo = isPropModuleFunc {M = M} {N = N} (homPath p) (homPath q)


-- --isSetModuleHomo : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : Module R) → isSet (ModuleHomomorphism R M N)
-- --isSetModuleHomo M N h k p q i = ModuleHomomorphism≡
-- --  (p≡qHomo i)
-- --  (ModuleHomoLinearIsProp {x = h} {y = k} (p≡qHomo i))
-- --  (ModuleHomoScalarIsProp {x = h} {y = k} (p≡qHomo i))
-- --    where
-- --      p≡qHomo : (λ j → ModuleHomomorphism.h (p j)) ≡ (λ j → ModuleHomomorphism.h (q j))
-- --      p≡qHomo = isPropModuleFunc {M = M} {N = N} (λ j → ModuleHomomorphism.h (p j)) (λ j → ModuleHomomorphism.h (q j))

-- -- ModuleHomoLinearProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : ⟨ M ⟩m → ⟨ N ⟩m) →
-- --                        isProp (helpModuleHomomorphismLinear {M = M} {N = N} h)
-- -- ModuleHomoLinearProp {M = M} {N = N} h p q i x y =
-- --   isSetLeftModule N (h ((M LeftModule.+ x) y)) ( (N LeftModule.+ (h x)) (h y)) (p x y) (q x y) i

-- -- ModuleHomoScalarProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : ⟨ M ⟩m → ⟨ N ⟩m) →
-- --                        isProp (helpModuleHomomorphismScalar {M = M} {N = N} h)
-- -- ModuleHomoScalarProp {M = M} {N = N} h p q i r x =
-- --   isSetLeftModule N (h ((M LeftModule.⋆ r) x)) ((N LeftModule.⋆ r) (h x)) (p r x ) (q r x) i

-- -- ModuleHomoLinearProp2 : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h k : ⟨ M ⟩m → ⟨ N ⟩m) →
-- --                         (p : h ≡ k) → {hLin : helpModuleHomomorphismLinear {M = M} {N = N} (p i0)} →
-- --                         {kLin : helpModuleHomomorphismLinear {M = M} {N = N} (p i1)} →
-- --                          (λ i → helpModuleHomomorphismLinear {M = M} {N = N} (p i)) [ hLin ≡ kLin ]
-- -- ModuleHomoLinearProp2 {M = M} {N = N} h k p {hLin} {kLin} = isProp→PathP (λ i → ModuleHomoLinearProp {M = M} {N = N} (p i)) hLin kLin

-- -- ModuleHomoScalarProp2 : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h k : ⟨ M ⟩m → ⟨ N ⟩m) →
-- --                         (p : h ≡ k) → {hSca : helpModuleHomomorphismScalar {M = M} {N = N} (p i0)} →
-- --                         {kSca : helpModuleHomomorphismScalar {M = M} {N = N} (p i1)} →
-- --                          (λ i → helpModuleHomomorphismScalar {M = M} {N = N} (p i)) [ hSca  ≡ kSca ]
-- -- ModuleHomoScalarProp2 {M = M} {N = N} h k p {hSca} {kSca} = isProp→PathP (λ i → ModuleHomoScalarProp {M = M} {N = N} (p i)) hSca kSca

-- -- homIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → Type ℓ
-- -- homIsProp {R = R} {M = M} {N = N} = (h : LeftModuleHomomorphism R M N) → (k : LeftModuleHomomorphism R M N) → LeftModuleHomomorphism.h h ≡ LeftModuleHomomorphism.h k

-- -- linIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → Type ℓ
-- -- linIsProp {R = R} {M = M} {N = N} = (h : LeftModuleHomomorphism R M N) → helpModuleHomomorphismLinear {M = M} {N = N} (LeftModuleHomomorphism.h h)

-- -- scaIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → Type ℓ
-- -- scaIsProp {R = R} {M = M} {N = N} = (h : LeftModuleHomomorphism R M N) → helpModuleHomomorphismScalar {M = M} {N = N} (LeftModuleHomomorphism.h h)

-- -- --isSetModuleModuleHomo2 : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → {x y : LeftModuleHomomorphism R M N} →
-- -- --                         isSet (⟨ M ⟩m → ⟨ N ⟩m) →
-- -- --                         isProp (linIsProp {M = M} {N = N}) →
-- -- --                         isProp (scaIsProp {M = M} {N = N}) →
-- -- --                         isProp (x ≡ y)
-- -- --isSetModuleModuleHomo2 {x = x} {y = y} setHom propLin propScal p q i j = record {
-- -- --  h = setHom (LeftModuleHomomorphism.h (p i)) (LeftModuleHomomorphism.h (q i)) (λ k → LeftModuleHomomorphism.h {!!}) {!!} i {!j!} ;
-- -- --  linear = {!!} ;
-- -- --  scalar = {!!}}

-- -- --isSetModuleModuleHomo : {ℓ : Level} → {R : Ring {ℓ}} → (M N : LeftModule R) → isSet (LeftModuleHomomorphism R M N)
-- -- --isSetModuleModuleHomo M N h k p q = cong LeftModuleHomomorphism≡
-- -- --                                    (λ i → isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) <*>
-- -- --                                    isProp→PathP (λ i → λ t s → λ j → λ k → ModuleHomoLinearProp2 (LeftModuleHomomorphism.h (p i)) (LeftModuleHomomorphism.h (q i))
-- -- --                                    {!!} --(λ l → isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) l)
-- -- --                                    k) (λ i → LeftModuleHomomorphism.linear (p i)) (λ i → LeftModuleHomomorphism.linear (q i)) <*>
-- -- --                                    {!!}

-- -- --isSetModuleModuleHomo : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → isSet (LeftModuleHomomorphism R M N)
-- -- --isSetModuleModuleHomo {M = M} {N = N} h k p q = λ i → LeftModuleHomomorphism≡
-- -- --  (isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i)
-- -- --  (λ j → λ x y → isSetLeftModule N ((isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) j ((M LeftModule.+ x) y)) ((N LeftModule.+ ((isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) j x)) ((isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) j y)) (LeftModuleHomomorphism.linear {!!} x y) {!!} j)
-- -- --  (λ j → λ x y → {!!})
-- -- --  {!!}
