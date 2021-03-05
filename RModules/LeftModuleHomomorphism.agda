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
isPropModuleFunc {N = N} {h = h} {k = k} = liftFunExt (isSetLeftModule N)

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

--***************************************** compositions ******************************************************

ModuleHomoComp : {ℓ : Level} → {R : Ring {ℓ}} → {M N L : LeftModule R} → LeftModuleHomomorphism R M N →
                 LeftModuleHomomorphism R N L → LeftModuleHomomorphism R M L
ModuleHomoComp {M = M} {N = N} {L = L} homoH homoK = record {h = λ x → LeftModuleHomomorphism.h homoK (LeftModuleHomomorphism.h homoH x)  ;
                                     linear = λ x y →
  (LeftModuleHomomorphism.h homoK (LeftModuleHomomorphism.h homoH (((M LeftModule.+ x) y))))                             ≡⟨ cong (LeftModuleHomomorphism.h homoK) (LeftModuleHomomorphism.linear homoH x y) ⟩
   LeftModuleHomomorphism.h homoK ((N LeftModule.+ LeftModuleHomomorphism.h homoH x) (LeftModuleHomomorphism.h homoH y)) ≡⟨ LeftModuleHomomorphism.linear homoK (LeftModuleHomomorphism.h homoH x) (LeftModuleHomomorphism.h homoH y) ⟩
   (L LeftModule.+ LeftModuleHomomorphism.h homoK (LeftModuleHomomorphism.h homoH x)) (LeftModuleHomomorphism.h homoK (LeftModuleHomomorphism.h homoH y)) ∎ ;
                                     scalar = λ r x →
  LeftModuleHomomorphism.h homoK (LeftModuleHomomorphism.h homoH ((M LeftModule.⋆ r) x))   ≡⟨ cong (LeftModuleHomomorphism.h homoK) (LeftModuleHomomorphism.scalar homoH r x) ⟩
  (LeftModuleHomomorphism.h homoK ((N LeftModule.⋆ r) (LeftModuleHomomorphism.h homoH x))) ≡⟨ (LeftModuleHomomorphism.scalar homoK r (LeftModuleHomomorphism.h homoH x)) ⟩
  ((L LeftModule.⋆ r) (LeftModuleHomomorphism.h homoK (LeftModuleHomomorphism.h homoH x)) ∎)}

ModuleHomoId : {ℓ : Level} → {R : Ring {ℓ}} → {M : LeftModule R} → LeftModuleHomomorphism R M M
ModuleHomoId = record {h = λ x → x ;
                       linear = λ x y → refl ;
                       scalar = λ r x → refl}

ModuleHomoIdLeftComp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : LeftModuleHomomorphism R M N) → 
                       ModuleHomoComp ModuleHomoId h ≡ h
ModuleHomoIdLeftComp {M = M} {N = N} h = LeftModuleHomomorphism≡ refl
                         (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                         isSetLeftModule N
                         (LeftModuleHomomorphism.h h ((M LeftModule.+ x) y))
                         ((N LeftModule.+ (LeftModuleHomomorphism.h h x)) (LeftModuleHomomorphism.h h y))
                         (t x y)
                         (s x y)
                         )))
                         (LeftModuleHomomorphism.linear (ModuleHomoComp ModuleHomoId h))
                         (LeftModuleHomomorphism.linear h))
                         (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                         isSetLeftModule N
                         (LeftModuleHomomorphism.h h ((M LeftModule.⋆ r) x))
                         ((N LeftModule.⋆ r) (LeftModuleHomomorphism.h h x))
                         (t r x)
                         (s r x)
                         )))
                         (LeftModuleHomomorphism.scalar (ModuleHomoComp ModuleHomoId h))
                         (LeftModuleHomomorphism.scalar h))

ModuleHomoIdRightComp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : LeftModuleHomomorphism R M N) → 
                       ModuleHomoComp h ModuleHomoId ≡ h
ModuleHomoIdRightComp {M = M} {N = N} h = LeftModuleHomomorphism≡ refl
                                          (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                                          isSetLeftModule N
                                          ((LeftModuleHomomorphism.h h ((M LeftModule.+ x) y)))
                                          (((N LeftModule.+ (LeftModuleHomomorphism.h h x)) (LeftModuleHomomorphism.h h y)))
                                          (t x y)
                                          (s x y)
                                          )))
                                          (LeftModuleHomomorphism.linear (ModuleHomoComp h ModuleHomoId))
                                          (LeftModuleHomomorphism.linear h))
                                          (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                                          isSetLeftModule N
                                          (LeftModuleHomomorphism.h h ((M LeftModule.⋆ r) x))
                                          ((N LeftModule.⋆ r) (LeftModuleHomomorphism.h h x))
                                          (t r x)
                                          (s r x)
                                          )))
                                          (LeftModuleHomomorphism.scalar (ModuleHomoComp h ModuleHomoId))
                                          (LeftModuleHomomorphism.scalar h))

ModuleHomoCompAsso : {ℓ : Level} → {R : Ring {ℓ}} → {M N L G : LeftModule R} → (h : LeftModuleHomomorphism R M N) →
                     (k : LeftModuleHomomorphism R N L) → (f : LeftModuleHomomorphism R L G) →
                     ModuleHomoComp h (ModuleHomoComp k f) ≡ ModuleHomoComp (ModuleHomoComp h k) f
ModuleHomoCompAsso {M = M} {N = N} {L = L} {G = G} h k f = LeftModuleHomomorphism≡ refl
                           (isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                           isSetLeftModule G
                           (LeftModuleHomomorphism.h (ModuleHomoComp h (ModuleHomoComp k f)) ((M LeftModule.+ x) y))
                           ((G LeftModule.+ (LeftModuleHomomorphism.h (ModuleHomoComp (ModuleHomoComp h k) f) x)) (LeftModuleHomomorphism.h (ModuleHomoComp (ModuleHomoComp h k) f) y))
                           (t x y)
                           (s x y)
                           )))
                           (LeftModuleHomomorphism.linear (ModuleHomoComp h (ModuleHomoComp k f)))
                           (LeftModuleHomomorphism.linear (ModuleHomoComp (ModuleHomoComp h k) f)))
                           (isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
                           isSetLeftModule G
                           (LeftModuleHomomorphism.h (ModuleHomoComp h (ModuleHomoComp k f)) ((M LeftModule.⋆ r) x))
                           ((G LeftModule.⋆ r) (LeftModuleHomomorphism.h (ModuleHomoComp (ModuleHomoComp h k) f) x))
                           (t r x)
                           (s r x)
                           )))
                           (LeftModuleHomomorphism.scalar (ModuleHomoComp h (ModuleHomoComp k f)))
                           (LeftModuleHomomorphism.scalar (ModuleHomoComp (ModuleHomoComp h k) f)))

--********************************* TODO : Help funcs 2, Trying to prove LeftModuleHomomorphism R M N is a set *********************

ModuleHomoLinearIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → {x y : LeftModuleHomomorphism R M N}
                         → (p : LeftModuleHomomorphism.h x ≡ LeftModuleHomomorphism.h y)
                         → (λ i → helpModuleHomomorphismLinear {M = M} {N = N} (p i))
                                 [ LeftModuleHomomorphism.linear x ≡ LeftModuleHomomorphism.linear y ]
ModuleHomoLinearIsProp {M = M} {N = N} {x = homoH} {y = homoK} p = isProp→PathP (λ i → λ t s → funExt (λ x → funExt (λ y →
                           isSetLeftModule N
                           (p i ((M LeftModule.+ x) y) )
                           ((N LeftModule.+ ((p i) x)) ((p i) y))
                           (t x y)
                           (s x y))))
                           (LeftModuleHomomorphism.linear homoH)
                           (LeftModuleHomomorphism.linear homoK)

ModuleHomoScalarIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → {x y : LeftModuleHomomorphism R M N}
                         → (p : LeftModuleHomomorphism.h x ≡ LeftModuleHomomorphism.h y)
                         → (λ i → helpModuleHomomorphismScalar {M = M} {N = N} (p i))
                            [ LeftModuleHomomorphism.scalar x ≡ LeftModuleHomomorphism.scalar y ]
ModuleHomoScalarIsProp {M = M} {N = N} {x = homoH} {y = homoK} p = isProp→PathP (λ i → λ t s → funExt (λ r → funExt (λ x →
  isSetLeftModule N
  (p i (((M LeftModule.⋆ r) x)))
  ((N LeftModule.⋆ r) (p i x))
  (t r x)
  (s r x))))
  (LeftModuleHomomorphism.scalar homoH)
  (LeftModuleHomomorphism.scalar homoK)

ModuleHomo≡ : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → {x y : LeftModuleHomomorphism R M N}
              → (p : LeftModuleHomomorphism.h x ≡ LeftModuleHomomorphism.h y)
              → (x ≡ y)
ModuleHomo≡ {ℓ} {R} {M} {N} {x} {y} p = LeftModuleHomomorphism≡ p
                                        (ModuleHomoLinearIsProp {x = x} {y = y} p)
                                        (ModuleHomoScalarIsProp {x = x} {y = y} p)

ModuleHomoLinearProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : ⟨ M ⟩m → ⟨ N ⟩m) →
                       isProp (helpModuleHomomorphismLinear {M = M} {N = N} h)
ModuleHomoLinearProp {M = M} {N = N} h p q i x y =
  isSetLeftModule N (h ((M LeftModule.+ x) y)) ( (N LeftModule.+ (h x)) (h y)) (p x y) (q x y) i

ModuleHomoScalarProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h : ⟨ M ⟩m → ⟨ N ⟩m) →
                       isProp (helpModuleHomomorphismScalar {M = M} {N = N} h)
ModuleHomoScalarProp {M = M} {N = N} h p q i r x =
  isSetLeftModule N (h ((M LeftModule.⋆ r) x)) ((N LeftModule.⋆ r) (h x)) (p r x ) (q r x) i

ModuleHomoLinearProp2 : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h k : ⟨ M ⟩m → ⟨ N ⟩m) →
                        (p : h ≡ k) → {hLin : helpModuleHomomorphismLinear {M = M} {N = N} (p i0)} →
                        {kLin : helpModuleHomomorphismLinear {M = M} {N = N} (p i1)} →
                         (λ i → helpModuleHomomorphismLinear {M = M} {N = N} (p i)) [ hLin ≡ kLin ]
ModuleHomoLinearProp2 {M = M} {N = N} h k p {hLin} {kLin} = isProp→PathP (λ i → ModuleHomoLinearProp {M = M} {N = N} (p i)) hLin kLin

ModuleHomoScalarProp2 : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → (h k : ⟨ M ⟩m → ⟨ N ⟩m) →
                        (p : h ≡ k) → {hSca : helpModuleHomomorphismScalar {M = M} {N = N} (p i0)} →
                        {kSca : helpModuleHomomorphismScalar {M = M} {N = N} (p i1)} →
                         (λ i → helpModuleHomomorphismScalar {M = M} {N = N} (p i)) [ hSca  ≡ kSca ]
ModuleHomoScalarProp2 {M = M} {N = N} h k p {hSca} {kSca} = isProp→PathP (λ i → ModuleHomoScalarProp {M = M} {N = N} (p i)) hSca kSca

homIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → Type ℓ
homIsProp {R = R} {M = M} {N = N} = (h : LeftModuleHomomorphism R M N) → (k : LeftModuleHomomorphism R M N) → LeftModuleHomomorphism.h h ≡ LeftModuleHomomorphism.h k

linIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → Type ℓ
linIsProp {R = R} {M = M} {N = N} = (h : LeftModuleHomomorphism R M N) → helpModuleHomomorphismLinear {M = M} {N = N} (LeftModuleHomomorphism.h h)

scaIsProp : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → Type ℓ
scaIsProp {R = R} {M = M} {N = N} = (h : LeftModuleHomomorphism R M N) → helpModuleHomomorphismScalar {M = M} {N = N} (LeftModuleHomomorphism.h h)

--isSetModuleModuleHomo2 : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → {x y : LeftModuleHomomorphism R M N} →
--                         isSet (⟨ M ⟩m → ⟨ N ⟩m) →
--                         isProp (linIsProp {M = M} {N = N}) →
--                         isProp (scaIsProp {M = M} {N = N}) →
--                         isProp (x ≡ y)
--isSetModuleModuleHomo2 {x = x} {y = y} setHom propLin propScal p q i j = record {
--  h = setHom (LeftModuleHomomorphism.h (p i)) (LeftModuleHomomorphism.h (q i)) (λ k → LeftModuleHomomorphism.h {!!}) {!!} i {!j!} ;
--  linear = {!!} ;
--  scalar = {!!}}

--isSetModuleModuleHomo : {ℓ : Level} → {R : Ring {ℓ}} → (M N : LeftModule R) → isSet (LeftModuleHomomorphism R M N)
--isSetModuleModuleHomo M N h k p q = cong LeftModuleHomomorphism≡
--                                    (λ i → isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) <*>
--                                    isProp→PathP (λ i → λ t s → λ j → λ k → ModuleHomoLinearProp2 (LeftModuleHomomorphism.h (p i)) (LeftModuleHomomorphism.h (q i))
--                                    {!!} --(λ l → isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) l)
--                                    k) (λ i → LeftModuleHomomorphism.linear (p i)) (λ i → LeftModuleHomomorphism.linear (q i)) <*>
--                                    {!!}

--isSetModuleModuleHomo : {ℓ : Level} → {R : Ring {ℓ}} → {M N : LeftModule R} → isSet (LeftModuleHomomorphism R M N)
--isSetModuleModuleHomo {M = M} {N = N} h k p q = λ i → LeftModuleHomomorphism≡
--  (isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i)
--  (λ j → λ x y → isSetLeftModule N ((isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) j ((M LeftModule.+ x) y)) ((N LeftModule.+ ((isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) j x)) ((isPropModuleFunc {M = M} {N = N} (λ j → LeftModuleHomomorphism.h (p j)) (λ j → LeftModuleHomomorphism.h (q j)) i) j y)) (LeftModuleHomomorphism.linear {!!} x y) {!!} j)
--  (λ j → λ x y → {!!})
--  {!!}
