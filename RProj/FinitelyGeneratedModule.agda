{-# OPTIONS --cubical #-}

module ThesisWork.RProj.FinitelyGeneratedModule where

open import ThesisWork.RModules.RModule
open import Cubical.Data.Vec.Base
open import Cubical.Data.List.Base
open import Cubical.Foundations.Prelude
open import ThesisWork.RModules.CommutativeRing
open import Cubical.Data.Nat
open import Cubical.Foundations.Structure
open import Cubical.Data.FinData.Base
open import ThesisWork.RModules.RModuleHomomorphismProperties
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

sumGenerators : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (M : Module R) → {n : ℕ} →
                (gVec : Vec ⟨ M ⟩M n) → (rVec : Vec ⟨ R ⟩ n) → ⟨ M ⟩M
sumGenerators R M [] [] = Module.0m M
sumGenerators R M (g ∷ gVec) (r ∷ rVec) = (r ⋆M g) +M (sumGenerators R M gVec rVec)
  where
    _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
    g +M h = (M Module.+ g) h
    _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
    r ⋆M g = (M Module.⋆ r) g

finiteGenerator : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → Type ℓ
finiteGenerator {R = R} M = Σ ℕ λ n →
                              Σ (Vec ⟨ M ⟩M n) (λ V → (g : ⟨ M ⟩M) →
                                Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R M V r ≡ g)

isFinitelyGenerated : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → Type ℓ
isFinitelyGenerated M = ∥ (finiteGenerator M) ∥

FinGenIsProp : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M : Module R) → isProp (isFinitelyGenerated M)
FinGenIsProp M = propTruncIsProp

--************************************************ Properties ***************************************

moveInvGen : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (M : Module R) → {n : ℕ} →
             (gVec : Vec ⟨ M ⟩M (1 + n)) → (rVec : Vec ⟨ R ⟩ (1 + n)) → (g : ⟨ M ⟩M) →
             sumGenerators R M gVec rVec ≡ g →
             sumGenerators R M (tail gVec) (tail rVec) ≡
               (M Module.+ g) ((Module.- M) ((M Module.⋆ (head rVec)) (head gVec)))
moveInvGen R M (g1 ∷ gVec) (r1 ∷ rVec) g sumGen =
  sumGenerators R M gVec rVec
                                         ≡⟨ sym (ModuleZeroLeft {M = M} (sumGenerators R M gVec rVec)) ⟩
  (0M +M (sumGenerators R M gVec rVec))
           ≡⟨ cong (λ x → x +M (sumGenerators R M gVec rVec)) (sym (ModuleInvLeft {M = M} (r1 ⋆M g1))) ⟩
  (((-M (r1 ⋆M g1)) +M (r1 ⋆M g1)) +M (sumGenerators R M gVec rVec))
               ≡⟨ sym (Module+Isasso {M = M} (-M (r1 ⋆M g1)) (r1 ⋆M g1) (sumGenerators R M gVec rVec)) ⟩
  ((-M (r1 ⋆M g1)) +M ((r1 ⋆M g1) +M (sumGenerators R M gVec rVec)))
                  ≡⟨ cong (λ x → (-M (r1 ⋆M g1)) +M x) sumGen ⟩
  ((-M (r1 ⋆M g1)) +M g)                                       ≡⟨ ModuleIsAb {M = M} (-M (r1 ⋆M g1)) g ⟩
  (g +M (-M (r1 ⋆M g1))) ∎
    where
      0M = Module.0m M
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
      g +M h = (M Module.+ g) h
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
      r ⋆M g = (M Module.⋆ r) g
      -M_ : ⟨ M ⟩M → ⟨ M ⟩M
      -M g = (Module.- M) g

Eq2FirstGen : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (M : Module R) → {n : ℕ} →
             (gVec : Vec ⟨ M ⟩M (2 + n)) → (rVec : Vec ⟨ R ⟩ (2 + n)) → (g : ⟨ M ⟩M) →
             sumGenerators R M gVec rVec ≡ g →
             (M Module.+ (M Module.⋆ (head rVec)) (head gVec))
               ((M Module.+ ((M Module.⋆ (head (tail rVec))) (head (tail gVec))))
                 (sumGenerators R M (tail (tail gVec)) (tail (tail rVec)))) ≡ g
Eq2FirstGen R M (g1 ∷ g2 ∷ gVec) (r1 ∷ r2 ∷ rVec) g sumEq = sumEq

--(Proof that generators can be unique)
canEliminateDuplicates : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (M : Module R) → {n : ℕ} →
                         (gVec : Vec ⟨ M ⟩M (2 + n)) → (m k : ℕ) → head gVec ≡ head (tail gVec) →
                         ((g : ⟨ M ⟩M) → Σ (Vec ⟨ R ⟩ (2 + n)) λ r → sumGenerators R M gVec r ≡ g) →
                          Σ (Vec ⟨ M ⟩M (1 + n)) (λ V → (g : ⟨ M ⟩M) →
                              Σ (Vec ⟨ R ⟩ (1 + n)) λ r → sumGenerators R M V r ≡ g)
canEliminateDuplicates R M {n} (g1 ∷ g2 ∷ gVec) m k g1=g2 finGengVec =
  (g1 ∷ gVec) , (λ g → ((r1 g) +R (r2 g) ∷ restR g) ,
    (((((r1 g) +R (r2 g)) ⋆M g1) +M (rest g))        ≡⟨ cong (λ x → x +M (rest g))
                                                          (ModuleLDist {M = M} (r1 g) (r2 g) g1) ⟩
    ((((r1 g) ⋆M g1) +M ((r2 g) ⋆M g1)) +M (rest g))
                              ≡⟨ sym (Module+Isasso {M = M} ((r1 g) ⋆M g1) ((r2 g) ⋆M g1) (rest g)) ⟩
    (((r1 g) ⋆M g1) +M (((r2 g) ⋆M g1) +M (rest g)))
                                ≡⟨ cong (λ x → ((r1 g) ⋆M g1) +M (((r2 g) ⋆M x) +M (rest g))) g1=g2 ⟩
    (((r1 g) ⋆M g1) +M (((r2 g) ⋆M g2) +M (rest g)))
                                ≡⟨ Eq2FirstGen R M (g1 ∷ g2 ∷ gVec) (rVec g) g (snd (finGengVec g)) ⟩
    g ∎))
    where
      _+R_ : ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
      r +R s = ((snd R) CommutativeRingStr.+ r) s
      _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
      g +M h = (M Module.+ g) h
      _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
      r ⋆M g = (M Module.⋆ r) g
      rVec : (g : ⟨ M ⟩M) → Vec ⟨ R ⟩ (2 + n)
      rVec g = fst (finGengVec g)
      r1 : (g : ⟨ M ⟩M) → ⟨ R ⟩
      r1 g = head (rVec g)
      r2 : (g : ⟨ M ⟩M) → ⟨ R ⟩
      r2 g = head (tail (rVec g))
      restR : (g : ⟨ M ⟩M) → Vec ⟨ R ⟩ n
      restR g = tail (tail (rVec g))
      rest : (g : ⟨ M ⟩M) → ⟨ M ⟩M
      rest g = (sumGenerators R M gVec (tail (tail (rVec g))))
