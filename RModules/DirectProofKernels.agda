{-# OPTIONS --cubical #-}

module ThesisWork.RModules.DirectProofKernels where

--open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
open import Cubical.Data.Sigma.Base
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
open import ThesisWork.BasicCategoryTheory.Limits.Kernel
open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import ThesisWork.RModules.CommutativeRing
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Module.Base
open import ThesisWork.RModules.RModuleHomomorphism
open import ThesisWork.RModules.RModuleHomomorphismProperties
open import ThesisWork.RModules.RModule
open import ThesisWork.RModules.RMod
open import Cubical.Foundations.Structure
open import ThesisWork.CompatibilityCode
open import ThesisWork.SetSigmaType
open import Agda.Builtin.Cubical.HCompU
open import Cubical.Core.Primitives renaming
  (_[_≡_] to _[_≡_]P)

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.PropositionalTruncation.Base
open import ThesisWork.RModules.RModuleProperties
open import ThesisWork.SetQuotientHelp
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import Cubical.HITs.PropositionalTruncation.Properties renaming
  (elim to elimHprop ;
   elim2 to elim2Hprop ;
   elim3 to elim3Hprop ;
   rec to recHprop ;
   rec2 to rec2Hprop )

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Binary.Base
open import ThesisWork.RModules.MonicToInjective

open import ThesisWork.RModules.RModProperties


monicsAreKernelsRModDirect : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A S : Precategory.ob (RModPreCat R)} →
                             (k : Precategory.hom (RModPreCat R) S A) → isMonic (RMod {R = R}) k →
                             ∥ Σ (Precategory.ob (RModPreCat R))
                                 (λ B → Σ (Precategory.hom (RModPreCat R) A B)
                                          (λ f → isKernel (RMod {R = R}) (hasZeroObjectRMod R) f k)) ∥
monicsAreKernelsRModDirect R {A} {S} k monk =
  ∣ fst kcoK , (CoKernel.coKer (snd kcoK)) ,
    ((kernelConst k
                  (CoKernel.coKerComp (snd kcoK))
                  h'Help
                  monk) ,
    refl) ∣
    where  
      k' = ModuleHomomorphism.h k
      0A = Module.0m A
      _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
      x +A y = (A Module.+ x) y
      _⋆A_ = Module._⋆_ A

      kcoK = hasAllCoKernelsRModNonTrunk R k

      _∘_ = Precategory.seq (RModPreCat R)
      0a : (A B : Precategory.ob (RModPreCat R))  → Precategory.hom (RModPreCat R) A B
      0a A B = ZeroArrow.f (getZeroArrow (RMod {R = R}) {A = A} {B = B} (hasZeroObjectRMod R))

      getRel : (x y : ⟨ A ⟩M) → [ x ] ≡ [ y ] → coKernelRel R k x y
      getRel = effective (coKernelRelMonicProp R k monk) (coKernelRelisEquiv R k)
    
      h'Help : {D : Module R} → (h : ModuleHomomorphism R D A) → h ∘ CoKernel.coKer (snd (hasAllCoKernelsRModNonTrunk R k)) ≡ 0a D (makeCoKernelObjRMod R k) → Σ (ModuleHomomorphism R D S) (λ h' → h' ∘ k ≡ h)
      h'Help {E} h hcok=0 =
        (moduleHomo (λ e → fst (getRel 0A (ModuleHomomorphism.h h e) λ i → ModuleHomomorphism.h (sym hcok=0 i) e))
                    (λ e e' → a+a' e e' ≡⟨ MonicToInj R k monk (a+a' e e') ((S Module.+ a e e') (a' e e'))
                                           (k' (a+a' e e') ≡⟨ sym (ModuleZeroLeft {M = A} (k' (a+a' e e'))) ⟩
                                           (0A +A (k' (a+a' e e'))) ≡⟨ sym (snd (getRelHelp (e +E e'))) ⟩
                                           (h' (e +E e'))      ≡⟨ ModuleHomomorphism.linear h e e' ⟩
                                           ((h' e) +A (h' e')) ≡⟨ cong₂ _+A_
                                                                  (snd (getRelHelp e))
                                                                  (snd (getRelHelp e')) ⟩
                                           ((0A +A k' (a e e')) +A (0A +A k' (a' e e'))) ≡⟨ cong₂ _+A_
                                                                                            (ModuleZeroLeft {M = A} (k' (a e e')))
                                                                                            (ModuleZeroLeft {M = A} (k' (a' e e'))) ⟩
                                           (k' (a e e') +A k' (a' e e')) ≡⟨ sym (ModuleHomomorphism.linear k (a e e') (a' e e')) ⟩
                                           k' ((a e e') +S (a' e e')) ∎) ⟩
                              ((a e e') +S (a' e e')) ∎)
                    λ r e → a'' r e ≡⟨ MonicToInj R k monk (a'' r e) (r ⋆S (a''' e))
                                       (k' (a'' r e) ≡⟨ sym (ModuleZeroLeft {M = A} (k' (a'' r e))) ⟩
                                       (0A +A k' (a'' r e)) ≡⟨ sym (snd (getRelHelp (r ⋆E e))) ⟩
                                       h' (r ⋆E e) ≡⟨ ModuleHomomorphism.scalar h r e ⟩
                                       (r ⋆A h' e) ≡⟨ cong (λ x → r ⋆A x) (snd (getRelHelp e)) ⟩
                                       (r ⋆A (0A +A k' (a''' e))) ≡⟨ cong (λ x → r ⋆A x) (ModuleZeroLeft {M = A} (k' (a''' e))) ⟩
                                       (r ⋆A k' (a''' e)) ≡⟨ sym (ModuleHomomorphism.scalar k r (a''' e)) ⟩
                                       k' (r ⋆S (a''' e)) ∎) ⟩
                            (r ⋆S (a''' e)) ∎) ,
        ModuleHomo≡ (funExt (λ e → k' (a''' e) ≡⟨ sym (ModuleZeroLeft {M = A} (k' (a''' e))) ⟩
                                   (0A +A k' (a''' e)) ≡⟨ sym (snd (getRelHelp e)) ⟩
                                   h' e ∎))
          where
            _+E_ = Module._+_ E
            _⋆E_ = Module._⋆_ E
            _+S_ = Module._+_ S
            _⋆S_ = Module._⋆_ S
            h' = ModuleHomomorphism.h h

            getRelHelp : (e : ⟨ E ⟩M) → coKernelRel R k 0A (h' e)
            getRelHelp e = getRel 0A (h' e) (λ i → ModuleHomomorphism.h (sym hcok=0 i) e)
            
            a+a' : (e e' : ⟨ E ⟩M) → ⟨ S ⟩M
            a+a' e e' = fst (getRelHelp (e +E e'))
            a : (e e' : ⟨ E ⟩M) → ⟨ S ⟩M
            a e e' = fst (getRelHelp e)
            a' : (e e' : ⟨ E ⟩M) → ⟨ S ⟩M
            a' e e' = fst (getRelHelp e')

            a'' : (r : ⟨ R ⟩) → (e : ⟨ E ⟩M) → ⟨ S ⟩M
            a'' r e = fst (getRelHelp (r ⋆E e))

            a''' : (e : ⟨ E ⟩M) → ⟨ S ⟩M
            a''' e = fst (getRelHelp e)

-- epicsAreCokernelsRModDirect : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
--                               (f : Precategory.hom (RModPreCat R) A B) → isEpic (RMod {R = R}) f →
--                               ∥ Σ (Precategory.ob (RModPreCat R))
--                                   (λ S → Σ (Precategory.hom (RModPreCat R) S A)
--                                            (λ k → isCoKernel (RMod {R = R}) (hasZeroObjectRMod R) k f)) ∥
-- epicsAreCokernelsRModDirect R {A} {B} f fEpi =
--   ∣ (fst fKer , (Kernel.ker (snd fKer)) ,
--     ((coKernelConst f
--                     (Kernel.kerComp (snd fKer))
--                     h'Help
--                     fEpi) ,
--     refl)) ∣
--     where
--       fKer = hasAllKernelsRModNonTrunk R f
--       _∘_ = Precategory.seq (RModPreCat R)
--       0a : (A B : Precategory.ob (RModPreCat R))  → Precategory.hom (RModPreCat R) A B
--       0a A B = ZeroArrow.f (getZeroArrow (RMod {R = R}) {A = A} {B = B} (hasZeroObjectRMod R))

--       h'Help : {D : Module R} → (h : ModuleHomomorphism R A D) → (Kernel.ker (snd fKer)) ∘ h ≡ 0a (makeKernelObjRMod R f) D → Σ (ModuleHomomorphism R B D) (λ h' → f ∘ h' ≡ h)
--       h'Help {D} h kerf∘h=0 =
--         recHprop (λ p q → Σ≡ (fEpi D (fst p) (fst q) ((f ∘ (fst p)) ≡⟨ snd p ⟩
--                                                                h ≡⟨ sym (snd q) ⟩
--                                                                (f ∘ fst q) ∎)) (toPathP (isSetModuleHomo A D _ _ _ _)))
--                  {!!}
--                  (EpicAreSurj R f fEpi {!!})
          
