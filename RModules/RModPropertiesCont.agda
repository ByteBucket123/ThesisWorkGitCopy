{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModPropertiesCont where

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

open import ThesisWork.BasicCategoryTheory.IsomorphismHelp

open import ThesisWork.RModules.RModProperties

--Might take a long time to type check.
epicsAreCokernelsRMod : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
                        (f : Precategory.hom (RModPreCat R) A B) → isEpic (RMod {R = R}) f →
                        ∥ Σ (Precategory.ob (RModPreCat R))
                           (λ S → Σ (Precategory.hom (RModPreCat R) S A)
                                    (λ k → isCoKernel (RMod {R = R}) (hasZeroObjectRMod R) k f)) ∥
epicsAreCokernelsRMod R {A} {B} f fEpic =
  ∣ (fst fKer ,
    (Kernel.ker (snd fKer)) , {!!}) ∣
--      transport (cong (isCoKernel (RMod {R = R}) (hasZeroObjectRMod R) (Kernel.ker (snd fKer))) incEqKer∘mapf=f)
--                (PostcompIsoPreserveCoKernel incEqKer ker catIsoEqKer (hasZeroObjectRMod R) incEqcoKer) ) ∣
    where
      _∘_ : {A B D : Precategory.ob (RModPreCat R)} → Precategory.hom (RModPreCat R) A B →
            Precategory.hom (RModPreCat R) B D → Precategory.hom (RModPreCat R) A D
      f ∘ g = Precategory.seq (RModPreCat R) f g
      0a : (A B : Precategory.ob (RModPreCat R))  → Precategory.hom (RModPreCat R) A B
      0a A B = ZeroArrow.f (getZeroArrow (RMod {R = R}) {A = A} {B = B} (hasZeroObjectRMod R))

      f' = ModuleHomomorphism.h f
      fKer = hasAllKernelsRModNonTrunk R f

      0A = Module.0m A
      _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
      a +A b = (A Module.+ a) b
      -A_ : ⟨ A ⟩M → ⟨ A ⟩M
      -A a = (Module.- A) a
      _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
      r ⋆A a = (A Module.⋆ r) a
      0B = Module.0m B
      _+B_ : ⟨ B ⟩M → ⟨ B ⟩M → ⟨ B ⟩M
      a +B b = (B Module.+ a) b
      -B_ : ⟨ B ⟩M → ⟨ B ⟩M
      -B a = (Module.- B) a
      _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
      r ⋆B a = (B Module.⋆ r) a

      _+K_ = Module._+_ (EquivKernelObj f)
      _⋆K_ = Module._⋆_ (EquivKernelObj f)

      ker = Kernel.ker (snd fKer)
      incEqKer : ModuleHomomorphism R A (EquivKernelObj f)
      incEqKer = moduleHomo [_]
                            (λ x y → eq/ _ _ (cong f' refl))
                             λ r x → eq/ _ _ (cong f' refl)
      mapf : ModuleHomomorphism R (EquivKernelObj f) B
      mapf = moduleHomo (rec (isSetModule B) f' (λ a b fa=fb → fa=fb))
                        (elim2 (λ a b → isProp→isSet (isSetModule B _ _)) (ModuleHomomorphism.linear f)
                          (λ a b c r → toPathP (isSetModule B _ _ _ _))
                          (λ a b c r → toPathP (isSetModule B _ _ _ _)))
                        λ r → elim (λ a → isProp→isSet (isSetModule B _ _)) (ModuleHomomorphism.scalar f r)
                           λ a b r → toPathP (isSetModule B _ _ _ _)
      mapf' = ModuleHomomorphism.h mapf
      
      incEqKer∘mapf=f : incEqKer ∘ mapf ≡ f
      incEqKer∘mapf=f = ModuleHomo≡ (funExt (λ a → refl))

      mapfEpic : isEpic (RMod {R = R}) mapf
      mapfEpic = PostCompIsEpicToEpic (RMod {R = R}) f fEpic mapf incEqKer incEqKer∘mapf=f

--      mapfMon : isMonic (RMod {R = R}) mapf
--      mapfMon E g h gmapf=hmapf = ModuleHomo≡ (funExt (λ x → {!!}))
--        elim2 {B = λ a b → a ≡ b} (λ a b → isProp→isSet (squash/ _ _)) {!!} {!!} {!!}
--          (ModuleHomomorphism.h g x) (ModuleHomomorphism.h h x)))

      elimTrunk : (b : ⟨ B ⟩M) → Σ ⟨ EquivKernelObj f ⟩M (λ [a] → b ≡ ModuleHomomorphism.h mapf [a])
      elimTrunk b = recHprop (λ ([a] , b=f[a]) ([c] , b=f[c]) → Σ≡ (HelpEq/ [a] [c] (λ (a' , [a']=[a]) (c' , [c']=[c]) →
                             eq/ a' c'
                               (f' a'     ≡⟨ cong mapf' [a']=[a] ⟩
                               mapf' [a]  ≡⟨ sym b=f[a] ⟩
                               b          ≡⟨ b=f[c] ⟩
                               mapf' [c] ≡⟨ cong mapf' (sym [c']=[c]) ⟩
                               f' c' ∎)))
                             (toPathP (isSetModule B _ _ _ _)))
                             (λ (a , b=fa) → [ a ] , b=fa)
                             (EpicAreSurj R f fEpic b)

      mapfInv' = λ b → fst (elimTrunk b)
      mapfInv'∘mapf'=id : (λ x → mapfInv' (mapf' x)) ≡ (λ x → x)
      mapfInv'∘mapf'=id = funExt (λ x → HelpEq/ (mapfInv' (mapf' x)) x
                           (λ (a , [a]=fInvfx) (c , [c]=x) → eq/ a c 
                             (f' a                      ≡⟨ refl ⟩
                             mapf' [ a ]                ≡⟨ cong mapf' [a]=fInvfx ⟩
                             mapf' (mapfInv' (mapf' x)) ≡⟨ sym (snd (elimTrunk (mapf' x))) ⟩
                             mapf' x                    ≡⟨ cong mapf' (sym [c]=x) ⟩
                             mapf' [ c ]                ≡⟨ refl ⟩
                             f' c ∎)))

      mapf'∘mapfInv'=id : (λ x → mapf' (mapfInv' x)) ≡ (λ x → x)
      mapf'∘mapfInv'=id = funExt (λ b → sym (snd (elimTrunk b)))

------This is the step that eats all the compilation time...
--      mapfInv : ModuleHomomorphism R B (EquivKernelObj f)
--      mapfInv = ModuleHomoInvIsHomo (EquivKernelObj f) B mapf mapfInv' mapf'∘mapfInv'=id mapfInv'∘mapf'=id

--      catIsoEqKer : CatIso (EquivKernelObj f) B
--      catIsoEqKer = catiso mapf mapfInv mapfInv'∘mapf'=id mapf'∘mapfInv'=id

      h'Help : (E : Module R) → (h : ModuleHomomorphism R A E) → ker ∘ h ≡ 0a (makeKernelObjRMod R f) E →
               Σ (ModuleHomomorphism R (EquivKernelObj f) E)
                 (λ h' → ModuleHomoComp incEqKer h' ≡ h)
      h'Help E h kerfh=0 =
        (moduleHomo (rec (isSetModule E) (ModuleHomomorphism.h h)
                     λ a b fa=fb → h' a                              ≡⟨ sym (ModuleZeroRight {M = E} (h' a)) ⟩
                                   ((h' a) +E 0E)     ≡⟨ cong (λ x → (h' a) +E x) (sym (ModuleInvLeft {M = E} (h' b))) ⟩
                                   ((h' a) +E ((-E (h' b)) +E h' b)) ≡⟨ cong (λ x → (h' a) +E (x +E h' b))
                                                                             (sym (ModuleHomomorphismLinSub b h)) ⟩
                                   ((h' a) +E (h' (-A b) +E h' b))   ≡⟨ Module+Isasso {M = E} (h' a) (h' (-A b)) (h' b) ⟩
                                   (((h' a) +E (h' (-A b))) +E h' b) ≡⟨ cong (λ x → x +E h' b)
                                                                             (sym (ModuleHomomorphism.linear h a (-A b))) ⟩
                                   (h' (a +A (-A b)) +E h' b)
                                        ≡⟨ cong (λ x → x +E h' b)
                                           (funExt⁻ (λ i → ModuleHomomorphism.h (kerfh=0 i)) ((a +A (-A b)) ,
                                             (f' (a +A (-A b))       ≡⟨ ModuleHomomorphism.linear f a (-A b) ⟩
                                             ((f' a) +B (f' (-A b))) ≡⟨ cong (λ x → (f' a) +B x) (ModuleHomomorphismLinSub b f) ⟩
                                             ((f' a) +B (-B (f' b))) ≡⟨ cong (λ x → x +B (-B (f' b))) fa=fb ⟩
                                             ((f' b) +B (-B (f' b))) ≡⟨ ModuleInvRight {M = B} (f' b) ⟩
                                             0B ∎))) ⟩
                                   (0E +E h' b)                      ≡⟨ ModuleZeroLeft {M = E} (h' b) ⟩
                                   h' b ∎)
                                      (elim2 (λ x y → isProp→isSet (isSetModule E _ _)) (ModuleHomomorphism.linear h)
                                        (λ a b c r → toPathP (isSetModule E _ _ _ _))
                                        (λ a b c r → toPathP (isSetModule E _ _ _ _)))
                                      λ r → elim (λ a → isProp→isSet (isSetModule E _ _)) (ModuleHomomorphism.scalar h r)
                                        (λ a b r → toPathP (isSetModule E _ _ _ _))) ,
                                      ModuleHomo≡ refl
        where
          h' = ModuleHomomorphism.h h
          0E = Module.0m E
          _+E_ : ⟨ E ⟩M → ⟨ E ⟩M → ⟨ E ⟩M
          x +E y = (E Module.+ x) y
          -E_ : ⟨ E ⟩M → ⟨ E ⟩M
          -E_ = (Module.- E)

      incEqcoKer : isCoKernel RMod (hasZeroObjectRMod R) (Kernel.ker (snd fKer)) incEqKer
      incEqcoKer = (coKernelConst incEqKer
                                  (ModuleHomo≡ (funExt (λ (a , fa=0) → eq/ a 0A
                                    (f' a ≡⟨ fa=0 ⟩
                                    0B    ≡⟨ sym (ModuleHomomorphismPreserveZero f) ⟩
                                    f' 0A ∎))))
                                  (λ {E} h Kerfh=0 → h'Help E h Kerfh=0)
                                  λ E g h incKerg=incKerh → ModuleHomo≡ (funExt (elimProp (λ x → isSetModule E _ _)
                                                              λ a i → ModuleHomomorphism.h (incKerg=incKerh i) a))) ,
                    refl
