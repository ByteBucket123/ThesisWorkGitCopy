{-# OPTIONS --cubical #-}

module ThesisWork.RModules.MonicToInjective where

--open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
open import Cubical.Data.Sigma.Base
--open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
--open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
--open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
--open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
--open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
--open import ThesisWork.BasicCategoryTheory.Limits.Kernel
--open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
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
--open import Agda.Builtin.Cubical.HCompU
open import Cubical.Core.Primitives renaming
  (_[_≡_] to _[_≡_]P)

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
--open import Cubical.HITs.PropositionalTruncation.Base
--open import ThesisWork.RModules.RModuleProperties
open import ThesisWork.SetQuotientHelp
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
--open import Cubical.HITs.PropositionalTruncation.Properties renaming
--  (elim to elimHprop ;
--   elim2 to elim2Hprop ;
--   elim3 to elim3Hprop ;
--   rec to recHprop ;
--   rec2 to rec2Hprop )

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
--open import Cubical.Relation.Binary.Base

--************************************************* Help *****************************************************

Σ2DepIso : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {C : A → B → Type ℓ''} →
           Iso (Σ A (λ a → Σ B (C a))) (Σ (Σ A (λ _ → B)) (λ (a , b) → C a b))
Σ2DepIso =
  iso (λ (a , (b , c)) → (a , b) , c)
      (λ ((a , b) , c) → (a , (b , c)))
      (λ z → refl)
      (λ z → refl)

Σ2DepHelp : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {C : A → B → Type ℓ''} →
            (Σ A (λ a → Σ B (C a))) ≡ (Σ (Σ A (λ _ → B)) (λ (a , b) → C a b))
Σ2DepHelp = ua (isoToEquiv Σ2DepIso)         

Σ2Dep : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {C : A → B → Type ℓ''} →
        {x y : Σ A (λ a → Σ B (C a))} →
        (p : fst x ≡ fst y) →
        (q : fst (snd x) ≡ fst (snd y)) →
        (λ i → C (p i) (q i)) [ snd (snd x) ≡ snd (snd y) ]P → 
        x ≡ y
Σ2Dep {x = x} {y = y} p q r = isoFunInjective Σ2DepIso x y (Σ≡ (Σ≡ p q) r)

Σ3DepIso : {ℓ ℓ1 ℓ2 ℓ3 ℓ4 : Level} → {A : Type ℓ} → {B : Type ℓ1} → {C : Type ℓ2} → {D : A → C → Type ℓ3} → {E : B → C → Type ℓ4} →
           Iso (Σ A (λ a → Σ B (λ b → Σ C (λ c → Σ (D a c) (λ _ → E b c)))))
               (Σ (Σ A (λ _ → Σ B (λ _ → C))) (λ (a , b , c) → Σ (D a c) (λ _ → E b c)))
Σ3DepIso =
  iso (λ (a , b , c , d , e) → (a , (b , c)) , (d , e))
      (λ ((a , b , c) , d , e) → a , (b , (c , (d , e))))
      (λ z → refl)
      λ z → refl

Σ3DepProp : {ℓ ℓ1 ℓ2 ℓ3 ℓ4 : Level} → {A : Type ℓ} → {B : Type ℓ1} → {C : Type ℓ2} → {D : A → C → Type ℓ3} → {E : B → C → Type ℓ4} →
           {x y : Σ A (λ a → Σ B (λ b → Σ C (λ c → Σ (D a c) (λ _ → E b c))))} →
           ((a : A) → (c : C) → isProp (D a c)) → ((b : B) → (c : C) → isProp (E b c)) →
           (p : fst x ≡ fst y) →
           (q : fst (snd x) ≡ fst (snd y)) →
           (r : fst (snd (snd x)) ≡ fst (snd (snd y))) →
           x ≡ y
Σ3DepProp {x = x} {y = y} propD propE p q r = isoFunInjective Σ3DepIso x y (Σ≡ (Σ≡ p (Σ≡ q r))
                                                (toPathP (Σ≡ (propD _ _ _ _) (propE _ _ _ _))))

--**************************************************** Proof **********************************************************

generetedMon : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A : Module R) →
               (a : ⟨ A ⟩M) → Module R
generetedMon R A a =
  moduleConst objGen
              0Gen
              _+Gen_
              -Gen_
              _⋆Gen_
              (isModule
                (ismodule
                  (isabgroup
                    (isgroup
                      (ismonoid
                        (issemigroup
                          (isSetΣ (isSetModule A) (λ g → isSetΣ (CommutativeRingIsSet R) (λ r → isProp→isSet (isSetModule A _ _))))
                          (λ (g , r , g=r⋆a) (g' , r' , g'=r'⋆a) (g'' , r'' , g''=r''⋆a) →
                            Σ2Dep (Module+Isasso {M = A} g g' g'') (Ring+Isasso R r r' r'') (toPathP (isSetModule A _ _ _ _))))
                        λ (g , r , g=r⋆a) → (Σ2Dep (ModuleZeroRight {M = A} g) (RingZeroRight R r) (toPathP
                          (isSetModule A _ _ _ _))) ,
                          Σ2Dep (ModuleZeroLeft {M = A} g) (RingZeroLeft R r) (toPathP (isSetModule A _ _ _ _)))
                      λ (g , r , g=r⋆a) → (Σ2Dep (ModuleInvRight {M = A} g) (RingInvRight R r) (toPathP (isSetModule A _ _ _ _))) ,
                        (Σ2Dep (ModuleInvLeft {M = A} g) (RingInvLeft R r) (toPathP (isSetModule A _ _ _ _))))
                    λ (g , r , g=r⋆a) (g' , r' , g'=r'⋆a) → Σ2Dep (ModuleIsAb {M = A} g g') (RingIsAb R r r')
                      (toPathP (isSetModule A _ _ _ _)))
                  (λ r s (g , t , g=t⋆a) → Σ2Dep (Module·Isasso {M = A} r s g) (sym (Ring·Isasso R r s t))
                    (toPathP (isSetModule A _ _ _ _)))
                  (λ r s (g , t , g=t⋆a) → Σ2Dep (ModuleLDist {M = A} r s g) (Ring·DistLeft R r s t)
                    (toPathP (isSetModule A _ _ _ _)))
                  (λ r (g , t , g=t⋆a) (g' , t' , g'=t'⋆a) → Σ2Dep (ModuleRDist {M = A} r g g') (Ring·DistRight R r t t')
                    (toPathP (isSetModule A _ _ _ _)))
                  λ (g , t , g=t⋆a) → Σ2Dep (ModuleLId {M = A} g) (Ring·OneLeft R t) (toPathP (isSetModule A _ _ _ _))))
  where
    0A = Module.0m A
    _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
    x +A y = (A Module.+ x) y
    -A_ : ⟨ A ⟩M → ⟨ A ⟩M
    -A x = (Module.- A) x
    _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
    a ⋆A b = (A Module.⋆ a) b

    0R = CommutativeRingStr.0r (snd R)
    _+R_ : ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
    x +R y = ((snd R) CommutativeRingStr.+ x) y
    -R_ : ⟨ R ⟩ → ⟨ R ⟩
    -R x = (CommutativeRingStr.- (snd R)) x
    _·R_ : ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
    x ·R y = ((snd R) CommutativeRingStr.· x) y

    objGen = Σ ⟨ A ⟩M (λ g → Σ ⟨ R ⟩ (λ r → g ≡ r ⋆A a))
    0Gen : objGen
    0Gen = 0A , 0R , (sym (ModuleMulZeroRing A a))
    _+Gen_ : objGen → objGen → objGen
    (g , r , g=r⋆a) +Gen (g' , r' , g'=r'⋆a) = (g +A g') , ((r +R r') ,
      ((g +A g')              ≡⟨ cong₂ (λ x y → x +A y) g=r⋆a g'=r'⋆a ⟩
      ((r ⋆A a) +A (r' ⋆A a)) ≡⟨ sym (ModuleLDist {M = A} r r' a) ⟩
      ((r +R r') ⋆A a) ∎))
    -Gen_ : objGen → objGen
    -Gen (g , r , g=r⋆a) = (-A g) , ((-R r) ,
      ((-A g)       ≡⟨ cong (λ x → -A x) g=r⋆a ⟩
      (-A (r ⋆A a)) ≡⟨ sym (ModuleSubMulRing A a r) ⟩
      ((-R r) ⋆A a) ∎))
    _⋆Gen_ : ⟨ R ⟩ → objGen → objGen
    s ⋆Gen (g , r , g=r⋆a) = (s ⋆A g) , ((s ·R r) ,
      ((s ⋆A g)       ≡⟨ cong (λ x → s ⋆A x) g=r⋆a ⟩
      (s ⋆A (r ⋆A a)) ≡⟨ sym (Module·Isasso {M = A} s r a) ⟩
      ((s ·R r) ⋆A a) ∎))

genModLinProd : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A : Module R) → (a a' : ⟨ A ⟩M) → Module R
genModLinProd R A a a' =
  moduleConst objGen
              0Gen
              _+Gen_
              -Gen_
              _⋆Gen_
              (isModule
                (ismodule
                  (isabgroup
                    (isgroup
                      (ismonoid
                        (issemigroup
                          (isSetΣ (isSetModule A) (λ g → isSetΣ (isSetModule A) λ g1 → isSetΣ (CommutativeRingIsSet R)
                            (λ r → isSetΣ (isProp→isSet (isSetModule A _ _)) (λ _ → isProp→isSet (isSetModule A _ _)))))
                          λ (g , g1 , r , _ , _) (g2 , g3 , r1 , _ , _) (g4 , g5 , r2 , _ , _) →
                            Σ3DepPropHelp (Module+Isasso {M = A} g g2 g4) (Module+Isasso {M = A} g1 g3 g5) (Ring+Isasso R r r1 r2))
                        λ (g , g1 , r , _ , _) →
                          (Σ3DepPropHelp (ModuleZeroRight {M = A} g) (ModuleZeroRight {M = A} g1) (RingZeroRight R r)) ,
                          Σ3DepPropHelp (ModuleZeroLeft {M = A} g) (ModuleZeroLeft {M = A} g1) (RingZeroLeft R r))
                      λ (g , g1 , r , _ , _) →
                        (Σ3DepPropHelp (ModuleInvRight {M = A} g) (ModuleInvRight {M = A} g1) (RingInvRight R r)) ,
                        (Σ3DepPropHelp (ModuleInvLeft {M = A} g) (ModuleInvLeft {M = A} g1) (RingInvLeft R r)))
                    λ (g , g1 , r , _ , _) (g2 , g3 , r' , _ , _) →
                      Σ3DepPropHelp (ModuleIsAb {M = A} g g2) (ModuleIsAb {M = A} g1 g3) (RingIsAb R r r'))
                  (λ r s (g , g1 , t , _ , _) →
                    Σ3DepPropHelp (Module·Isasso {M = A} r s g) (Module·Isasso {M = A} r s g1) (sym (Ring·Isasso R r s t)))
                  (λ r s (g , g1 , t , _ , _) →
                    Σ3DepPropHelp (ModuleLDist {M = A} r s g) (ModuleLDist {M = A} r s g1) (Ring·DistLeft R r s t))
                  (λ r (g , g1 , s , _ , _) (g2 , g3 , t , _ , _) →
                    Σ3DepPropHelp (ModuleRDist {M = A} r g g2) (ModuleRDist {M = A} r g1 g3) (Ring·DistRight R r s t))
                  λ (g , g1 , r , _ , _) → Σ3DepPropHelp (ModuleLId {M = A} g) (ModuleLId {M = A} g1) (Ring·OneLeft R r)))
  where
    0A = Module.0m A
    _+A_ : ⟨ A ⟩M → ⟨ A ⟩M → ⟨ A ⟩M
    x +A y = (A Module.+ x) y
    -A_ : ⟨ A ⟩M → ⟨ A ⟩M
    -A x = (Module.- A) x
    _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
    a ⋆A b = (A Module.⋆ a) b

    0R = CommutativeRingStr.0r (snd R)
    _+R_ : ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
    x +R y = ((snd R) CommutativeRingStr.+ x) y
    -R_ : ⟨ R ⟩ → ⟨ R ⟩
    -R x = (CommutativeRingStr.- (snd R)) x
    _·R_ : ⟨ R ⟩ → ⟨ R ⟩ → ⟨ R ⟩
    x ·R y = ((snd R) CommutativeRingStr.· x) y

    objGen = Σ ⟨ A ⟩M λ g → Σ ⟨ A ⟩M λ g' → Σ ⟨ R ⟩ (λ r → Σ (g ≡ r ⋆A a ) λ _ → g' ≡ r ⋆A a') 
    0Gen : objGen
    0Gen = 0A , 0A , 0R , (sym (ModuleMulZeroRing A a)) , (sym (ModuleMulZeroRing A a'))
    _+Gen_ : objGen → objGen → objGen
    (g , g1 , r , g=r⋆a , g1=r⋆a') +Gen (g2 , g3 , r' , g2=r'⋆a , g3=r'⋆a') = (g +A g2) , ((g1 +A g3) , (r +R r' ,
      ((g +A g2)              ≡⟨ cong₂ _+A_ g=r⋆a g2=r'⋆a ⟩
      ((r ⋆A a) +A (r' ⋆A a)) ≡⟨ sym (ModuleLDist {M = A} r r' a) ⟩
      ((r +R r') ⋆A a) ∎) ,
      ((g1 +A g3)               ≡⟨ cong₂ _+A_ g1=r⋆a' g3=r'⋆a' ⟩
      ((r ⋆A a') +A (r' ⋆A a')) ≡⟨ sym (ModuleLDist {M = A} r r' a') ⟩
      ((r +R r') ⋆A a') ∎)))
    -Gen_ : objGen → objGen
    -Gen (g , g1 , r , g=r⋆a , g1=r⋆a') = (-A g) , ((-A g1) , ((-R r) , (
      ((-A g)       ≡⟨ cong -A_ g=r⋆a ⟩
      (-A (r ⋆A a)) ≡⟨ sym (ModuleSubMulRing A a r) ⟩
      ((-R r) ⋆A a) ∎) ,
      ((-A g1)       ≡⟨ cong -A_ g1=r⋆a' ⟩
      (-A (r ⋆A a')) ≡⟨ sym (ModuleSubMulRing A a' r) ⟩
      ((-R r) ⋆A a') ∎))))
    _⋆Gen_ : ⟨ R ⟩ → objGen → objGen
    s ⋆Gen (g , g1 , r , g=r⋆a , g1=r⋆a') = (s ⋆A g) , ((s ⋆A g1) , ((s ·R r) , (
      ((s ⋆A g)       ≡⟨ cong (λ x → s ⋆A x) g=r⋆a ⟩
      (s ⋆A (r ⋆A a)) ≡⟨ sym (Module·Isasso {M = A} s r a) ⟩
      ((s ·R r) ⋆A a) ∎) ,
      ((s ⋆A g1)       ≡⟨ cong (λ x → s ⋆A x) g1=r⋆a' ⟩
      (s ⋆A (r ⋆A a')) ≡⟨ sym (Module·Isasso {M = A} s r a') ⟩
      ((s ·R r) ⋆A a') ∎))))

    Σ3DepPropHelp : {x y : objGen} →
                    (p : fst x ≡ fst y) →
                    (q : fst (snd x) ≡ fst (snd y)) →
                    (r : fst (snd (snd x)) ≡ fst (snd (snd y))) →
                    x ≡ y
    Σ3DepPropHelp = Σ3DepProp (λ a c → isSetModule A _ _) (λ b c → isSetModule A _ _)

MonicToInj : {ℓ : Level} → (R : CommutativeRing {ℓ}) → {A B : Precategory.ob (RModPreCat R)} →
             (f : Precategory.hom (RModPreCat R) A B) → (isMonic (RMod {R = R}) f) → (a a' : ⟨ A ⟩M) →
             ModuleHomomorphism.h f a ≡ ModuleHomomorphism.h f a' → a ≡ a'
MonicToInj R {A} {B} f monf a a' fa=fa' =
  funExt⁻ {f = g'} {g = h'} (λ i → ModuleHomomorphism.h (g=h i)) (a , (a' , (1R ,
    ((sym (ModuleLId {M = A} a)) , sym (ModuleLId {M = A} a')))))
    where
      f' = ModuleHomomorphism.h f
      1R = CommutativeRingStr.1r (snd R)
      _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
      a ⋆A b = (A Module.⋆ a) b
      _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
      a ⋆B b = (B Module.⋆ a) b

      g : ModuleHomomorphism R (genModLinProd R A a a') A
      g = moduleHomo fst (λ x y → refl) (λ r x → refl)
      g' = ModuleHomomorphism.h g
      h : ModuleHomomorphism R (genModLinProd R A a a') A
      h = moduleHomo (λ x → fst (snd x)) (λ x y → refl) (λ r x → refl)
      h' = ModuleHomomorphism.h h
      g=h : g ≡ h
      g=h = monf (genModLinProd R A a a') g h (ModuleHomo≡ (funExt (λ (g , g1 , r , g=r⋆a , g1=r⋆a') →
        f' g         ≡⟨ cong f' g=r⋆a ⟩
        f' (r ⋆A a)  ≡⟨ ModuleHomomorphism.scalar f r a ⟩
        (r ⋆B f' a)  ≡⟨ cong (λ x → r ⋆B x) fa=fa' ⟩
        (r ⋆B f' a') ≡⟨ sym (ModuleHomomorphism.scalar f r a') ⟩
        f' (r ⋆A a') ≡⟨ cong f' (sym g1=r⋆a') ⟩
        f' g1 ∎)))

--   funExt⁻ {f = g'} {g = h'} (λ i → ModuleHomomorphism.h (g=h i))
--     ((a , (1R , sym (ModuleLId {M = A} a))) , a' , (1R , (sym (ModuleLId {M = A} a'))))
--     where
--       f' = ModuleHomomorphism.h f
--       1R = CommutativeRingStr.1r (snd R)
--       _⋆A_ : ⟨ R ⟩ → ⟨ A ⟩M → ⟨ A ⟩M
--       a ⋆A b = (A Module.⋆ a) b
--       _⋆B_ : ⟨ R ⟩ → ⟨ B ⟩M → ⟨ B ⟩M
--       a ⋆B b = (B Module.⋆ a) b

--       aGen = generetedMon R A a
--       a'Gen = generetedMon R A a'
--       prodGen = productOfModules aGen a'Gen
--       fstHomoProd : ModuleHomomorphism R prodGen aGen
--       fstHomoProd = moduleHomo fst (λ x y → refl) λ r x → refl
--       sndHomoProd : ModuleHomomorphism R prodGen a'Gen
--       sndHomoProd = moduleHomo snd (λ x y → refl) λ r x → refl
--       fstHomoa : ModuleHomomorphism R aGen A
--       fstHomoa = moduleHomo fst (λ x y → refl) λ r x → refl
--       fstHomoa' : ModuleHomomorphism R a'Gen A
--       fstHomoa' = moduleHomo fst (λ x y → refl) λ r x → refl
--       g : ModuleHomomorphism R prodGen A
--       g = ModuleHomoComp fstHomoProd fstHomoa
--       g' = ModuleHomomorphism.h g
--       h : ModuleHomomorphism R prodGen A
--       h = ModuleHomoComp sndHomoProd fstHomoa'
--       h' = ModuleHomomorphism.h h

--       g=h : g ≡ h
--       g=h = monf prodGen g h (ModuleHomo≡ (funExt (λ ((g , r , g=r⋆Aa) , (g' , r' , g'=r'⋆Aa)) →
--         f' g         ≡⟨ cong f' g=r⋆Aa ⟩
--         f' (r ⋆A a)  ≡⟨ ModuleHomomorphism.scalar f r a ⟩
--         (r ⋆B f' a)  ≡⟨ cong (λ x → r ⋆B x) fa=fa' ⟩
--         (r ⋆B f' a') ≡⟨ sym (ModuleHomomorphism.scalar f r a') ⟩
--         f' (r ⋆A a') ≡⟨ cong f' (sym {!g'=r'⋆Aa!}) ⟩
--         f' g' ∎)))


-- -- MonicToInjective : {ℓ : Level} → {R : CommutativeRing {ℓ}} → {M N : Module R} → (f : ModuleHomomorphism R M N) →
-- --                    isMonic RMod f → {a b : ⟨ M ⟩M} → ModuleHomomorphism.h f a ≡ ModuleHomomorphism.h f b → a ≡ b
-- -- MonicToInjective {ℓ} {R} {M} {N} f fMon {a} {b} fa=fb = {!!}
-- --   where
-- --     f' = ModuleHomomorphism.h f
-- --     0M = Module.0m M
-- --     _+M_ : ⟨ M ⟩M → ⟨ M ⟩M → ⟨ M ⟩M
-- --     a +M b = (M Module.+ a) b
-- --     _+N_ : ⟨ N ⟩M → ⟨ N ⟩M → ⟨ N ⟩M
-- --     a +N b = (N Module.+ a) b
-- --     -M_ : ⟨ M ⟩M → ⟨ M ⟩M
-- --     -M a = (Module.- M) a
-- --     -N_ : ⟨ N ⟩M → ⟨ N ⟩M
-- --     -N a = (Module.- N) a
-- --     _⋆M_ : ⟨ R ⟩ → ⟨ M ⟩M → ⟨ M ⟩M
-- --     r ⋆M a = (M Module.⋆ r) a
-- --     _⋆N_ : ⟨ R ⟩ → ⟨ N ⟩M → ⟨ N ⟩M
-- --     r ⋆N a = (N Module.⋆ r) a
-- --     FeqMonoid : Module R
-- --     FeqMonoid = moduleConst (⟨ M ⟩M / λ m m' → f' m ≡ f' m')
-- --                             [ 0M ]
-- --                             (elim2 (λ x y → squash/) (λ a b → [ a +M b ]) (λ a b c f'a=f'b → eq/ (a +M c) (b +M c)
-- --                               (f' (a +M c)       ≡⟨ ModuleHomomorphism.linear f a c ⟩
-- --                               ((f' a) +N (f' c)) ≡⟨ cong (λ x → x +N (f' c)) f'a=f'b ⟩
-- --                               ((f' b) +N (f' c)) ≡⟨ sym (ModuleHomomorphism.linear f b c) ⟩
-- --                               f' (b +M c) ∎))
-- --                               λ a b c f'b=f'c → eq/ (a +M b) (a +M c)
-- --                                 (f' (a +M b)       ≡⟨ ModuleHomomorphism.linear f a b ⟩
-- --                                 ((f' a) +N (f' b)) ≡⟨ cong (λ x → (f' a) +N x) f'b=f'c ⟩
-- --                                 ((f' a) +N (f' c)) ≡⟨ sym (ModuleHomomorphism.linear f a c) ⟩
-- --                                 f' (a +M c) ∎))
-- --                             (elim (λ x → squash/) (λ a → [ -M a ]) λ a b f'a=f'b → eq/ (-M a) (-M b)
-- --                               (f' (-M a)  ≡⟨ ModuleHomomorphismLinSub a f ⟩
-- --                               (-N (f' a)) ≡⟨ cong (λ x → -N x ) f'a=f'b ⟩
-- --                               (-N (f' b)) ≡⟨ sym (ModuleHomomorphismLinSub b f) ⟩
-- --                               f' (-M b) ∎))
-- --                             (λ r → elim (λ x → squash/) (λ a → [ r ⋆M a ]) λ a b f'a=f'b → eq/ (r ⋆M a) (r ⋆M b)
-- --                               (f' (r ⋆M a)  ≡⟨ ModuleHomomorphism.scalar f r a ⟩
-- --                               (r ⋆N (f' a)) ≡⟨ cong (λ x → r ⋆N x) f'a=f'b ⟩
-- --                               (r ⋆N (f' b)) ≡⟨ sym (ModuleHomomorphism.scalar f r b) ⟩
-- --                               f' (r ⋆M b) ∎))
-- --                             (isModule
-- --                               (ismodule
-- --                                 (isabgroup
-- --                                   (isgroup
-- --                                     (ismonoid
-- --                                       (issemigroup
-- --                                         squash/
-- --                                         {!!})
-- --                                       {!!})
-- --                                     {!!})
-- --                                   {!!})
-- --                                 {!!}
-- --                                 {!!}
-- --                                 {!!}
-- --                                 {!!}))
