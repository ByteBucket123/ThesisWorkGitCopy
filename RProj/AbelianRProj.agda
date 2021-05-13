{-# OPTIONS --cubical #-}

module ThesisWork.RProj.AbelianRProj where

open import Cubical.Foundations.Prelude
open import ThesisWork.HelpFunctions
--open import Cubical.Data.Sigma.Base
open import ThesisWork.BasicCategoryTheory.Limits.InitialObject
--open import ThesisWork.BasicCategoryTheory.Limits.TerminalObject
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
--open import ThesisWork.BasicCategoryTheory.Limits.BinaryCoProduct
--open import ThesisWork.BasicCategoryTheory.Limits.Kernel
--open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import ThesisWork.RModules.CommutativeRing
--open import Cubical.Algebra.Ring.Base
--open import Cubical.Algebra.Semigroup.Base
--open import Cubical.Algebra.Monoid.Base
--open import Cubical.Algebra.Group.Base
--open import Cubical.Algebra.AbGroup.Base
--open import Cubical.Algebra.Module.Base
open import ThesisWork.RModules.RModuleHomomorphism
open import ThesisWork.RModules.RModuleHomomorphismProperties
open import ThesisWork.RModules.RModule
open import ThesisWork.RModules.RMod
open import Cubical.Foundations.Structure
open import ThesisWork.CompatibilityCode
--open import ThesisWork.SetSigmaType
--open import Agda.Builtin.Cubical.HCompU
--open import Cubical.Core.Primitives renaming
--  (_[_≡_] to _[_≡_]P)

--open import Cubical.HITs.SetQuotients.Base
--open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.PropositionalTruncation.Base
--open import ThesisWork.RModules.RModuleProperties
--open import ThesisWork.SetQuotientHelp
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
--open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import Cubical.HITs.PropositionalTruncation.Properties renaming
  (elim to elimHprop ;
   elim2 to elim2Hprop ;
   elim3 to elim3Hprop ;
   rec to recHprop ;
   rec2 to rec2Hprop )

open import Cubical.Foundations.Isomorphism
--open import Cubical.Foundations.Univalence
--open import Cubical.Relation.Binary.Base
--open import ThesisWork.RModules.MonicToInjective
open import ThesisWork.RModules.RModProperties
open import ThesisWork.AbelianCategory.Abelian
open import ThesisWork.RProj.RProj
open import ThesisWork.RProj.ProjModule
open import ThesisWork.RProj.Projective
open import ThesisWork.RProj.FinitelyGeneratedModule
open import Cubical.Data.Nat.Base
open import Cubical.Data.Vec.Base
open import ThesisWork.RProj.ProjModuleHomo
open import Cubical.Foundations.Equiv

private
  ob = Precategory.ob
  cat = UnivalentCategory.cat
  hom = Precategory.hom
  id = Precategory.idn
  idl = Precategory.seq-λ
  idr = Precategory.seq-ρ
  catAsso = Precategory.seq-α
  _,_∘_ = Precategory.seq
  _∘_ = ModuleHomoComp
  _<_×_> = BinaryProduct.<_×_>

HomSets≡ : {ℓ : Level} → {R : CommutativeRing {ℓ}} → (M N : ProjModule R) →
           Precategory.hom (UnivalentCategory.cat (RProj R)) M N ≡
           Precategory.hom (UnivalentCategory.cat (RMod {R = R})) (ProjModule→Module M) (ProjModule→Module N)
HomSets≡ {R = R} M N = ProjModHom≡ModHom

RProjHasZero : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasZeroObject (RProj R)
RProjHasZero R = ZeroProjModule ,CatWithZero
                   ((λ B → transport (cong isContr (sym (HomSets≡ ZeroProjModule B)))
                                     (zeroModuleisInitialObject R (ProjModule→Module B))) ,Zero
                   λ B → transport (cong isContr (sym (HomSets≡ B ZeroProjModule)))
                                   (zeroModuleisTerminalObject R (ProjModule→Module B)))
  where
    _⋆Z_ = Module._⋆_ (zeroModule R)
    0Z = Module.0m (zeroModule R)

    isProjectiveZero : isProjectiveModule R (zeroModule R)
    isProjectiveZero {E} {X} f e eSurj =
      ∣ (f* , ModuleHomo≡ (funExt (λ * → e' (f*' *)  ≡⟨ cong (λ x → e' (f*' x)) (isPropOneElem * 0Z) ⟩
                                         e' (f*' 0Z) ≡⟨ cong e' (ModuleHomomorphismPreserveZero f*) ⟩
                                         e' 0E       ≡⟨ ModuleHomomorphismPreserveZero e ⟩
                                         0X          ≡⟨ sym (ModuleHomomorphismPreserveZero f) ⟩
                                         f' 0Z       ≡⟨ cong f' (isPropOneElem 0Z *) ⟩
                                         f' *  ∎))) ∣
      where
        0E = Module.0m E
        0X = Module.0m X
        f' = ModuleHomomorphism.h f
        e' = ModuleHomomorphism.h e
        f* = fst (zeroModuleisInitialObject R E)
        f*' = ModuleHomomorphism.h f*

    isFinGenZero : isFinitelyGenerated (zeroModule R)
    isFinGenZero = ∣ (zero , ([] , (λ g → [] , (isPropOneElem 0Z g)))) ∣

    ZeroProjModule = Module→ProjModule (zeroModule R) isProjectiveZero isFinGenZero

isProjectiveProd : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A B : ProjModule R) →
                   isProjectiveModule R (productOfModules (ProjModule→Module A) (ProjModule→Module B))
isProjectiveProd R A B {E} {X} f e esurj =
  recHprop propTruncIsProp
           (λ f'A →
             recHprop propTruncIsProp
                      (λ f'B →
                        ∣ ((coProdHomo (fst f'A) (fst f'B)) , ModuleHomo≡ (funExt (λ x → coProdHom∘ex=fx f'A f'B x ))) ∣)
                      (getIsProj B BProj e esurj))
           (getIsProj A AProj e esurj)
  where
    prodModule = productOfModules (ProjModule→Module A) (ProjModule→Module B)
    fstHom = fstHomo (ProjModule→Module A) (ProjModule→Module B)

    pACoProdAB = pACoProd R (ProjModule→Module A) (ProjModule→Module B)
    pBCoProdAB = pBCoProd R (ProjModule→Module A) (ProjModule→Module B)
    
    AProj : ModuleHomomorphism R (ProjModule→Module A) X
    AProj = pACoProdAB ∘ f
    BProj : ModuleHomomorphism R (ProjModule→Module B) X
    BProj = pBCoProdAB ∘ f

    coProdHom∘ex=fx : (f'A : Σ (ModuleHomomorphism R (ProjModule→Module A) E) (λ v → ModuleHomoComp v e ≡ AProj)) →
                      (f'B : Σ (ModuleHomomorphism R (ProjModule→Module B) E) (λ v → ModuleHomoComp v e ≡ BProj)) →
                      (x :  ⟨ prodModule ⟩M) → 
                      ModuleHomomorphism.h e (ModuleHomomorphism.h (coProdHomo (fst f'A) (fst f'B)) x) ≡ ModuleHomomorphism.h f x
    coProdHom∘ex=fx f'A f'B (a , b) =
      e' (coProdHom' (a , b))                      ≡⟨ refl ⟩
      e' (f'A' a +E f'B' b)                        ≡⟨ ModuleHomomorphism.linear e (f'A' a) (f'B' b) ⟩
      ((e' (f'A' a)) +X (e' (f'B' b)))             ≡⟨ cong₂ _+X_ (λ i → ModuleHomomorphism.h (snd f'A i) a)
                                                                 (λ i → ModuleHomomorphism.h (snd f'B i) b) ⟩
      ((f' (pACoProdAB' a)) +X f' (pBCoProdAB' b)) ≡⟨ refl ⟩
      ((f' ((a , 0B))) +X f' (0A , b))             ≡⟨ sym (ModuleHomomorphism.linear f (a , 0B) (0A , b)) ⟩
      f' (((a , 0B)) +Prod ((0A , b)))             ≡⟨ refl ⟩
      f' ((a +A 0A) , (0B +B b))                   ≡⟨ cong₂ (λ x y → f' (x , y)) (ModuleZeroRight {M = ProjModule→Module A} a)
                                                                                 (ModuleZeroLeft {M = ProjModule→Module B} b) ⟩
      f' (a , b) ∎
        where
          0A = Module.0m (ProjModule→Module A)
          0B = Module.0m (ProjModule→Module B)
          f' = ModuleHomomorphism.h f
          e' = ModuleHomomorphism.h e
          f'A' = ModuleHomomorphism.h (fst f'A)
          f'B' = ModuleHomomorphism.h (fst f'B)
          pACoProdAB' = ModuleHomomorphism.h pACoProdAB
          pBCoProdAB' = ModuleHomomorphism.h pBCoProdAB
          coProdHom' = ModuleHomomorphism.h (coProdHomo (fst f'A) (fst f'B))
          _+A_ = Module._+_ (ProjModule→Module A)
          _+B_ = Module._+_ (ProjModule→Module B)
          _+E_ = Module._+_ E
          _+X_ = Module._+_ X
          _+Prod_ = Module._+_ prodModule

moduleVecEq : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A : Module R) →
              {n m : ℕ} → (vecA : Vec ⟨ A ⟩M n) → (vecB : Vec ⟨ A ⟩M m) → (rA : Vec ⟨ R ⟩ n) → (rB : Vec ⟨ R ⟩ m) →
              sumGenerators R A (vecA ++ vecB) (rA ++ rB) ≡ (A Module.+ (sumGenerators R A vecA rA)) (sumGenerators R A vecB rB)
moduleVecEq R A [] vecB [] rB = sym (ModuleZeroLeft {M = A} (sumGenerators R A vecB rB))
moduleVecEq R A (a ∷ vecA) vecB (r ∷ rA) rB =
  sumGenerators R A ((a ∷ vecA) ++ vecB) ((r ∷ rA) ++ rB)                     ≡⟨ cong (λ x → (r ⋆A a) +A x)
                                                                                      (moduleVecEq R A vecA vecB rA rB) ⟩
  (r ⋆A a) +A ((sumGenerators R A vecA rA) +A (sumGenerators R A vecB rB))    ≡⟨ Module+Isasso {M = A} (r ⋆A a)
                                                                                               (sumGenerators R A vecA rA)
                                                                                               (sumGenerators R A vecB rB) ⟩
  ((sumGenerators R A (a ∷ vecA) (r ∷ rA)) +A (sumGenerators R A vecB rB)) ∎
  where
    _+A_ = Module._+_ A
    _⋆A_ = Module._⋆_ A

isFinGenProd : {ℓ : Level} → (R : CommutativeRing {ℓ}) → (A B : ProjModule R) →
               isFinitelyGenerated (productOfModules (ProjModule→Module A) (ProjModule→Module B))
isFinGenProd R A B =
  recHprop propTruncIsProp
    (λ genA →
      recHprop propTruncIsProp
        (λ genB →
          finGenProd genA genB)
        (getIsFinGen B))
    (getIsFinGen A)
  where
    0A = Module.0m (ProjModule→Module A)
    0B = Module.0m (ProjModule→Module B)
    modA = ProjModule→Module A
    modB = ProjModule→Module B
    _+A_ = Module._+_ modA
    -A_ = Module.-_ modA
    _⋆A_ = Module._⋆_ modA
    _+B_ = Module._+_ modB
    _⋆B_ = Module._⋆_ modB
    -B_ = Module.-_ modB
    prodModule = productOfModules modA modB
    _+Prod_ = Module._+_ prodModule
    _⋆Prod_ = Module._⋆_ prodModule

    makeProdVecA : {n : ℕ} → Vec ⟨ modA ⟩M n → Vec ⟨ prodModule ⟩M n
    makeProdVecA [] = []
    makeProdVecA (a ∷ vecA) = (a , 0B) ∷ makeProdVecA vecA

    makeProdVecB : {m : ℕ} → Vec ⟨ modB ⟩M m → Vec ⟨ prodModule ⟩M m
    makeProdVecB [] = []
    makeProdVecB (b ∷ vecB) = (0A , b) ∷ makeProdVecB vecB

    combVectors : {n m : ℕ} → Vec ⟨ modA ⟩M n → Vec ⟨ modB ⟩M m → Vec ⟨ prodModule ⟩M (n + m)
    combVectors vecA vecB = makeProdVecA vecA ++ makeProdVecB vecB

    combGenScalars : {n m : ℕ} → (vecA : Vec ⟨ modA ⟩M n) → (vecB : Vec ⟨ modB ⟩M m) →
                     (g : ⟨ prodModule ⟩M) →
                     ((g' : ⟨ modA ⟩M) → Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R modA vecA r ≡ g') → 
                     ((g' : ⟨ modB ⟩M) → Σ (Vec ⟨ R ⟩ m) λ r → sumGenerators R modB vecB r ≡ g') → 
                     Vec ⟨ R ⟩ (n + m)
    combGenScalars vecA vecB (a , b) genFunA genFunB = fst (genFunA a) ++ fst (genFunB b)

    rVecA : {n : ℕ} → (vecA : Vec ⟨ modA ⟩M n) → (g : ⟨ prodModule ⟩M) →
            (genFunA : (g' : ⟨ modA ⟩M) → Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R modA vecA r ≡ g') →
            Vec ⟨ R ⟩ n
    rVecA vecA (a , b) genFunA = fst (genFunA a)

    rVecB : {n : ℕ} → (vecB : Vec ⟨ modB ⟩M n) → (g : ⟨ prodModule ⟩M) →
            (genFunB : (g' : ⟨ modB ⟩M) → Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R modB vecB r ≡ g') →
            Vec ⟨ R ⟩ n
    rVecB vecB (a , b) genFunB = fst (genFunB b)

    AddVectorsEqHelp : {n m : ℕ} → (vecA : Vec ⟨ modA ⟩M n) → (vecB : Vec ⟨ modB ⟩M m) →
                       (g : ⟨ prodModule ⟩M) →
                       (genFunA : (g' : ⟨ modA ⟩M) → Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R modA vecA r ≡ g') → 
                       (genFunB : (g' : ⟨ modB ⟩M) → Σ (Vec ⟨ R ⟩ m) λ r → sumGenerators R modB vecB r ≡ g') →
                       sumGenerators R prodModule (combVectors vecA vecB) (combGenScalars vecA vecB g genFunA genFunB) ≡
                       ((sumGenerators R prodModule (makeProdVecA vecA) (fst (genFunA (fst g)))) +Prod
                       (sumGenerators R prodModule (makeProdVecB vecB) (fst (genFunB (snd g)))))
    AddVectorsEqHelp vecA vecB g genFunA genFunB = moduleVecEq R prodModule (makeProdVecA vecA)
                                                                            (makeProdVecB vecB)
                                                                            (rVecA vecA g genFunA)
                                                                            (rVecB vecB g genFunB)

    AddVectorsEqHelpA2 : {n : ℕ} → (vecA : Vec ⟨ modA ⟩M n) → (g : ⟨ prodModule ⟩M) →
                        (rVec : Vec ⟨ R ⟩ n) → sumGenerators R modA vecA rVec ≡ fst g →
                        sumGenerators R prodModule (makeProdVecA vecA) rVec ≡
                        ((sumGenerators R modA vecA rVec) , 0B)
    AddVectorsEqHelpA2 [] g [] sumGen=a = refl
    AddVectorsEqHelpA2 (a₁ ∷ vecA) (a , b) (r ∷ rVec) sumGen=a =
      ((r ⋆Prod (a₁ , 0B)) +Prod sumGenProd)
                               ≡⟨ cong (λ x → x +Prod sumGenProd) (Σ≡ refl (ModuleMulPresZero {M = modB} r)) ⟩
      (((r ⋆A a₁) , 0B) +Prod sumGenProd) ≡⟨ cong (λ x → ((r ⋆A a₁) , 0B) +Prod x)
                                            (AddVectorsEqHelpA2 vecA ((-A (r ⋆A a₁)) +A a , b) rVec (
                                              sumGen ≡⟨ sym (ModuleZeroLeft {M = modA} sumGen) ⟩
                                              (0A +A sumGen) ≡⟨ cong (λ x → x +A sumGen)
                                                                     (sym (ModuleInvLeft {M = modA} (r ⋆A a₁))) ⟩
                                              (((-A (r ⋆A a₁)) +A (r ⋆A a₁)) +A sumGen) ≡⟨ sym (Module+Isasso {M = modA}
                                                                                                              (-A (r ⋆A a₁))
                                                                                                              (r ⋆A a₁) sumGen) ⟩
                                              ((-A (r ⋆A a₁)) +A ((r ⋆A a₁) +A sumGen)) ≡⟨ cong (λ x → (-A (r ⋆A a₁)) +A x)
                                                                                                sumGen=a ⟩
                                              ((-A (r ⋆A a₁)) +A a) ∎)) ⟩
      (((r ⋆A a₁) , 0B) +Prod (sumGen , 0B))             ≡⟨ Σ≡ refl (ModuleZeroRight {M = modB} 0B) ⟩
      ((sumGenerators R modA (a₁ ∷ vecA) (r ∷ rVec)) , 0B) ∎
        where
          sumGen = sumGenerators R modA vecA rVec
          sumGenProd = sumGenerators R prodModule (makeProdVecA vecA) rVec


    AddVectorsEqHelpA : {n : ℕ} → (vecA : Vec ⟨ modA ⟩M n) → (g : ⟨ prodModule ⟩M) →
                        (genFunA : (g' : ⟨ modA ⟩M) → Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R modA vecA r ≡ g') →
                        sumGenerators R prodModule (makeProdVecA vecA) (fst (genFunA (fst g))) ≡ (fst g , 0B)
    AddVectorsEqHelpA vecA (a , b) genFunA =
      sumGenerators R prodModule (makeProdVecA vecA) (fst (genFunA a)) ≡⟨ AddVectorsEqHelpA2 vecA ((a , b))
                                                                            (fst (genFunA a)) (snd (genFunA a)) ⟩
      ((sumGenerators R modA vecA (fst (genFunA a))) , 0B)             ≡⟨ Σ≡ (snd (genFunA a)) refl ⟩
      (a , 0B) ∎

    AddVectorsEqHelpB2 : {m : ℕ} → (vecB : Vec ⟨ modB ⟩M m) → (g : ⟨ prodModule ⟩M) →
                         (rVec : Vec ⟨ R ⟩ m) → sumGenerators R modB vecB rVec ≡ snd g →
                         sumGenerators R prodModule (makeProdVecB vecB) rVec ≡
                         (0A , (sumGenerators R modB vecB rVec))
    AddVectorsEqHelpB2 [] g [] sumGen=b = refl
    AddVectorsEqHelpB2 (b₁ ∷ vecB) (a , b) (r ∷ rVec) sumGen=b =
      sumGenerators R prodModule (makeProdVecB (b₁ ∷ vecB)) (r ∷ rVec) ≡⟨ refl ⟩
      ((r ⋆Prod (0A , b₁)) +Prod sumGenProd) ≡⟨ cong (λ x → x +Prod sumGenProd) (Σ≡ (ModuleMulPresZero {M = modA} r) refl) ⟩
      ((0A , (r ⋆B b₁)) +Prod sumGenProd)    ≡⟨ cong (λ x → (0A , (r ⋆B b₁)) +Prod x)
                                                     (AddVectorsEqHelpB2 vecB (a , ((-B (r ⋆B b₁)) +B b)) rVec
                                                       (sumGen        ≡⟨ sym (ModuleZeroLeft {M = modB} sumGen) ⟩
                                                       (0B +B sumGen) ≡⟨ cong (λ x → x +B sumGen)
                                                                              (sym (ModuleInvLeft {M = modB} (r ⋆B b₁))) ⟩
                                                       (((-B (r ⋆B b₁)) +B (r ⋆B b₁)) +B sumGen)
                                                                                 ≡⟨ sym (Module+Isasso {M = modB} (-B (r ⋆B b₁))
                                                                                                       (r ⋆B b₁) sumGen) ⟩
                                                       ((-B (r ⋆B b₁)) +B ((r ⋆B b₁) +B sumGen))
                                                                                 ≡⟨ cong (λ x → (-B (r ⋆B b₁)) +B x) sumGen=b ⟩
                                                       ((-B (r ⋆B b₁)) +B b) ∎)) ⟩
      ((0A , (r ⋆B b₁)) +Prod (0A , sumGen)) ≡⟨ Σ≡ (ModuleZeroRight {M = modA} 0A) refl ⟩
      (0A , sumGenerators R modB (b₁ ∷ vecB) (r ∷ rVec)) ∎
        where
          sumGen = sumGenerators R modB vecB rVec
          sumGenProd = sumGenerators R prodModule (makeProdVecB vecB) rVec

    AddVectorsEqHelpB : {m : ℕ} → (vecB : Vec ⟨ modB ⟩M m) → (g : ⟨ prodModule ⟩M) →
                        (genFunB : (g' : ⟨ modB ⟩M) → Σ (Vec ⟨ R ⟩ m) λ r → sumGenerators R modB vecB r ≡ g') →
                        sumGenerators R prodModule (makeProdVecB vecB) (fst (genFunB (snd g))) ≡ (0A , snd g)
    AddVectorsEqHelpB vecB (a , b) genFunB =
      sumGenerators R prodModule (makeProdVecB vecB) (fst (genFunB b)) ≡⟨ AddVectorsEqHelpB2 vecB (a , b) (fst (genFunB b))
                                                                                                          (snd (genFunB b)) ⟩
      (0A , sumGenerators R modB vecB (fst (genFunB b)))               ≡⟨ Σ≡ refl (snd (genFunB b)) ⟩
      (0A , b) ∎

    AddVectorsEq : {n m : ℕ} → (vecA : Vec ⟨ modA ⟩M n) → (vecB : Vec ⟨ modB ⟩M m) →
                   (g : ⟨ prodModule ⟩M) →
                   (genFunA : (g' : ⟨ modA ⟩M) → Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R modA vecA r ≡ g') → 
                   (genFunB : (g' : ⟨ modB ⟩M) → Σ (Vec ⟨ R ⟩ m) λ r → sumGenerators R modB vecB r ≡ g') →
                   sumGenerators R prodModule (combVectors vecA vecB) (combGenScalars vecA vecB g genFunA genFunB)
                   ≡ g
    AddVectorsEq vecA vecB (a , b) genFunA genFunB =
      sumGenerators R prodModule (combVectors vecA vecB) (combGenScalars vecA vecB (a , b) genFunA genFunB)
                                        ≡⟨ AddVectorsEqHelp vecA vecB (a , b) genFunA genFunB ⟩
      (((sumGenerators R prodModule (makeProdVecA vecA) (fst (genFunA a))) +Prod
        (sumGenerators R prodModule (makeProdVecB vecB) (fst (genFunB b)))))
                                                                       ≡⟨ cong₂ _+Prod_ (AddVectorsEqHelpA vecA (a , b) genFunA)
                                                                                        (AddVectorsEqHelpB vecB (a , b) genFunB) ⟩
        ((a , 0B) +Prod (0A , b))  ≡⟨ Σ≡ (ModuleZeroRight {M = modA} a) (ModuleZeroLeft {M = modB} b) ⟩
      (a , b) ∎

    finGenProd : (genA : finiteGenerator modA) → (genB : finiteGenerator modB) →
                 isFinitelyGenerated prodModule
    finGenProd (n , vecA , genFunA) (m , vecB , genFunB) =
      ∣ ((n + m) ,
        (combVectors vecA vecB , λ g → (combGenScalars vecA vecB g genFunA genFunB) , AddVectorsEq vecA vecB g genFunA genFunB)) ∣

--Σ ℕ λ n →
--Σ (Vec ⟨ M ⟩M n) (λ V → (g : ⟨ M ⟩M) →
--Σ (Vec ⟨ R ⟩ n) λ r → sumGenerators R M V r ≡ g)    

hasAllBinaryProductsRProj : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasAllBinaryProducts (RProj R)
hasAllBinaryProductsRProj R A B = ∣ ({!!} , {!!}) ∣
  where
    prodModule = productOfModules (ProjModule→Module A) (ProjModule→Module B)

    ProdProj = Module→ProjModule prodModule {!!} {!!}

-- RProjHasZero : {ℓ : Level} → (R : CommutativeRing {ℓ}) → hasZeroObject (RProj R)
-- RProjHasZero R = (Module→ProjModule (zeroModule R) isProjectiveZero isFinGenZero) ,CatWithZero
--                    ((λ B → (projModuleHomo (λ * → ProjModule.0m B) (λ * * → sym (ModuleZeroRight {M = ProjModule→Module B}
--                    (ProjModule.0m B))) λ r * → sym (ModuleMulPresZero {M = ProjModule→Module B} r)) ,
--                    λ hom → ProjModuleHomo≡ (funExt (λ * → sym (
--                      ProjectiveModuleHomomorphism.h hom * ≡⟨ cong (ProjectiveModuleHomomorphism.h hom)
--                                                                   (isPropOneElem * (Module.0m (zeroModule R))) ⟩
--                      ProjectiveModuleHomomorphism.h hom (Module.0m (zeroModule R)) ≡⟨ ModuleHomomorphismPreserveZero
--                                                                                         (ProjModHom→ModHom hom) ⟩
--                      ProjModule.0m B ∎)))) ,Zero {!!})
--   where
--     _⋆Z_ = Module._⋆_ (zeroModule R)

--     isProjectiveZero : isProjectiveModule R (zeroModule R)
--     isProjectiveZero {E} f e eSurj = zeroModuleisInitialObject R E
--     isFinGenZero : isFinitelyGenerated (zeroModule R)
--     isFinGenZero = ∣ (suc zero , * ∷ [] , λ * → ((CommutativeRingStr.1r (snd R)) ∷ []) ,
--                        (sumGenerators R (zeroModule R) (* ∷ []) ((CommutativeRingStr.1r (snd R)) ∷ []) ≡⟨ refl ⟩
--                        ((CommutativeRingStr.1r (snd R)) ⋆Z *) ≡⟨ ModuleLId {M = zeroModule R} * ⟩
--                        * ∎)) ∣
