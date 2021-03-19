{-- 
  This is a proof translated from Unimath. Here is the original proof: 
  https://github.com/UniMath/UniMath/blob/master/UniMath/CategoryTheory/AbelianToAdditive.v 
--}

{-# OPTIONS --cubical #-}

module ThesisWork.AbelianCategory.AbelianToAdditive where

open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.HelpFunctions
open import Cubical.HITs.PropositionalTruncation
open import ThesisWork.CompatibilityCode
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import ThesisWork.BasicCategoryTheory.Limits.BinaryProduct
open import ThesisWork.BasicCategoryTheory.Limits.Kernel
open import ThesisWork.BasicCategoryTheory.Limits.CoKernel
open import Cubical.Data.Sigma.Base
open import ThesisWork.AbelianCategory.Abelian
open import ThesisWork.BasicCategoryTheory.ElementaryArrowProperties
open import ThesisWork.AbelianCategory.AdditiveCategory

private
  ob = Precategory.ob
  cat = UnivalentCategory.cat
  hom = Precategory.hom
  id = Precategory.idn
  idl = Precategory.seq-λ
  idr = Precategory.seq-ρ
  catAsso = Precategory.seq-α
  _,_∘_ = Precategory.seq
  _<_×_> = BinaryProduct.<_×_>
  AbEpicsAreCoKernelsNonProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  AbEpicsAreCoKernelsNonProp C abel = {A B S : ob (cat C)} → (k : hom (cat C) B S) → isEpic C k →
                                      Σ (hom (cat C) A B) (λ f → isCoKernel C (Abelian.AbHasZero abel) f k)

DiagonalMap : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
              hom (cat C) X (BinaryProduct.A×B bin)
DiagonalMap C {X = X} bin = bin < (id (cat C) X) × (id (cat C) X) >

IdZeroMap : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
            hom (cat C) X (BinaryProduct.A×B bin)
IdZeroMap C abel {X = X} bin = bin < id (cat C) X × ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel)) >

ZeroIdMap : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
            hom (cat C) X (BinaryProduct.A×B bin)
ZeroIdMap C abel {X = X} bin = bin < ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel)) × id (cat C) X >

IdMapLeftIsMonic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
                   {k : hom (cat C) X X} → isMonic C (bin < (id (cat C) X) × k >)
IdMapLeftIsMonic C {X = X} bin {k = k} D g h gMap=hMap =
  g                  ≡⟨ sym (idr (cat C) g) ⟩
  (g ∘ id (cat C) X) ≡⟨ cong (λ x → g ∘ x) (sym (BinaryProduct.pAcomp bin (id (cat C) X) k)) ⟩
  (g ∘ (Map ∘ pA))   ≡⟨ sym (catAsso (cat C) g Map pA) ⟩
  ((g ∘ Map) ∘ pA)   ≡⟨ cong (λ x → x ∘ pA) gMap=hMap ⟩
  ((h ∘ Map) ∘ pA)   ≡⟨ catAsso (cat C) h Map pA ⟩
  (h ∘ (Map ∘ pA))   ≡⟨ cong (λ x → h ∘ x) (BinaryProduct.pAcomp bin (id (cat C) X) k) ⟩
  (h ∘ id (cat C) X) ≡⟨ idr (cat C) h ⟩
  h ∎
    where
      _∘_ = _,_∘_ (cat C)
      Map = bin < (id (cat C) X) × k >
      pA = BinaryProduct.pA bin

IdMapRightIsMonic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
                    {k : hom (cat C) X X} → isMonic C (bin < k × (id (cat C) X) >)
IdMapRightIsMonic C {X = X} bin {k = k} D g h gMap=hMap =
  g                  ≡⟨ sym (idr (cat C) g) ⟩
  (g ∘ id (cat C) X) ≡⟨ cong (λ x → g ∘ x) (sym (BinaryProduct.pBcomp bin k (id (cat C) X))) ⟩
  (g ∘ (Map ∘ pB))   ≡⟨ sym (catAsso (cat C) g Map pB) ⟩
  ((g ∘ Map) ∘ pB)   ≡⟨ cong (λ x → x ∘ pB) gMap=hMap ⟩
  ((h ∘ Map) ∘ pB)   ≡⟨ catAsso (cat C) h Map pB ⟩
  (h ∘ (Map ∘ pB))   ≡⟨ cong (λ x → h ∘ x) (BinaryProduct.pBcomp bin k (id (cat C) X)) ⟩
  (h ∘ id (cat C) X) ≡⟨ idr (cat C) h ⟩
  h ∎
    where
      _∘_ = _,_∘_ (cat C)
      Map = bin < k × (id (cat C) X) >
      pB = BinaryProduct.pB bin

DiagonalMapIsMonic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
                     isMonic C (DiagonalMap C bin)
DiagonalMapIsMonic C bin = IdMapLeftIsMonic C bin

IdZeroMapIsMonic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
                   (bin : BinaryProduct C X X) → isMonic C (IdZeroMap C abel bin)
IdZeroMapIsMonic C abel bin = IdMapLeftIsMonic C bin

ZeroIdMapIsMonic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
                   (bin : BinaryProduct C X X) → isMonic C (ZeroIdMap C abel bin)
ZeroIdMapIsMonic C abel bin = IdMapRightIsMonic C bin

BinProdpAIsEpic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
                  isEpic C (BinaryProduct.pA bin)
BinProdpAIsEpic C {X = X} bin D g h pAg=pAh =
  g                  ≡⟨ sym (idl (cat C) g) ⟩
  (id (cat C) X ∘ g) ≡⟨ cong (λ x → x ∘ g) (sym (BinaryProduct.pAcomp bin (id (cat C) X) (id (cat C) X))) ⟩
  ((DMap ∘ pA) ∘ g)  ≡⟨ catAsso (cat C) DMap pA g ⟩
  (DMap ∘ (pA ∘ g))  ≡⟨ cong (λ x → DMap ∘ x) pAg=pAh ⟩
  (DMap ∘ (pA ∘ h))  ≡⟨ sym (catAsso (cat C) DMap pA h) ⟩
  ((DMap ∘ pA) ∘ h)  ≡⟨ cong (λ x → x ∘ h) (BinaryProduct.pAcomp bin (id (cat C) X) (id (cat C) X)) ⟩
  (id (cat C) X ∘ h) ≡⟨ idl (cat C) h ⟩
  h ∎
    where
      _∘_ = _,_∘_ (cat C)
      DMap = DiagonalMap C bin
      pA = BinaryProduct.pA bin

BinProdpBIsEpic : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {X : ob (cat C)} → (bin : BinaryProduct C X X) →
                  isEpic C (BinaryProduct.pB bin)
BinProdpBIsEpic C {X = X} bin D g h pBg=pBh =
  g                  ≡⟨ sym (idl (cat C) g) ⟩
  (id (cat C) X ∘ g) ≡⟨ cong (λ x → x ∘ g) (sym (BinaryProduct.pBcomp bin (id (cat C) X) (id (cat C) X))) ⟩
  ((DMap ∘ pB) ∘ g)  ≡⟨ catAsso (cat C) DMap pB g ⟩
  (DMap ∘ (pB ∘ g))  ≡⟨ cong (λ x → DMap ∘ x) pBg=pBh ⟩
  (DMap ∘ (pB ∘ h))  ≡⟨ sym (catAsso (cat C) DMap pB h) ⟩
  ((DMap ∘ pB) ∘ h)  ≡⟨ cong (λ x → x ∘ h) (BinaryProduct.pBcomp bin (id (cat C) X) (id (cat C) X)) ⟩
  (id (cat C) X ∘ h) ≡⟨ idl (cat C) h ⟩
  h ∎
    where
      _∘_ = _,_∘_ (cat C)
      DMap = DiagonalMap C bin
      pB = BinaryProduct.pB bin

KernelOfpAArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
             (bin : BinaryProduct C X X) →
             (UnivalentCategory.cat C), (ZeroIdMap C abel bin) ∘ (BinaryProduct.pA bin) ≡
             (ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel)))
KernelOfpAArrow C abel {X = X} bin =
  BinaryProduct.pAcomp bin (ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel))) (id (cat C) X)

KernelOfpAFactors : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
                    (bin : BinaryProduct C X X) →
                    kernelFactors C (Abelian.AbHasZero abel) (BinaryProduct.pA bin) (ZeroIdMap C abel bin)
KernelOfpAFactors C abel {X} bin {D} h hpA=0 =
  (h ∘ pB ) , 
  (sym (BinaryProduct.uni bin (0a D X) (h ∘ pB) ((h ∘ pB) ∘ zeroId)
  ((((h ∘ pB) ∘ zeroId) ∘ pA ) ≡⟨ catAsso (cat C) (h ∘ pB) zeroId pA ⟩
  ((h ∘ pB) ∘ (zeroId ∘ pA))   ≡⟨ cong (λ x → (h ∘ pB) ∘ x) (BinaryProduct.pAcomp bin (0a X X) (id (cat C) X)) ⟩
  ((h ∘ pB) ∘ 0a X X)          ≡⟨ ZeroArrowCompLeft C (Abelian.AbHasZero abel) (h ∘ pB) ⟩
  0a D X ∎)
  ((((h ∘ pB) ∘ zeroId) ∘ pB) ≡⟨ catAsso (cat C) (h ∘ pB) zeroId pB ⟩
  ((h ∘ pB) ∘ (zeroId ∘ pB))  ≡⟨ cong (λ x → (h ∘ pB) ∘ x) (BinaryProduct.pBcomp bin (0a X X) (id (cat C) X)) ⟩
  ((h ∘ pB) ∘ id (cat C) X)   ≡⟨ idr (cat C) (h ∘ pB) ⟩
  (h ∘ pB) ∎)))
  ∙ BinaryProduct.uni bin (0a D X) (h ∘ pB) h hpA=0 refl
  where
    _∘_ = _,_∘_ (cat C)
    0a : (a b : ob (cat C)) → hom (cat C) a b
    0a a b = ZeroArrow.f (getZeroArrow C {a} {b} (Abelian.AbHasZero abel))
    pB = BinaryProduct.pB bin
    pA = BinaryProduct.pA bin
    zeroId = ZeroIdMap C abel bin

KernelOfpA : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
             (bin : BinaryProduct C X X) → Kernel C (Abelian.AbHasZero abel) (BinaryProduct.pA bin)
KernelOfpA C abel bin = kernelConst (ZeroIdMap C abel bin)
                                    (KernelOfpAArrow C abel bin)
                                    (KernelOfpAFactors C abel bin)
                                    (ZeroIdMapIsMonic C abel bin)

KernelOfpBArrow : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
             (bin : BinaryProduct C X X) →
             (UnivalentCategory.cat C), (IdZeroMap C abel bin) ∘ (BinaryProduct.pB bin) ≡
             (ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel)))
KernelOfpBArrow C abel {X = X} bin =
  BinaryProduct.pBcomp bin (id (cat C) X) (ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel)))

KernelOfpBFactors : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
                    (bin : BinaryProduct C X X) →
                    kernelFactors C (Abelian.AbHasZero abel) (BinaryProduct.pB bin) (IdZeroMap C abel bin)
KernelOfpBFactors C abel {X} bin {D} h hpB=0 =
  (h ∘ pA) ,
  sym (BinaryProduct.uni bin (h ∘ pA) (0a D X) ((h ∘ pA) ∘ idZero)
  ((((h ∘ pA) ∘ idZero) ∘ pA) ≡⟨ catAsso (cat C) (h ∘ pA) idZero pA ⟩
  ((h ∘ pA) ∘ (idZero ∘ pA))  ≡⟨ cong (λ x → (h ∘ pA) ∘ x) (BinaryProduct.pAcomp bin (id (cat C) X)
                                   (ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel)))) ⟩
  ((h ∘ pA) ∘ (id (cat C) X)) ≡⟨ idr (cat C) (h ∘ pA) ⟩
  (h ∘ pA) ∎)
  ((((h ∘ pA) ∘ idZero) ∘ pB) ≡⟨ catAsso (cat C) (h ∘ pA) idZero pB ⟩
  ((h ∘ pA) ∘ (idZero ∘ pB))  ≡⟨ cong (λ x → (h ∘ pA) ∘ x) (BinaryProduct.pBcomp bin (id (cat C) X)
                                   (ZeroArrow.f (getZeroArrow C (Abelian.AbHasZero abel)))) ⟩
  ((h ∘ pA) ∘ 0a X X)         ≡⟨ ZeroArrowCompLeft C (Abelian.AbHasZero abel) (h ∘ pA) ⟩
  0a D X ∎))
  ∙ BinaryProduct.uni bin (h ∘ pA) (0a D X) h refl hpB=0
  where
    _∘_ = _,_∘_ (cat C)
    0a : (a b : ob (cat C)) → hom (cat C) a b
    0a a b = ZeroArrow.f (getZeroArrow C {a} {b} (Abelian.AbHasZero abel))
    pB = BinaryProduct.pB bin
    pA = BinaryProduct.pA bin
    idZero = IdZeroMap C abel bin

KernelOfpB : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
             (bin : BinaryProduct C X X) → Kernel C (Abelian.AbHasZero abel) (BinaryProduct.pB bin)
KernelOfpB C abel bin = kernelConst (IdZeroMap C abel bin)
                                    (KernelOfpBArrow C abel bin)
                                    (KernelOfpBFactors C abel bin)
                                    (IdZeroMapIsMonic C abel bin)

CoKernelOfKernelOfpA : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C ) → {X : ob (cat C)} →
                       (bin : BinaryProduct C X X) → AbEpicsAreCoKernelsNonProp C abel → 
                       CoKernel C (Abelian.AbHasZero abel) (Kernel.ker (KernelOfpA C abel bin))
CoKernelOfKernelOfpA C abel bin epic→coKer =
  isCoKernel→CoKernel C (Abelian.AbHasZero abel) (Kernel.ker (KernelOfpA C abel bin))
    {!!} {!!}
  where
    cok = AbEpicsAreCoKernelsNonProp

-- AbEpicsAreCoKernelsNonProp : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
-- AbEpicsAreCoKernelsNonProp C abel = {A B S : ob (cat C)} → (k : hom (cat C) B S) → isEpic C k →
--                                     Σ (hom (cat C) A B) (λ f → isCoKernel C (Abelian.AbHasZero abel) f k)
