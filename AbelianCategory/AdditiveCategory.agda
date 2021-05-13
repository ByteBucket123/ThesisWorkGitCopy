{-# OPTIONS --cubical #-}

module ThesisWork.AbelianCategory.AdditiveCategory where

open import Cubical.Foundations.Prelude
open import ThesisWork.BasicCategoryTheory.ExtendedCategoryDefinitions
open import ThesisWork.HelpFunctions
open import Cubical.HITs.PropositionalTruncation
open import ThesisWork.CompatibilityCode
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Semigroup.Base
open import ThesisWork.BasicCategoryTheory.Limits.ZeroObject
open import Cubical.Data.Sigma.Base

private
  ob = Precategory.ob
  cat = UnivalentCategory.cat
  hom = Precategory.hom
  id = Precategory.idn
  idl = Precategory.seq-λ
  idr = Precategory.seq-ρ
  catAsso = Precategory.seq-α
  _,_∘_ = Precategory.seq

--******************************************** Data structures ***********************************************************

record CategoryWithAbHomSets {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor abHomSets
  field
    abHomSet : (x y : ob (cat C)) → AbGroupStr (hom (cat C) x y)

private
  _,_,_+PreAdd_ : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (AbHomSet : CategoryWithAbHomSets C) → {x y : ob (cat C)} →
                       hom (cat C) x y → hom (cat C) x y → hom (cat C) x y
  _,_,_+PreAdd_ C AbHomSet {x = x} {y = y} = AbGroupStr._+_ (CategoryWithAbHomSets.abHomSet AbHomSet x y) 

record PreAdditiveCategory {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor preAddCat
  field
    isAbHomSet : CategoryWithAbHomSets C
    preAddLinear : {x y z : ob (cat C)} → {f : hom (cat C) x y} → {g h : hom (cat C) y z} → 
                   (cat C , f ∘ (C , isAbHomSet , g +PreAdd h)) ≡ (C , isAbHomSet , ((cat C) , f ∘ g) +PreAdd ((cat C) , f ∘ h))
    postAddLinear : {x y z : ob (cat C)} → {f g : hom (cat C) x y} → {h : hom (cat C) y z} →
                    cat C , (C , isAbHomSet , f +PreAdd g) ∘ h ≡ (C , isAbHomSet , ((cat C) , f ∘ h) +PreAdd ((cat C) , g ∘ h))

record BinDirectSum {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') (a b : ob (cat C)) : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor binDirSum
  field
    isPreAdd : PreAdditiveCategory C
    co : ob (cat C)
    in1 : hom (cat C) a co
    in2 : hom (cat C) b co
    p1 :  hom (cat C) co a
    p2 :  hom (cat C) co b
    in1p1 : ((cat C) , in1 ∘ p1) ≡ id (cat C) a
    in2p2 : ((cat C) , in2 ∘ p2) ≡ id (cat C) b
    p1in1+p2in2 : (C , (PreAdditiveCategory.isAbHomSet isPreAdd) , (cat C) , p1 ∘ in1 +PreAdd ((cat C) , p2 ∘ in2)) ≡ id (cat C) co

--TODO: Truncate hasBinDirSum.
record AdditiveCategory {ℓ ℓ'} (C : UnivalentCategory ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ  ℓ')) where
  constructor addCat
  field
    isPreAdd : PreAdditiveCategory C
    addHasZero : hasZeroObject C
    hasBinDirSum : (a b : ob (cat C)) → BinDirectSum C a b

--********************************************************* Theorem ******************************************************

private
  hom0 : {ℓ ℓ' : Level} → {C : UnivalentCategory ℓ ℓ'} → (preAdd : PreAdditiveCategory C) → (a b : ob (cat C)) → hom (cat C) a  b
  hom0 preAdd a b = AbGroupStr.0g (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet preAdd) a b)

zeroArrowIsZeroAlemma : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {a : ob (cat C)} → (hasZero : hasZeroObject C) →
                    (preAdd : PreAdditiveCategory C) →
                    (hom0 preAdd a (CategoryWithZeroObject.obj hasZero) ≡ ZeroArrow.f (getZeroArrow C hasZero)) ×
                    (hom0 preAdd (CategoryWithZeroObject.obj hasZero) a ≡ ZeroArrow.f (getZeroArrow C hasZero))
zeroArrowIsZeroAlemma C {a = a} hasZero preAdd =
  (isContr→isProp (ZeroObject.isTerm (CategoryWithZeroObject.isZero hasZero) a)
                  (hom0 preAdd a (CategoryWithZeroObject.obj hasZero))
                  (ZeroArrow.f (getZeroArrow C hasZero))) ,
  (isContr→isProp (ZeroObject.isInit (CategoryWithZeroObject.isZero hasZero) a)
                  (hom0 preAdd (CategoryWithZeroObject.obj hasZero) a)
                  (ZeroArrow.f (getZeroArrow C hasZero)))

zeroArrowIsZeroAlemma2 : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {a b c : ob (cat C)} → 
                         (preAdd : PreAdditiveCategory C) →
                         (f : hom (cat C) c b) →
                         (((cat C) , f ∘ hom0 preAdd b a) ≡ hom0 preAdd c a ) ×
                         (cat C , hom0 preAdd a c ∘ f ≡ hom0 preAdd a b)
zeroArrowIsZeroAlemma2 C {a} {b} {c} preAdd f =
  ((f ∘ 0g b a)                                      ≡⟨ sym (x+0=x (f ∘ 0g b a)) ⟩
  ((f ∘ 0g b a) + (0g c a))                          ≡⟨ cong (λ x → (f ∘ 0g b a) + x) (sym (x+-x=0 (f ∘ 0g b a))) ⟩
  ((f ∘ 0g b a) + ((f ∘ 0g b a) + (- (f ∘ 0g b a)))) ≡⟨ asso (f ∘ 0g b a) (f ∘ 0g b a) (- (f ∘ 0g b a)) ⟩
  (((f ∘ 0g b a) + (f ∘ 0g b a)) + (- (f ∘ 0g b a))) ≡⟨ cong (λ x → x + (- (f ∘ 0g b a)))
                                                             (sym (PreAdditiveCategory.preAddLinear preAdd)) ⟩
  ((f ∘ ((0g b a) + (0g b a))) + (- (f ∘ 0g b a)))   ≡⟨ cong (λ x → (f ∘ x) + (- (f ∘ 0g b a))) (x+0=x (0g b a)) ⟩
  ((f ∘ (0g b a)) + (- (f ∘ 0g b a)))                ≡⟨ x+-x=0 (f ∘ 0g b a) ⟩
  0g c a ∎) ,
  ((0g a c ∘ f)                                       ≡⟨ sym (x+0=x (0g a c ∘ f)) ⟩
  ((0g a c ∘ f) + (0g a b))                           ≡⟨ cong (λ x → (0g a c ∘ f) + x) (sym (x+-x=0 (0g a c ∘ f))) ⟩
  ((0g a c ∘ f) +  ((0g a c ∘ f) + (- (0g a c ∘ f)))) ≡⟨ asso (0g a c ∘ f) (0g a c ∘ f) (- (0g a c ∘ f)) ⟩
  (((0g a c ∘ f) +  (0g a c ∘ f)) + (- (0g a c ∘ f))) ≡⟨ cong (λ x → x + (- (0g a c ∘ f)))
                                                              (sym (PreAdditiveCategory.postAddLinear preAdd)) ⟩
  ((((0g a c) + (0g a c)) ∘ f) + (- (0g a c ∘ f)))    ≡⟨ cong (λ x → (x ∘ f) + (- (0g a c ∘ f))) (x+0=x (0g a c)) ⟩
  ((0g a c ∘ f) + (- (0g a c ∘ f)))                   ≡⟨ x+-x=0 (0g a c ∘ f) ⟩
  0g a b ∎)
    where
      0g = hom0 preAdd
      _+_ = _,_,_+PreAdd_ C (PreAdditiveCategory.isAbHomSet preAdd)
      _∘_ = _,_∘_ (cat C)
      -_ : {x y : ob (cat C)} → hom (cat C) x y → hom (cat C) x y 
      -_  {x = x} {y = y} = AbGroupStr.-_ (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet preAdd) x y)
      x+0=x : {a b : ob (cat C)} → (x : hom (cat C) a b) → x + (0g a b) ≡ x
      x+0=x {a} {b} x = fst (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet preAdd) a b)))) x)
      x+-x=0 : {a b : ob (cat C)} → (x : hom (cat C) a b) → x + (- x) ≡ 0g a b
      x+-x=0 {a} {b} x = fst (IsGroup.inverse (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet preAdd) a b))) x)
      asso : {a b : ob (cat C)} → (x y z : hom (cat C) a b) → x + (y + z) ≡ (x + y) + z
      asso {a} {b} x y z = IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet preAdd) a b))))) x y z

zeroArrowIsZeroAb : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {a b : ob (cat C)} → (hasZero : hasZeroObject C)
                    (preAdd : PreAdditiveCategory C) →
                    hom0 preAdd a b ≡ ZeroArrow.f (getZeroArrow C hasZero)
zeroArrowIsZeroAb C {a = a} {b = b} hasZero preAdd =
  0g a b                  ≡⟨ sym (fst (zeroArrowIsZeroAlemma2 C preAdd (0g a zero))) ⟩
  (0g a zero ∘ 0g zero b) ≡⟨ cong (λ x → 0g a zero ∘ x) (snd (zeroArrowIsZeroAlemma C hasZero preAdd)) ⟩
  (0g a zero ∘ 0a zero b) ≡⟨ cong (λ x → x ∘ 0a zero b) (fst (zeroArrowIsZeroAlemma C hasZero preAdd)) ⟩
  (0a a zero ∘ 0a zero b) ≡⟨ ZeroArrowIsUnique C hasZero
                             {h = 0a a zero} {k = ZeroArrow.toZero (getZeroArrow C {a} {b} hasZero)}
                             {j = 0a zero b} {l = ZeroArrow.fromZero (getZeroArrow C {a} {b} hasZero)}
                             (λ {g} {h} → cong₂ _∘_ (isContr→isProp (ZeroObject.isTerm (CategoryWithZeroObject.isZero hasZero) a)
                                                    g (0a a zero))
                                                    (isContr→isProp (ZeroObject.isInit (CategoryWithZeroObject.isZero hasZero) b)
                                                    h (0a zero b)))
                             (ZeroArrow→isZeroArrow C hasZero (getZeroArrow C {a} {b} hasZero)) ⟩
  0a a b ∎
    where
      0g = hom0 preAdd
      0a : (a b : ob (cat C)) → hom (cat C) a b
      0a a b = ZeroArrow.f (getZeroArrow C {a} {b} hasZero)
      zero = CategoryWithZeroObject.obj hasZero
      _+_ = _,_,_+PreAdd_ C (PreAdditiveCategory.isAbHomSet preAdd)
      _∘_ = _,_∘_ (cat C)

in1p2=0 : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {a b : ob (cat C)} → (hasZero : hasZeroObject C)
          (binSum : BinDirectSum C a b) →
          (cat C) , (BinDirectSum.in1 binSum) ∘ (BinDirectSum.p2 binSum) ≡ ZeroArrow.f (getZeroArrow C hasZero)
in1p2=0 C {a} {b} hasZero binSum =
  (in1 ∘ p2)                                                                 ≡⟨ sym (x+0=x (in1 ∘ p2)) ⟩
  ((in1 ∘ p2) + 0g a b)                                                      ≡⟨ cong (λ x → (in1 ∘ p2) + x)
                                                                                     (sym (x+-x=0 (in1 ∘ p2))) ⟩
  ((in1 ∘ p2) + ((in1 ∘ p2) + (- (in1 ∘ p2))))                               ≡⟨ asso (in1 ∘ p2) (in1 ∘ p2) (- (in1 ∘ p2)) ⟩
  (((in1 ∘ p2) + (in1 ∘ p2)) + (- (in1 ∘ p2)))                               ≡⟨ cong (λ x → x + (- (in1 ∘ p2)))
                                                                                     (cong₂ _+_ (sym (idl (cat C) (in1 ∘ p2)))
                                                                                                (sym (idr (cat C) (in1 ∘ p2)))) ⟩
  ((((1n a) ∘ (in1 ∘ p2)) + ((in1 ∘ p2) ∘ 1n b)) + (- (in1 ∘ p2)))           ≡⟨ cong₂ (λ x y → ((x ∘ (in1 ∘ p2)) + ((in1 ∘ p2) ∘ y))
                                                                                      + (- (in1 ∘ p2)))
                                                                                      (sym (BinDirectSum.in1p1 binSum))
                                                                                      (sym (BinDirectSum.in2p2 binSum)) ⟩
  ((((in1 ∘ p1) ∘ (in1 ∘ p2)) + ((in1 ∘ p2) ∘ (in2 ∘ p2))) + (- (in1 ∘ p2))) ≡⟨ cong₂ (λ x y → (x  + y) + (- (in1 ∘ p2)))
                                                                                      (sym (catAsso (cat C) (in1 ∘ p1) in1 p2))
                                                                                      (sym (catAsso (cat C) (in1 ∘ p2) in2 p2)) ⟩
  (((((in1 ∘ p1) ∘ in1) ∘ p2) + (((in1 ∘ p2) ∘ in2) ∘ p2)) + (- (in1 ∘ p2))) ≡⟨ cong (λ x → x + (- (in1 ∘ p2)))
                                                  (sym (PreAdditiveCategory.postAddLinear (BinDirectSum.isPreAdd binSum))) ⟩
  (((((in1 ∘ p1) ∘ in1) + ((in1 ∘ p2) ∘ in2)) ∘ p2) + (- (in1 ∘ p2)))        ≡⟨ cong₂ (λ x y → ((x + y) ∘ p2) + (- (in1 ∘ p2)))
                                                                                     (catAsso (cat C) in1  p1 in1)
                                                                                     (catAsso (cat C) in1 p2 in2) ⟩
  ((((in1 ∘ (p1 ∘ in1)) + (in1 ∘ (p2 ∘ in2))) ∘ p2) + (- (in1 ∘ p2)))        ≡⟨ cong (λ x → (x ∘ p2) + (- (in1 ∘ p2)))
                                                      (sym (PreAdditiveCategory.preAddLinear (BinDirectSum.isPreAdd binSum))) ⟩
  (((in1 ∘ ((p1 ∘ in1) + (p2 ∘ in2))) ∘ p2) + (- (in1 ∘ p2)))                 ≡⟨ cong (λ x → ((in1 ∘ x) ∘ p2) + (- (in1 ∘ p2)))
                                                                                (BinDirectSum.p1in1+p2in2 binSum) ⟩
  (((in1 ∘ 1n (BinDirectSum.co binSum)) ∘ p2) + (- (in1 ∘ p2)))              ≡⟨ cong (λ x → (x ∘ p2) + (- (in1 ∘ p2)))
                                                                                (idr (cat C) in1) ⟩
  ((in1 ∘ p2) + (- (in1 ∘ p2)))                                              ≡⟨ x+-x=0 (in1 ∘ p2) ⟩
  0g a b                                                                     ≡⟨ zeroArrowIsZeroAb C hasZero
                                                                                (BinDirectSum.isPreAdd binSum) ⟩
  0a ∎
    where
      _∘_ = _,_∘_ (cat C)
      0g = hom0 (BinDirectSum.isPreAdd binSum)
      0a = ZeroArrow.f (getZeroArrow C hasZero)
      1n = id (cat C)
      p1 = BinDirectSum.p1 binSum
      p2 = BinDirectSum.p2 binSum
      in1  = BinDirectSum.in1  binSum
      in2  = BinDirectSum.in2  binSum
      _+_ = _,_,_+PreAdd_ C (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum))
      -_ : {x y : ob (cat C)} → hom (cat C) x y → hom (cat C) x y 
      -_  {x = x} {y = y} = AbGroupStr.-_ (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) x y)
      x+0=x : {a b : ob (cat C)} → (x : hom (cat C) a b) → x + (0g a b) ≡ x
      x+0=x {a} {b} x = fst (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b)))) x)
      x+-x=0 : {a b : ob (cat C)} → (x : hom (cat C) a b) → x + (- x) ≡ 0g a b
      x+-x=0 {a} {b} x = fst (IsGroup.inverse (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b))) x)
      asso : {a b : ob (cat C)} → (x y z : hom (cat C) a b) → x + (y + z) ≡ (x + y) + z
      asso {a} {b} x y z = IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b))))) x y z
      comu : {a b : ob (cat C)} → (x y : hom (cat C) a b) → x + y ≡ y + x
      comu {a} {b} x y = IsAbGroup.comm (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b)) x y

      
in2p1=0 : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → {a b : ob (cat C)} → (hasZero : hasZeroObject C)
          (binSum : BinDirectSum C a b) →
          (cat C) , (BinDirectSum.in2 binSum) ∘ (BinDirectSum.p1 binSum) ≡ ZeroArrow.f (getZeroArrow C hasZero)
in2p1=0 C {a} {b} hasZero binSum =
  (in2 ∘ p1)                                                                 ≡⟨ sym (x+0=x (in2 ∘ p1)) ⟩
  ((in2 ∘ p1) + 0g b a)                                                      ≡⟨ cong (λ x → (in2 ∘ p1) + x)
                                                                                     (sym (x+-x=0 (in2 ∘ p1))) ⟩
  ((in2 ∘ p1) + ((in2 ∘ p1) + (- (in2 ∘ p1))))                               ≡⟨ asso (in2 ∘ p1) (in2 ∘ p1) (- (in2 ∘ p1)) ⟩
  (((in2 ∘ p1) + (in2 ∘ p1)) + (- (in2 ∘ p1)))                               ≡⟨ cong₂ (λ x y → (x + y) + (- (in2 ∘ p1)))
                                                                                  (sym (idl (cat C) (in2 ∘ p1)))
                                                                                  (sym (idr (cat C) (in2 ∘ p1))) ⟩
  ((((1n b) ∘ (in2 ∘ p1)) + ((in2 ∘ p1) ∘ (1n a))) + (- (in2 ∘ p1)))         ≡⟨ cong₂ (λ x y → ((x ∘ (in2 ∘ p1)) + ((in2 ∘ p1) ∘ y))
                                                                                      + (- (in2 ∘ p1)))
                                                                                  (sym (BinDirectSum.in2p2 binSum))
                                                                                  (sym (BinDirectSum.in1p1 binSum)) ⟩
  ((((in2 ∘ p2) ∘ (in2 ∘ p1)) + ((in2 ∘ p1) ∘ (in1 ∘ p1))) + (- (in2 ∘ p1))) ≡⟨ cong₂ (λ x y → (x + y) + (- (in2 ∘ p1)))
                                                                                  (sym (catAsso (cat C) (in2 ∘ p2) in2 p1))
                                                                                  (sym (catAsso (cat C) (in2 ∘ p1) in1 p1)) ⟩
  (((((in2 ∘ p2) ∘ in2) ∘ p1) + (((in2 ∘ p1) ∘ in1) ∘ p1)) + (- (in2 ∘ p1))) ≡⟨ cong (λ x → x + (- (in2 ∘ p1)))
                                                       (sym (PreAdditiveCategory.postAddLinear (BinDirectSum.isPreAdd binSum))) ⟩
  (((((in2 ∘ p2) ∘ in2) + ((in2 ∘ p1) ∘ in1)) ∘ p1) + (- (in2 ∘ p1)))        ≡⟨ cong₂ (λ x y → ((x + y) ∘ p1) + (- (in2 ∘ p1)))
                                                                                  (catAsso (cat C) in2 p2 in2)
                                                                                  (catAsso (cat C) in2 p1 in1) ⟩
  ((((in2 ∘ (p2 ∘ in2)) + (in2 ∘ (p1 ∘ in1))) ∘ p1) + (- (in2 ∘ p1)))        ≡⟨ cong (λ x → (x ∘ p1) + (- (in2 ∘ p1)))
                                                       (sym (PreAdditiveCategory.preAddLinear (BinDirectSum.isPreAdd binSum))) ⟩
  (((in2 ∘ ((p2 ∘ in2) + (p1 ∘ in1))) ∘ p1) + (- (in2 ∘ p1)))                ≡⟨ cong (λ x → ((in2 ∘ x) ∘ p1) + (- (in2 ∘ p1)))
                                                                                  (comu (p2 ∘ in2) (p1 ∘ in1)) ⟩
  (((in2 ∘ ((p1 ∘ in1) + (p2 ∘ in2))) ∘ p1) + (- (in2 ∘ p1)))                ≡⟨ cong (λ x → ((in2 ∘ x) ∘ p1) + (- (in2 ∘ p1)))
                                                                                   (BinDirectSum.p1in1+p2in2 binSum) ⟩
  (((in2 ∘ 1n (BinDirectSum.co binSum)) ∘ p1) + (- (in2 ∘ p1)))              ≡⟨ cong (λ x → (x ∘ p1) + (- (in2 ∘ p1)))
                                                                                  (idr (cat C) in2) ⟩
  ((in2 ∘ p1) + (- (in2 ∘ p1)))                                              ≡⟨ x+-x=0 (in2 ∘ p1) ⟩
  0g b a                                                                     ≡⟨ zeroArrowIsZeroAb C hasZero
                                                                                  (BinDirectSum.isPreAdd binSum) ⟩
  0a ∎
    where
      _∘_ = _,_∘_ (cat C)
      0g = hom0 (BinDirectSum.isPreAdd binSum)
      0a = ZeroArrow.f (getZeroArrow C hasZero)
      1n = id (cat C)
      p1 = BinDirectSum.p1 binSum
      p2 = BinDirectSum.p2 binSum
      in1  = BinDirectSum.in1  binSum
      in2  = BinDirectSum.in2  binSum
      _+_ = _,_,_+PreAdd_ C (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum))
      -_ : {x y : ob (cat C)} → hom (cat C) x y → hom (cat C) x y 
      -_  {x = x} {y = y} = AbGroupStr.-_ (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) x y)
      x+0=x : {a b : ob (cat C)} → (x : hom (cat C) a b) → x + (0g a b) ≡ x
      x+0=x {a} {b} x = fst (IsMonoid.identity (IsGroup.isMonoid (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b)))) x)
      x+-x=0 : {a b : ob (cat C)} → (x : hom (cat C) a b) → x + (- x) ≡ 0g a b
      x+-x=0 {a} {b} x = fst (IsGroup.inverse (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b))) x)
      asso : {a b : ob (cat C)} → (x y z : hom (cat C) a b) → x + (y + z) ≡ (x + y) + z
      asso {a} {b} x y z = IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (IsAbGroup.isGroup (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b))))) x y z
      comu : {a b : ob (cat C)} → (x y : hom (cat C) a b) → x + y ≡ y + x
      comu {a} {b} x y = IsAbGroup.comm (AbGroupStr.isAbGroup (CategoryWithAbHomSets.abHomSet (PreAdditiveCategory.isAbHomSet (BinDirectSum.isPreAdd binSum)) a b)) x y


-- --  Definition isBinDirectSum (a b co : A) (i1 : a --> co) (i2 : b --> co)
-- --             (p1 : co --> a) (p2 : co --> b) : hProp :=
-- --    i1 · p1 = 1  ∧  i2 · p2 = 1  ∧
-- --    i1 · p2 = 0  ∧  i2 · p1 = 0  ∧
-- --    p1 · i1 + p2 · i2 = 1.
