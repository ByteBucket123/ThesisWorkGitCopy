{-# OPTIONS --cubical #-}

module ThesisWork.UnivalentFormulations where

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import ThesisWork.CompatibilityCode
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Fiberwise

ob = Precategory.ob

infixl 20 _<*>_
_<*>_ : ∀ {a b} {A : I → Type a} {B : ∀ i → A i → Type b}
        → ∀ {f g} → (\ i → (a : A i) → B i a) [ f ≡ g ]
        → ∀ {x y} → (p : A [ x ≡ y ])
        → (\ i → B i (p i)) [ f x ≡ g y ]
p <*> q = \ i → p i (q i)

tempΣ≡ : {ℓ ℓ' : Level} → ∀ {A B} → {x y : Σ {ℓ} {ℓ'} A B} → (p : fst x ≡ fst y)
                       → (\ i → B (p i)) [ snd x ≡ snd y ]
                       → x ≡ y
tempΣ≡ p q = cong (_,_) p <*> q

--Alternative definition of univalent category.

record isUnivalentAlt {ℓ ℓ' : Level} (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    univ : (x : ob C) → isContr (Σ (ob C) (λ y → CatIso {C = C} x y))

isoEquivToUnivalentHelp : {ℓ : Level} → {C : Precategory ℓ ℓ} →
                      ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) →
                      ((x : ob C) → isContr (Σ (ob C) (λ y →  x ≡ y))) →
                      isUnivalentAlt C
isoEquivToUnivalentHelp {C = C} isocat contrEq = record{ univ = λ x → transport (cong (λ x → isContr (Σ (ob C) x)) (funExt (λ y → ua (isocat x y)))) (contrEq x) }

isoEquivToUnivalentAlt : {ℓ : Level} → {C : Precategory ℓ ℓ} →
                         ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) →
                         isUnivalentAlt C
isoEquivToUnivalentAlt = flip isoEquivToUnivalentHelp (λ x → isContrSingl x)


--************************************************************ Test *******************************************************

--ua-gluePath

--congSigma≃ : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ} → {C : Type ℓ'} →
--             (F : Type ℓ → C → Type ℓ'') → (A ≃ B) → Σ C (F A) ≃ Σ C (F B)
--congSigma≃ {C = C} F e = pathToEquiv (cong (λ x → Σ C (F x)) (ua e))

--congSigma≃ : {ℓ ℓ' ℓ'' : Level} → {C : Type ℓ'} → {A : C → Type ℓ} → {B : C → Type ℓ} → (f : (y : C) → A y ≃ B y) → Σ C A ≃ Σ C B
--congSigma≃ {C = C} e = pathToEquiv (cong (λ x → Σ C x) (funExt (λ x → ua (e x))))

--isoEquivToUnivalentAlt' : {ℓ : Level} → {C : Precategory (ℓ-suc ℓ) ℓ} →
--                         ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) →
--                         isUnivalentAlt C
--isoEquivToUnivalentAlt' {C = C} isoCat = record{ univ = λ x → transport (cong (λ y → isContr (Σ (ob C) y))
--                                           (lower (lift (funExt (λ y → ua {!isoCat x y!}))))) {!!}}
--  record{ univ = λ x →  invEq (cong≃ isContr {!cong≃ (Σ (ob C)) ?!}) {!!}}

--isoEquivToUnivalentHelp' : {ℓ ℓ' : Level} → {C : Precategory ℓ ℓ'} →
--                      ((x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y) →
--                      ((x : ob C) → isContr (Σ (ob C) (λ y →  x ≡ y))) →
--                      isUnivalentAlt C
--isoEquivToUnivalentHelp' {C = C} isocat contrEq = record{ univ = λ x → transp (λ i → ua-gluePath (congSigma≃ λ y → {!isocat x y!}) {!!} {!!} i) i0 (contrEq x)}

--************************************************************* Help Theorems ******************************************************************************************

idCatIso : {ℓ ℓ' : Level} → {C : Precategory ℓ ℓ'} → (x : Precategory.ob C) → CatIso {C = C} x x
idCatIso {C = C} x = catiso (Precategory.idn C x) (Precategory.idn C x) (Precategory.seq-λ C (Precategory.idn C x)) (Precategory.seq-ρ C (Precategory.idn C x))



--************************************************************* *******************************************************************************************

makeUnivalentFromSet : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') →
                       ((x y : Precategory.ob C) → isProp (x ≡ y)) →
                       ((x y : Precategory.ob C) → isProp (CatIso {C = C} x y)) →
                       ((x y : Precategory.ob C) → CatIso {C = C} x y → x ≡ y) →
                       isUnivalent C
makeUnivalentFromSet C propEq propCatIso catIso→Eq = record {univ = λ x y → equivIsEquiv (isoToEquiv
  (record {fun = pathToIso x y ;
           inv = catIso→Eq x y ;
           leftInv = λ z → propEq x y (catIso→Eq x y (pathToIso x y z)) z ;
           rightInv = λ z → propCatIso x y (pathToIso x y (catIso→Eq x y z)) z }))}

makeUnivalentFromSetEq : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                       ((x y : Precategory.ob C) → isProp (x ≡ y)) →
                       ((x y : Precategory.ob C) → (CatIso {C = C} x y) ≃ (x ≡ y)) →
                       isUnivalent C
makeUnivalentFromSetEq C propEq EquivIso = makeUnivalentFromSet C propEq (λ x y → transport (cong isProp (sym (ua (EquivIso x y)))) (propEq x y)) λ x y → equivFun (EquivIso x y)

univalent→Alt' : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                ((x y : Precategory.ob C) → isProp (x ≡ y)) →
                isUnivalent C →
                isUnivalentAlt C
univalent→Alt' C propEq isUniv = isoEquivToUnivalentHelp (univEquiv isUniv) (λ x → (x , refl) , (λ z → ΣPathP ((snd z) , (isProp→PathP (λ i → propEq x (snd z i)) refl (snd z)))))

univalent→Alt : {ℓ : Level} → (C : Precategory ℓ ℓ) →
                isUnivalent C →
                isUnivalentAlt C
univalent→Alt C isUniv = isoEquivToUnivalentAlt (univEquiv isUniv)

isContr→EquivFun : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → isContr A → isContr B → (f : A → B) → isEquiv f
isContr→EquivFun isContrA isContrB f = equivIsEquiv (isoToEquiv (
  iso f (λ b → fst isContrA) (λ z → isContr→isProp isContrB (f (fst isContrA)) z) (snd isContrA)))

univalentAlt→' : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') →
                isUnivalentAlt C →
                isUnivalent C
univalentAlt→' C isUnivAlt =
  record {univ = λ x → fiberEquiv (λ y → x ≡ y) (λ y → CatIso {C = C} x y) (pathToIso x) (
                                  isContr→EquivFun (isContrSingl x) (isUnivalentAlt.univ isUnivAlt x) (total x)) }
  where
    total : (x : ob C) → singl x → Σ (ob C) (CatIso x)
    total x = (\ p → p .fst , pathToIso x (p .fst) (p .snd))

univalentAlt→ : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') →
                isUnivalentAlt C →
                isUnivalent C
univalentAlt→ C isUnivAlt = record {univ = λ x y → isContrToUniv CatIso (pathToIso _ _) (isUnivalentAlt.univ isUnivAlt)}

--                                  (record {equiv-proof = λ y → {!!}})}

--univalentAlt→isProp : {ℓ : Level} → (C : Precategory ℓ ℓ) →
--                     isUnivalentAlt C →
--                     (x y : Precategory.ob C) → isProp (CatIso {C = C} x y)
--univalentAlt→isProp C isUniv x y p q = (sym (snd (PathPΣ (snd (isUnivalentAlt.univ isUniv x) (y , p))))) ∙ {!!}
--snd (PathPΣ (snd (isUnivalentAlt.univ isUniv x) (x , idCatIso x)))

--univalentAlt→ : {ℓ : Level} → (C : Precategory ℓ ℓ) →
--                ((x y : Precategory.ob C) → isProp (x ≡ y)) →
--                isUnivalentAlt C →
--                isUnivalent C
--univalentAlt→ C propEq isUniv = {!!}

--*************************************************** Lift univalence ****************************************************

liftFun : {ℓ ℓ' : Level} → {A B : Type ℓ} → (f : A → B) → Lift {ℓ} {ℓ'} A → Lift {ℓ} {ℓ'} B
liftFun f (lift a) = lift (f a)

liftFunFlip : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → (f : A → B) → Lift {ℓ} {ℓ'} A → Lift {ℓ'} {ℓ} B
liftFunFlip f (lift a) = lift (f a)

liftFun2 : {ℓ ℓ' : Level} → {A B C : Type ℓ} → (f : A → B → C) → Lift {ℓ} {ℓ'} A → Lift {ℓ} {ℓ'} B → Lift {ℓ} {ℓ'} C
liftFun2 f (lift a) (lift b) = lift (f a b)

lowerExt :{ℓ ℓ' : Level} → {A : Type ℓ} → {a b : Lift {ℓ} {ℓ'} A} → a ≡ b → lower a ≡ lower b
lowerExt x i = lower (x i)

PreCatLift : {ℓ ℓ' : Level} → Precategory ℓ ℓ' → Precategory (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
PreCatLift {ℓ} {ℓ'} precat =
  record {ob    = Lift {ℓ} {ℓ'} (Precategory.ob precat) ;
          hom   = λ (lift x) (lift y) → Lift {ℓ'} {ℓ} (Precategory.hom precat x y) ;
          idn   = λ x → lift (Precategory.idn precat (lower x)) ;
          seq   = liftFun2 (Precategory.seq precat) ;
          seq-λ = λ f → liftExt (Precategory.seq-λ precat (lower f)) ;
          seq-ρ = λ f → liftExt (Precategory.seq-ρ precat (lower f)) ;
          seq-α = λ f g h → liftExt (Precategory.seq-α precat (lower f) (lower g) (lower h)) }

PreCat≡ : {ℓ ℓ' : Level} → {x y : Precategory ℓ ℓ'} → 
          (obEq : ob x ≡ ob y) →
          (homEq : (\ i → (u w : obEq i) → Type ℓ') [ Precategory.hom x ≡ Precategory.hom y ]) →
          (idnEq : (\ i → (u : obEq i) → homEq i u u) [ Precategory.idn x ≡ Precategory.idn y ]) →
          (seqEq : (\ i → {x y z : obEq i} → homEq i x y → homEq i y z → homEq i x z)
            [ Precategory.seq x ≡ Precategory.seq y ]) →
          (seq-λEq : (\ i → {x y : obEq i} → (f : homEq i x y) → seqEq i (idnEq i x) f ≡ f)
            [ Precategory.seq-λ x ≡ Precategory.seq-λ y ]) →
          (seq-ρEq : (\ i → {x y : obEq i} → (f : homEq i x y) → seqEq i f (idnEq i y) ≡ f)
            [ Precategory.seq-ρ x ≡ Precategory.seq-ρ y ]) →
          (seqEq-α : (\ i → {u v w x : obEq i} → (f : homEq i u v) → (g : homEq i v w) → (h : homEq i w x) →
            seqEq i (seqEq i f g) h ≡ seqEq i f (seqEq i g h))
              [ Precategory.seq-α x ≡ Precategory.seq-α y ]) →
          x ≡ y
PreCat≡ obEq homEq idnEq seqEq seq-λEq seq-ρEq seq-αEq i =
  record {ob = obEq i ;
          hom = homEq i ;
          idn = idnEq i ;
          seq = seqEq i ;
          seq-λ = seq-λEq i ;
          seq-ρ = seq-ρEq i ;
          seq-α = seq-αEq i }

LiftCatIsoIso : {ℓ ℓ' : Level} → (C : Precategory ℓ ℓ') →
                {x y : Precategory.ob C} →
                Iso (CatIso {C = C} x y) (CatIso {C = PreCatLift C} (lift x) (lift y))
LiftCatIsoIso C =
  iso (λ x → catiso (lift (CatIso.h x))
                    (lift (CatIso.h⁻¹ x))
                    (liftExt (CatIso.sec x))
                    (liftExt (CatIso.ret x)))
      (λ x → catiso (lower (CatIso.h x))
                    (lower (CatIso.h⁻¹ x))
                    (lowerExt (CatIso.sec x))
                    (lowerExt (CatIso.ret x)))
      (λ z → refl)
       λ z → refl

module _ {ℓ ℓ' : Level} {C : Precategory ℓ ℓ'} (isocat : (x y : ob C) → (x ≡ y) ≃ CatIso {C = C} x y)  where
  LiftUnivAltHelp : (x y : Precategory.ob C) →
                    (x ≡ y) ≃ CatIso {C = PreCatLift C} (lift x) (lift y)
  LiftUnivAltHelp x y = compEquiv (isocat x y) (isoToEquiv (LiftCatIsoIso C))

  LiftExtEquiv : (x y : Precategory.ob C) → (lift {ℓ} {ℓ'} x ≡ lift {ℓ} {ℓ'} y) ≃ (x ≡ y)
  LiftExtEquiv x y = isoToEquiv (iso lowerExt
                                     liftExt
                                     (λ z → refl)
                                     (λ z → refl))

  LiftUnivAlt : isUnivalentAlt (PreCatLift C)
  LiftUnivAlt = isoEquivToUnivalentAlt (λ x y →
                  compEquiv (LiftExtEquiv (lower x) (lower y))
                    (LiftUnivAltHelp (lower x) (lower y)))

  LiftCatIsoIso' : {x y : Precategory.ob C} →
                       Iso (Lift {ℓ'} {ℓ} (CatIso {C = C} x y)) (CatIso {C = PreCatLift C} (lift x) (lift y))
  LiftCatIsoIso' =
    iso (λ (lift a) → Iso.fun (LiftCatIsoIso C) a)
        (λ b → lift (Iso.inv (LiftCatIsoIso C) b))
        (λ z → refl)
         λ z → refl

  LiftUnivAltHelpΣ : {x : Precategory.ob C} →
                     Iso (Lift {ℓ-max ℓ ℓ'} {ℓ'} (Σ (ob C) (λ y → CatIso {C = C} x y)))
                         (Σ (ob (PreCatLift C)) (λ y → CatIso {C = PreCatLift C} (lift x) y))
  LiftUnivAltHelpΣ =
    iso (λ (lift (ob , a)) →      (lift ob)   , (Iso.fun (LiftCatIsoIso C) a))
        (λ       (ob , b)  → lift ((lower ob) , Iso.inv (LiftCatIsoIso C) b))
        (λ z → refl)
         λ z → refl

  isPropΣCatIso : {x y : Precategory.ob C} → isProp (Σ (ob C) (λ y → CatIso {C = C} x y))
  isPropΣCatIso {x} {y} a b =
    lowerExt (isContr→isProp (transport (cong isContr (sym (ua (isoToEquiv LiftUnivAltHelpΣ))))
      (isUnivalentAlt.univ LiftUnivAlt (lift x))) (lift a) (lift b))

  isUnivAlt : isUnivalentAlt C
  isUnivAlt = record {univ = λ x → (x , (idCatIso x)) ,
    (λ z → isProp→PathP (λ i → (isPropΣCatIso {y = fst z})) (x , (idCatIso x)) z)}
