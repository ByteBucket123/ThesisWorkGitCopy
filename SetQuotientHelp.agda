{-# OPTIONS --cubical --no-import-sorts #-}

module ThesisWork.SetQuotientHelp where

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥; ∣_∣; squash)
                                                              renaming (elim2 to elim2HProp ;
                                                                        rec to recHProp)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂; ∣_∣₂; squash₂)

open import ThesisWork.HelpFunctions
open import ThesisWork.PathInductionHelp
open import Cubical.Foundations.Path
--for funDepTr, this is somewhere in the standard library, but ai can't find it...
--open import ThesisWork.SetSigmaType 

HelpEq/ : {ℓ : Level} → {A : Type ℓ} → {R : A → A → Type ℓ} →
         (p q : A / R) → ((p' : Σ A (λ a → [ a ] ≡ p)) →  (q' : Σ A (λ a → [ a ] ≡ q)) → [ fst p' ] ≡ [ fst q' ]) →
         p ≡ q
HelpEq/ p q [a]=[b] = recHProp (squash/ _ _) (recHProp (isPropΠ (λ x → squash/ _ _))
                       (λ (a , [a]=p) (b , [b]=q) → p     ≡⟨ sym [a]=p ⟩
                                                    [ a ] ≡⟨ [a]=[b] (a , [a]=p) (b , [b]=q) ⟩
                                                    [ b ] ≡⟨ [b]=q ⟩
                                                    q ∎)
                       ([]surjective p)) ([]surjective q)

rec3 : {ℓ : Level} {A B : Type ℓ} {R : A → A → Type ℓ} (Bset : isSet B)
       (f : A → A → A → B)
         (feqf : (a b c d : A) (r : R a b) → f a c d ≡ f b c d)
         (feqm : (a b c d : A) (r : R b c) → f a b d ≡ f a c d)
         (feql : (a b c d : A) (r : R c d) → f a b c ≡ f a b d)
      → A / R → A / R → A / R → B
rec3 Bset f feqf feqm feql = rec (isSetΠ (λ _ → isSetΠ (λ _ → Bset)))
                                 (λ a → rec2 Bset (f a) (feqm a) (feql a))
                                 λ a b r → funExt (elimProp (λ x → liftFunExt Bset)
                                                   λ c → funExt (elimProp (λ _ → Bset _ _) (λ d → feqf a b c d r)))

funDepTr2l : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {C : Type ℓ'} → {B : A → C → Type ℓ''} → {a0 a1 : A} → (p : a0 ≡ a1) →
           (z : C) → (u0 : B a0 z) → (u1 : B a1 z) →
           PathP (λ i → B (p i) z) u0 u1 ≡ Path (B a1 z) (transport (λ i → B (p i) z) u0) u1
funDepTr2l {B = B} p z u0 u1 j = PathP (λ i → B (p (j ∨ i)) z) (transport-filler (λ i → B (p i) z) u0 j) u1

elim2 : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} {B : A / R → A / R → Type ℓ}
     → ((x y : A / R) → isSet (B x y))
     → (f : (a b : A) → (B [ a ] [ b ] ))
     → ((a b c : A) (r : R a b) → PathP (λ i → B (eq/ a b r i) [ c ] ) (f a c) (f b c))
     → ((a b c : A) (r : R b c) → PathP (λ i → B [ a ] (eq/ b c r i)) (f a b) (f a c))
     → (x y : A / R)
     → B x y
elim2 {A = A} {R = R} {B = B} Bset f feql feqr =
  elim (λ x → isSetΠ (Bset x))
       (λ x → elim (Bset [ x ]) (f x) (feqr x))
        λ x y r → funExt (elimProp (λ z → subst isProp
          (sym (funDepTr2l {B = B} (eq/ x y r) z (g x z) (g y z)))
            (Bset [ y ] z (transport (λ i → B (eq/ x y r i) z) (g x z)) (g y z)))
            λ z → feql x y z r)
    where
      g : (x : A) → (z : A / R) → B [ x ] z
      g x z = elim (Bset [ x ]) (f x) (feqr x) z

funDepTr3l : {ℓ ℓ' ℓ'' ℓ''' : Level} → {A : Type ℓ} → {C : Type ℓ'} {D : Type ℓ''} → {B : A → C → D →  Type ℓ'''} →
             {a0 a1 : A} → (p : a0 ≡ a1) →
             (z : C) → (w : D) → (u0 : B a0 z w) → (u1 : B a1 z w) →
             PathP (λ i → B (p i) z w) u0 u1 ≡ Path (B a1 z w) (transport (λ i → B (p i) z w) u0) u1
funDepTr3l {B = B} p z w u0 u1 j = PathP (λ i → B (p (j ∨ i)) z w) (transport-filler (λ i → B (p i) z w) u0 j) u1

funDepTr3m : {ℓ ℓ' ℓ'' ℓ''' : Level} → {A : Type ℓ} → {C : Type ℓ'} {D : Type ℓ''} → {B : A → C → D →  Type ℓ'''} →
             {c0 c1 : C} → (p : c0 ≡ c1) →
             (z : A) → (w : D) → (u0 : B z c0 w) → (u1 : B z c1 w) →
             PathP (λ i → B z (p i) w) u0 u1 ≡ Path (B z c1 w) (transport (λ i → B z (p i) w) u0) u1
funDepTr3m {B = B} p z w u0 u1 j = PathP (λ i → B z (p (j ∨ i)) w) (transport-filler (λ i → B z (p i) w) u0 j) u1

funDepTr3r : {ℓ ℓ' ℓ'' ℓ''' : Level} → {A : Type ℓ} → {C : Type ℓ'} {D : Type ℓ''} → {B : A → C → D →  Type ℓ'''} →
             {d0 d1 : D} → (p : d0 ≡ d1) →
             (z : A) → (w : C) → (u0 : B z w d0) → (u1 : B z w d1) →
             PathP (λ i → B z w (p i)) u0 u1 ≡ Path (B z w d1) (transport (λ i → B z w (p i)) u0) u1
funDepTr3r {B = B} p z w u0 u1 j = PathP (λ i → B z w (p (j ∨ i))) (transport-filler (λ i → B z w (p i)) u0 j) u1


liftFunExtDepRight : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → A → A → Type ℓ'} →
                     ((x y z : A) → isSet (B x y z)) → (x y : A) → 
                     {h k : (z : A) → B x y z} → (p q : h ≡ k) → p ≡ q
liftFunExtDepRight Bset x y {h} {k} p q i = funExt (λ z → Bset x y z (h z) (k z) (λ j → p j z ) (λ j → q j z) i)

liftFunExtDep : {ℓ : Level} → {A : Type ℓ} → {B : A → A → A → Type ℓ} →
                ((x y z : A) → isSet (B x y z)) → {x y : A} → (z : A) →
                (p : x ≡ y) → 
                (h : (w : A) → B (p i0) z w) →
                (k : (w : A) → B (p i1) z w) →
                (q r : PathP (λ i → (w : A) → B (p i) z w) h k) →
                q ≡ r
liftFunExtDep {A = A} {B = B} Bset {x} {y} z p =
  PathInduction C x (λ _ _ → liftFunExtDepRight Bset x z) y p 
    where
      C = λ x y p →
            (h : (w : A) → B (p i0) z w) → (k : (w : A) → B (p i1) z w) →
            (q r : PathP (λ i → (w : A) → B (p i) z w) h k) → q ≡ r

--Pi (h k : T) Pi (p q : h \equiv k) p  \equiv q 
--T = Pi (w : A) B x z w

--  funExt (λ w → subst {!!}
--                      (sym (funDepTr3l {B = B} p z w (h w) (k w)))
--                      (Bset y z w (transport (λ i → B (p i) z w) (h w)) (k w)
--                        (transport (PathP≡Path (λ i → B (p i) z w) (h w) (k w)) (λ j → q j w))
--                        (transport (PathP≡Path (λ i → B (p i) z w) (h w) (k w)) λ j → r j w)
--                        i))

--subst isProp
--                                           (sym (funDepTr3l {B = B} (eq/ x y r) [ z ] w (g x [ z ] w) (g y [ z ] w)))
--                                           (Bset [ y ] [ z ] w (transport (λ i → B (eq/ x y r i) [ z ] w) (g x [ z ] w))
--                                             (g y [ z ] w)))

--Bset (p j) z w (q j w) (r j w) {!!} {!!} j i
--  funExt λ w → transport (sym (funDepTr3l p z w (h w) (k w)))
--                         (Bset y z w (transport (λ j → B (p j) z w) {!!}) {!!} {!!} {!!})

lemmaElim3 : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} {B : A / R → A / R → A / R → Type ℓ} → 
             (Bset : (x y z : A / R) → isSet (B x y z)) →
             (f : (a b c : A) → (B [ a ] [ b ] [ c ] )) →
             (feqm : (a b c d : A) (r : R b c) → PathP (λ i → B [ a ] (eq/ b c r i) [ d ]) (f a b d) (f a c d)) →
             (feql : (a b c d : A) (r : R c d) → PathP (λ i → B [ a ] [ b ] (eq/ c d r i)) (f a b c) (f a b d))
             (x y : A) → (r : R x y) → (x' : A / R) → 
             isProp  (PathP (λ i → (z₁ : A / R) → B (eq/ x y r i) x' z₁)
               (elim2 (Bset [ x ]) (f x) (feqm x) (feql x) x')
               (elim2 (Bset [ y ]) (f y) (feqm y) (feql y) x'))
lemmaElim3 Bset f feqm feql x y r x' = liftFunExtDep Bset x' (eq/ x y r)
                                                     (elim2 (Bset [ x ]) (f x) (feqm x) (feql x) x')
                                                     (elim2 (Bset [ y ]) (f y) (feqm y) (feql y) x')

elim3 : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} {B : A / R → A / R → A / R → Type ℓ}
     → ((x y z : A / R) → isSet (B x y z))
     → (f : (a b c : A) → (B [ a ] [ b ] [ c ] ))
     → ((a b c d : A) (r : R a b) → PathP (λ i → B (eq/ a b r i) [ c ] [ d ] ) (f a c d) (f b c d))
     → ((a b c d : A) (r : R b c) → PathP (λ i → B [ a ] (eq/ b c r i) [ d ]) (f a b d) (f a c d))
     → ((a b c d : A) (r : R c d) → PathP (λ i → B [ a ] [ b ] (eq/ c d r i)) (f a b c) (f a b d))
     → (x y z : A / R)
     → B x y z
elim3 {A = A} {R = R} {B = B} Bset f feqf feqm feql =
  elim (λ x → isSetΠ (λ y → isSetΠ (λ z → Bset x y z)))
       (λ x → elim2 (Bset [ x ]) (f x) (feqm x) (feql x))
       λ x y r → funExt (elimProp (λ x' → lemmaElim3 Bset f feqm feql x y r x' )
                                  (λ z → funExt (elimProp (λ w → subst isProp
                                           (sym (funDepTr3l {B = B} (eq/ x y r) [ z ] w (g x [ z ] w) (g y [ z ] w)))
                                           (Bset [ y ] [ z ] w (transport (λ i → B (eq/ x y r i) [ z ] w) (g x [ z ] w))
                                             (g y [ z ] w)))
                                                          λ w → feqf x y z w r)))
    where
      g : (x : A) → (z w : A / R) → B [ x ] z w
      g x z w = elim2 (Bset [ x ]) (f x) (feqm x) (feql x) z w

--                                  (λ z → funExt (elimProp (λ w → subst isProp
--                                           (sym (funDepTr3l {B = B} (eq/ x y r) [ z ] w (g x [ z ] w) (g y [ z ] w)))
--                                           (Bset [ y ] [ z ] w (transport (λ i → B (eq/ x y r i) [ z ] w) (g x [ z ] w))
--                                             (g y [ z ] w)))
--                                                          λ w → feqf x y z w r)))
--    where
--      g : (x : A) → (z w : A / R) → B [ x ] z w
--      g x z w = elim2 (Bset [ x ]) (f x) (feqm x) (feql x) z w

--       λ x y r → funExt (elimProp {!!}
--                                  (λ z → funExt (elimProp (λ w →
--                                    subst isProp (sym (funDepTr3l {B = B} (eq/ x y r) z w (g x z w) (g y z w))) (
--                                      Bset [ y ] z w (transport (λ i → B (eq/ x y r i) z w) (g x z w)) (g y z w)))
--                                      λ w → ?)))


--elim2Help : {ℓ : Level} {A : Type ℓ} {R : A → A → Type ℓ} {B : A / R → A / R → Type ℓ}
--            (z : A / R )
--            (Bprop : (x : A / R ) → isProp (B x z))
--            {x y : A / R}
--            (eq : x ≡ y)
--            (bx : B x z)
--            (by : B y z) →
--            PathP (λ i → B (eq i) z) bx by
--elim2Help {B = B} z Bprop {x = x} =
--  J (λ y eq → ∀ bx by → PathP (λ i → B (eq i) z) bx by) (λ bx by → Bprop x bx by)

--λ x y r → funExt (elimProp (λ z → subst isProp (sym (
--                                                   funDepTr _ _ _ _ (eq/ x y r) (g x z) (g y z)))
--                                                     (Bset [ y ] z (transport _ (elim (Bset [ x ]) (f x) (feqr x) z))
--                                                       (elim (Bset [ y ]) (f y) (feqr y) z)))
--                                                                  (λ z → feql x y z r))

--(Path (_P_206 [ y ])
--       (transport (λ i → _P_206 (eq/ x y r i))
--        (elim (Bset [ x ]) (f x) (feqr x) z))
--       (elim (Bset [ y ]) (f y) (feqr y) z))

--λ x y r → funExt (elimProp (λ z → isProp→isPropPathP (λ i → {!!}) (g x z) (g y z))
--                                                                  (λ z → feql x y z r))
--  isOfHLevel→isOfHLevelDep 2 Bset
--              (g x) (g y) (cong g p) (cong g q) (squash/ x y p q) i j
--    where
--      g = λ x z → elim (Bset [ x ]) (f x) (feqr x) z

--funExt (λ z → elim2Help z (λ x → {!!} --Bset x z {!!} {!!}
--                                            ) (eq/ x y r)
--                                            (elim (λ y₁ → Bset [ x ] y₁) (λ y₁ → f x y₁) (λ y₁ z₁ r₁ → feqr x y₁ z₁ r₁) z)
--                                            (elim (λ y₁ → Bset [ y ] y₁) (λ y₁ → f y y₁) (λ y₁ z₁ r₁ → feqr y y₁ z₁ r₁) z))

--       (λ y₁ z₁ r₁ → feqr y y₁ z₁ r₁) z)
--                              λ x y r → funExt (λ z → isProp→PathP (λ i → {!!} )
--                                (elim (λ y₁ → Bset [ x ] y₁) (λ y₁ → f x y₁) (λ y₁ z₁ r₁ → feqr x y₁ z₁ r₁) z)
--                                (elim (λ y₁ → Bset [ y ] y₁) (λ y₁ → f y y₁) (λ y₁ z₁ r₁ → feqr y y₁ z₁ r₁) z))

SetPathPl : {ℓ ℓ' ℓ'' ℓ''' : Level} → {A : Type ℓ} → {C : Type ℓ'} {D : Type ℓ''} → {B : A → C → D →  Type ℓ'''} →
            ((x : A) → (y : C) → (z : D) → isSet (B x y z)) → 
            {a0 a1 : A} → (p : a0 ≡ a1) →
            (z : C) → (w : D) → (u0 : B a0 z w) → (u1 : B a1 z w) →
            isSet (PathP (λ i → B (p i) z w) u0 u1)
SetPathPl {B = B} Bset {a1 = a1} p z w u0 u1 =
  transport (cong isSet (sym (funDepTr3l {B = B} p z w u0 u1)))
    (isSet→isGroupoid (Bset a1 z w) (transport (λ i → B (p i) z w) u0) u1)

SetPathPm : {ℓ ℓ' ℓ'' ℓ''' : Level} → {A : Type ℓ} → {C : Type ℓ'} {D : Type ℓ''} → {B : A → C → D →  Type ℓ'''} →
            ((x : A) → (y : C) → (z : D) → isSet (B x y z)) → 
            {c0 c1 : C} → (p : c0 ≡ c1) →
            (z : A) → (w : D) → (u0 : B z c0 w) → (u1 : B z c1 w) →
            isSet (PathP (λ i → B z (p i) w) u0 u1)
SetPathPm {B = B} Bset {c1 = c1} p z w u0 u1 =
  transport (cong isSet (sym (funDepTr3m {B = B} p z w u0 u1)))
    (isSet→isGroupoid (Bset z c1 w) (transport (λ i → B z (p i) w) u0) u1)

SetPathPr : {ℓ ℓ' ℓ'' ℓ''' : Level} → {A : Type ℓ} → {C : Type ℓ'} {D : Type ℓ''} → {B : A → C → D →  Type ℓ'''} →
            ((x : A) → (y : C) → (z : D) → isSet (B x y z)) → 
            {d0 d1 : D} → (p : d0 ≡ d1) →
            (z : A) → (w : C) → (u0 : B z w d0) → (u1 : B z w d1) →
            isSet (PathP (λ i → B z w (p i)) u0 u1)
SetPathPr {B = B} Bset {d1 = d1} p z w u0 u1 =
  transport (cong isSet (sym (funDepTr3r {B = B} p z w u0 u1)))
    (isSet→isGroupoid (Bset z w d1) (transport (λ i → B z w (p i)) u0) u1)

PathPSetl : {ℓ1 ℓ2 ℓ3 ℓ4 : Level} → {A : Type ℓ1} → {C : Type ℓ2} → {D : Type ℓ3} → {B : A → C → D → Type ℓ4} → 
            {B1 B2 : (x : A) → (y : C) → (z : D) → B x y z} →
            ((x : A) → (y : C) → (z : D) → isSet (B x y z)) →
            {a0 a1 : A} → (p : a0 ≡ a1) →
            (z : C) → (w : D) →
            (q : B1 a0 z w ≡ B2 a0 z w) → (r : B1 a1 z w ≡ B2 a1 z w) →
            PathP (λ i → (B1 (p i) z w) ≡ (B2 (p i) z w)) q r
PathPSetl {B1 = B1} {B2 = B2} Bset {a1 = a1} p z w q r =
  transport (sym (funDepTr3l {B = λ x y z → B1 x y z ≡ B2 x y z} p z w q r))
    (Bset a1 z w _ _ (transport (λ i → (B1 (p i) z w) ≡ (B2 (p i) z w)) q) r)
