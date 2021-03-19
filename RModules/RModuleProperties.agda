{-# OPTIONS --cubical #-}

module ThesisWork.RModules.RModuleProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Foundations.SIP

--************************************************* Should be moved ************************************************

groupInvDist : {ℓ : Level} → {G : Group {ℓ}} → (a b : ⟨ G ⟩) →
               (GroupStr.- snd G) (((snd G) GroupStr.+ a) b) ≡
               ((snd G) GroupStr.+ ((GroupStr.- (snd G)) b)) ((GroupStr.- (snd G)) a)
groupInvDist {ℓ} {G} a b =
  (- (a + b))                                 ≡⟨ sym (x+0g≡x (- (a + b))) ⟩
  ((- (a + b)) + 0g)                          ≡⟨ cong (λ x → (- (a + b)) + x) (sym (x+-x≡0g a)) ⟩
  ((- (a + b)) + (a + (- a)))                 ≡⟨ cong (λ x → (- (a + b)) + (x + (- a))) (sym (x+0g≡x a)) ⟩
  ((- (a + b)) + ((a + 0g) + (- a)))          ≡⟨ cong (λ x → (- (a + b)) +  ((a + x) + (- a))) (sym (x+-x≡0g b)) ⟩
  ((- (a + b)) + ((a + (b + (- b))) + (- a))) ≡⟨ Asso (- (a + b)) ((a + (b + (- b)))) (- a) ⟩
  (((- (a + b)) + (a + (b + (- b)))) + (- a)) ≡⟨ cong (λ x → ((- (a + b)) + x) + (- a)) (Asso a b (- b)) ⟩
  (((- (a + b)) + ((a + b) + (- b))) + (- a)) ≡⟨ cong (λ x → x + (- a)) (Asso (- (a + b)) ((a + b)) (- b)) ⟩
  ((((- (a + b)) + (a + b)) + (- b)) + (- a)) ≡⟨ cong (λ x → (x + (- b)) + (- a)) (-x+x≡0g (a + b)) ⟩
  ((0g + (- b)) + (- a))                      ≡⟨ cong (λ x → x + (- a)) (0g+x≡x (- b)) ⟩
  ((- b) + (- a)) ∎
    where
      _+_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
      a + b = (snd G GroupStr.+ a) b
      -_ : ⟨ G ⟩ → ⟨ G ⟩
      - a = (GroupStr.- snd G) a
      0g = GroupStr.0g (snd G)
      x+0g≡x : (x : ⟨ G ⟩) → x + 0g ≡ x
      x+0g≡x x = fst (IsMonoid.identity (IsGroup.isMonoid (GroupStr.isGroup (snd G))) x)
      0g+x≡x : (x : ⟨ G ⟩) → 0g + x ≡ x
      0g+x≡x x = snd (IsMonoid.identity (IsGroup.isMonoid (GroupStr.isGroup (snd G))) x)
      x+-x≡0g : (x : ⟨ G ⟩) → x + (- x) ≡ 0g
      x+-x≡0g x = fst (IsGroup.inverse (GroupStr.isGroup (snd G)) x)
      -x+x≡0g : (x : ⟨ G ⟩) → (- x) + x ≡ 0g
      -x+x≡0g x = snd (IsGroup.inverse (GroupStr.isGroup (snd G)) x)
      Asso : (a b c : ⟨ G ⟩) → a + (b + c) ≡ (a + b) + c
      Asso = IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd G))))

AbgroupInvDist : {ℓ : Level} → {G : AbGroup {ℓ}} → (a b : ⟨ G ⟩) →
               (AbGroupStr.- snd G) (((snd G) AbGroupStr.+ a) b) ≡
               ((snd G) AbGroupStr.+ ((AbGroupStr.- (snd G)) a)) ((AbGroupStr.- (snd G)) b)
AbgroupInvDist {ℓ} {G} a b =
  (- (a + b))     ≡⟨ groupInvDist {G = AbGroup→Group G} a b ⟩
  ((- b) + (- a)) ≡⟨ com (- b) (- a) ⟩
  ((- a) + (- b)) ∎
    where
      _+_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
      a + b = (snd G AbGroupStr.+ a) b
      -_ : ⟨ G ⟩ → ⟨ G ⟩
      - a = (AbGroupStr.- snd G) a
      0g = AbGroupStr.0g (snd G)
      com : (a b : ⟨ G ⟩) → a + b ≡ b + a
      com = IsAbGroup.comm (AbGroupStr.isAbGroup (snd G))
