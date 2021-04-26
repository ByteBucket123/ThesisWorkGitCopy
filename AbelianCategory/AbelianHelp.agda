
{-# OPTIONS --cubical #-}

module ThesisWork.AbelianCategory.AbelianHelp where

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
  AbMonicsAreKernels : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  AbMonicsAreKernels C abel = {A S : ob (cat C)} → (k : hom (cat C) S A) → isMonic C k →
                              Σ (ob (cat C))
                                (λ B → Σ (hom (cat C) A B)
                                         (λ f → isKernel' C (Abelian.AbHasZero abel) f k))

IsMonicAndEpicToIso : {ℓ ℓ' : Level} → (C : UnivalentCategory ℓ ℓ') → (abel : Abelian C) → AbMonicsAreKernels C abel →
              {A B : ob (cat C)} → (k : hom (cat C) A B) → isMonic C k → isEpic C k → CatIso {C = cat C} A B
IsMonicAndEpicToIso C abel mon→isKer {A} {B} k monK epicK =
  catiso k h' h'k=id kh'=id
    where
      S = fst (mon→isKer k monK)
      f = fst (snd (mon→isKer k monK))
      0a : (a b : ob (cat C)) → hom (cat C) a b
      0a a b = ZeroArrow.f (getZeroArrow C {a} {b} (Abelian.AbHasZero abel))

      f=0 : f ≡ 0a B S
      f=0 = epicK S f (0a B S) (((cat C) , k ∘ f)        ≡⟨ isKernel'.kerComp (snd (snd (mon→isKer k monK))) ⟩
                               0a A S                    ≡⟨ sym (ZeroArrowCompLeft C (Abelian.AbHasZero abel) k) ⟩
                               ((cat C) , k ∘ 0a B S) ∎)

      idf=0 = ((cat C) , (id (cat C) B) ∘ f) ≡⟨ idl (cat C) f ⟩
              f                              ≡⟨ f=0 ⟩
              0a B S ∎

      isKernelId : isKernel' C (Abelian.AbHasZero abel) f (id (cat C) B)
      isKernelId = isKernel'Const (idf=0)
                                  (λ {E} h hf=0 → h , (idr (cat C) h))
                                  λ D h g hid=gid → h                              ≡⟨ sym (idr (cat C) h) ⟩
                                                    ((cat C) , h ∘ (id (cat C) B)) ≡⟨ hid=gid ⟩
                                                    ((cat C) , g ∘ (id (cat C) B)) ≡⟨ idr (cat C) g ⟩
                                                    g ∎

      h' = fst (isKernel'.kerFactors (snd (snd (mon→isKer k monK))) (id (cat C) B) idf=0)
      h'k=id = snd (isKernel'.kerFactors (snd (snd (mon→isKer k monK))) (id (cat C) B) idf=0)
      kh'=id : (cat C) , k ∘ h' ≡ id (cat C) A
      kh'=id = monK A ((cat C) , k ∘ h')
                      (id (cat C) A)
                      (((cat C) , ((cat C) , k ∘ h') ∘ k) ≡⟨ catAsso (cat C) k h' k ⟩
                      ((cat C) , k ∘ ((cat C) , h' ∘ k))  ≡⟨ cong (λ w → (cat C) , k ∘ w) h'k=id ⟩
                      ((cat C) , k ∘ id (cat C) B)        ≡⟨ idr (cat C) k ⟩
                      k                                   ≡⟨ sym (idl (cat C) k) ⟩
                      ((cat C) , (id (cat C) A) ∘ k) ∎)

