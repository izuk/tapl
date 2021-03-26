module Language.Unit where

open import Data.Nat using (ℕ; _≟_; _<?_; suc; pred; zero; compare; less; equal; greater)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

infixr 7 _=>_

data Type : Set where
  _=>_ : Type → Type → Type
  Unit : Type

infix 9 #_
infix 5 ƛ_⊸_
infix 7 _∙_

data Term : Set where
  #_ : ℕ → Term
  ƛ_⊸_ :  Type → Term → Term
  _∙_ :  Term → Term → Term
  unit : Term

data Value : Term → Set where
  V-ƛ : ∀ {A t} → Value (ƛ A ⊸ t)
  V-unit : Value unit

infix 4 _~>_

-- depth
-- # x | x == depth -> v
--     | x < depth = x
--     | x > depth = x - 1

infix 5 _[_:=_]

_[_:=_] : Term → ℕ → Term → Term
(# x) [ k := t ] with compare k x
... | less _ _ = # (pred x)
... | equal _ = t
... | greater _ _ = # x
(ƛ A ⊸ t₁) [ k := t ] = ƛ A ⊸ (t₁ [ suc k := t ])
(L ∙ M) [ k := t ] = (L [ k := t ]) ∙ (M [ k := t ])
t [ _ := _ ] = t

data _~>_ : Term → Term → Set where
  E-App₁ : ∀ {t₁ t₂ t} → t₁ ~> t₂ → t₁ ∙ t ~> t₂ ∙ t
  E-App₂ : ∀ {t t₁ t₂} → Value t → t₁ ~> t₂ → t ∙ t₁ ~> t ∙ t₂
  E-AppAbs : ∀ {A t₁ t₂} → Value t₂ → (ƛ A ⊸ t₁) ∙ t₂ ~> t₁ [ 0 := t₂ ]

import Normalization
open module Normalization-Unit = Normalization Term Value _~>_

import Context
open module Context-Unit = Context Type using (Context; Ø; _,_; _∋_∷_; Z; S)

infix  4  _⊢_∷_

data _⊢_∷_ : Context → Term → Type → Set where
  ⊢# : ∀ {Γ x A} → Γ ∋ x ∷ A → Γ ⊢ # x ∷ A
  ⊢ƛ : ∀ {Γ t B} → (A : Type) → Γ , A ⊢ t ∷ B → Γ ⊢ (ƛ A ⊸ t) ∷ A => B
  _∙_ : ∀ {Γ t₁ t₂ A B} → Γ ⊢ t₁ ∷ A => B → Γ ⊢ t₂ ∷ A → Γ ⊢ t₁ ∙ t₂ ∷ B
  ⊢unit : ∀ {Γ} → Γ ⊢ unit ∷ Unit

progress : ∀ {t A} → Ø ⊢ t ∷ A → Progress t
progress (⊢ƛ _ _) = done V-ƛ 
progress (⊢L ∙ ⊢R) with progress ⊢L
... | step x₁ = step (E-App₁ x₁)
... | done V-ƛ with progress ⊢R
...   | step x₂ = step (E-App₂ V-ƛ x₂)
...   | done v₂ = step (E-AppAbs v₂)
progress ⊢unit = done V-unit

-- Given:
-- Γ ⊢ t₁ ∷ A₁
-- Γ , A₁ , A ⊢ t ∷ B

-- Prove:
-- Γ , A ⊢ t [ 1 := t₁ ] ∷ B

ext : ∀ {Γ Δ}
  → (∀ {A k l} → Γ ∋ k ∷ A → Δ ∋ l ∷ A)
  → (∀ {A B k l} → Γ , B ∋ k ∷ A → Δ , B ∋ l ∷ A)
ext ρ Z = {!!} 
ext ρ (S x) = {!!}

lemma : ∀ {Γ t t₁ A A₁ B} → Γ ⊢ t₁ ∷ A₁ → Γ , A₁ , A ⊢ t ∷ B → Γ , A ⊢ t [ 1 := t₁ ] ∷ B
lemma T₁ (⊢# x) = {!!}
lemma T₁ (⊢ƛ A T) = {!!}
lemma T₁ (T₂₁ ∙ T₂₂) = lemma T₁ T₂₁ ∙ lemma T₁ T₂₂
lemma T₁ ⊢unit = ⊢unit

subst-lemma : ∀ {Γ t₁ t A₁ A} → Γ ⊢ t₁ ∷ A₁ → Γ , A₁ ⊢ t ∷ A → Γ ⊢ t [ 0 := t₁ ] ∷ A
subst-lemma T₁ (⊢# Z) = T₁
subst-lemma T₁ (⊢# (S x)) = ⊢# x
subst-lemma T₁ (⊢ƛ A Tƛ) = ⊢ƛ A (lemma T₁ Tƛ)
subst-lemma T₁ (T₂₁ ∙ T₂₂) = subst-lemma T₁ T₂₁ ∙ subst-lemma T₁ T₂₂
subst-lemma T₁ ⊢unit = ⊢unit

preservation : ∀{t₁ t₂ Γ A} → Γ ⊢ t₁ ∷ A → t₁ ~> t₂ → Γ ⊢ t₂ ∷ A
preservation (T₁₁ ∙ T₁₂) (E-App₁ p) = preservation T₁₁ p ∙ T₁₂
preservation (T₁₁ ∙ T₁₂) (E-App₂ _ p) = T₁₁ ∙ preservation T₁₂ p
preservation (⊢ƛ _ T₁₁ ∙ T₂) (E-AppAbs _) = subst-lemma T₂ T₁₁

module Tests where

  id : Term
  id = ƛ Unit ⊸ # 0

  const : Term
  const = ƛ Unit ⊸ unit

  test-0 : (id ∙ unit) ~> unit
  test-0 = E-AppAbs V-unit

  test-1 : (const ∙ unit) ~> unit
  test-1 = E-AppAbs V-unit

  app : Term
  app = ƛ (Unit => Unit) ⊸ # 0 ∙ unit

  test-2 : (app ∙ id) ~~> unit
  test-2 =
    begin
      app ∙ id
    ~>⟨ E-AppAbs V-ƛ ⟩
      id ∙ unit
    ~>⟨ E-AppAbs V-unit ⟩
      unit
    ∎

  test-3 : const ∙ (id ∙ unit) ~~> unit
  test-3 =
    begin
      const ∙ (id ∙ unit)
    ~>⟨ E-App₂ V-ƛ test-0 ⟩
      const ∙ unit
    ~>⟨ test-1 ⟩
      unit
    ∎

  two : Term
  two = ƛ (Unit => Unit) ⊸ (ƛ Unit ⊸ # 1 ∙ (# 1 ∙ # 0))

  test-two : (two ∙ id) ∙ unit ~~> unit
  test-two =
    begin
      (two ∙ id) ∙ unit
    ~>⟨ E-App₁ (E-AppAbs V-ƛ) ⟩
      (ƛ Unit ⊸ id ∙ (id ∙ # 0)) ∙ unit
    ~>⟨ E-AppAbs V-unit ⟩
      id ∙ (id ∙ unit)
    ~>⟨ E-App₂ V-ƛ (E-AppAbs V-unit) ⟩
      id ∙ unit
    ~>⟨ E-AppAbs V-unit ⟩
      unit
    ∎
  
  test-unit : Ø ⊢ unit ∷ Unit
  test-unit = ⊢unit

  test-id : Ø ⊢ ƛ Unit ⊸ # 0 ∷ Unit => Unit
  test-id = ⊢ƛ Unit (⊢# Z)

  test-app : Ø ⊢ (ƛ Unit ⊸ # 0) ∙ unit ∷ Unit
  test-app = test-id ∙ test-unit
