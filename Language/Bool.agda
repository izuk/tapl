module Language.Bool where

open import Data.Nat using (ℕ; _≟_; _<?_; suc; zero)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

infixr 7 _=>_

data Type : Set where
  _=>_ : Type → Type → Type
  Unit : Type
  Bool : Type

infix 9 #_
infix 5 ƛ_⊸_
infix 7 _∙_
infix 6 if_then_else_

data Term : Set where
  #_ : ℕ → Term
  ƛ_⊸_ :  Type → Term → Term
  _∙_ :  Term → Term → Term
  if_then_else_ : Term → Term → Term → Term
  unit : Term
  true : Term
  false : Term

data Value : Term → Set where
  V-ƛ : ∀ {A t} → Value (ƛ A ⊸ t)
  V-unit : Value unit
  V-true : Value true
  V-false : Value false

infix 9 _[_:=_]

shift : (ℕ → ℕ) → Term → Term
shift c = fn 0
  where
    fn : (k : ℕ) → Term → Term
    fn k (# x) with x <? k
    ... | yes _ = # x
    ... | no _ = # (c x)
    fn k (ƛ A ⊸ t) = ƛ A ⊸ fn (suc k) t
    fn k (t₁ ∙ t₂) = (fn k t₁) ∙ (fn k t₂)
    fn k (if t then t₁ else t₂) = if (fn k t) then (fn k t₁) else (fn k t₂)
    fn _ t = t

_[_:=_] : Term → ℕ → Term → Term
(# x) [ y := v ] with x ≟ y
... | yes _ = v
... | no _ = # x
(ƛ A ⊸ t) [ y := v ] = ƛ A ⊸ t [ 1 := shift suc v ]
(L ∙ M) [ y := v ] = L [ y := v ] ∙ M [ y := v ]
(if t then t₁ else t₂) [ y := v ] = if (t [ y := v ]) then (t₁ [ y := v ]) else (t₂ [ y := v ])
t [ _ := _ ] = t

infix 4 _~>_

dec : ℕ → ℕ
-- TODO: Find a way to remove the zero case.
dec zero = zero
dec (suc x) = x

data _~>_ : Term → Term → Set where
  ξ-∙₁ : ∀ {t₁ t₂ t} → t₁ ~> t₂ → t₁ ∙ t ~> t₂ ∙ t
  ξ-∙₂ : ∀ {t t₁ t₂} → t₁ ~> t₂ → t ∙ t₁ ~> t ∙ t₂
  ξ-ite : ∀ {t t' t₁ t₂} → t ~> t' → if t then t₁ else t₂ ~> if t' then t₁ else t₂
  β-ƛ : ∀ {A t₁ t} → Value t → (ƛ A ⊸ t₁) ∙ t ~> shift dec (t₁ [ 0 := shift suc t ])
  β-true : ∀ {t₁ t₂} → if true then t₁ else t₂ ~> t₁
  β-false : ∀ {t₁ t₂} → if false then t₁ else t₂ ~> t₂

import Normalization
open module Normalization-Bool = Eval Term _~>_

module Tests where

  id : Term
  id = ƛ Unit ⊸ # 0

  const : Term
  const = ƛ Unit ⊸ unit

  test-0 : (id ∙ unit) ~> unit
  test-0 = β-ƛ V-unit

  test-1 : (const ∙ unit) ~> unit
  test-1 = β-ƛ V-unit

  app : Term
  app = ƛ (Unit => Unit) ⊸ # 0 ∙ unit

  test-2 : (app ∙ id) ~~> unit
  test-2 =
    begin
      app ∙ id
    ~>⟨ β-ƛ V-ƛ ⟩
      id ∙ unit
    ~>⟨ β-ƛ V-unit ⟩
      unit
    ∎

  test-3 : const ∙ (id ∙ unit) ~~> unit
  test-3 =
    begin
      const ∙ (id ∙ unit)
    ~>⟨ ξ-∙₂ test-0 ⟩
      const ∙ unit
    ~>⟨ test-1 ⟩
      unit
    ∎

  not : Term
  not = ƛ Bool ⊸ if # 0 then false else true

  test-4 : not ∙ true ~~> false
  test-4 =
    begin
      not ∙ true
    ~>⟨ β-ƛ V-true ⟩
      if true then false else true
    ~>⟨ β-true ⟩
      false
    ∎

import Context
open module Context-Bool = Context Type

infix  4  _⊢_∷_

data _⊢_∷_ : Context → Term → Type → Set where
  ⊢# : ∀ {Γ x A} → Γ ∋ x ∷ A → Γ ⊢ # x ∷ A
  ⊢ƛ : ∀ {Γ t A B} → Γ , A ⊢ t ∷ B → Γ ⊢ (ƛ A ⊸ t) ∷ A => B
  _∙_ : ∀ {Γ t₁ t₂ A B} → Γ ⊢ t₁ ∷ A => B → Γ ⊢ t₂ ∷ A → Γ ⊢ t₁ ∙ t₂ ∷ B
  if_then_else_ : ∀ {Γ t t₁ t₂ A} → Γ ⊢ t ∷ Bool → Γ ⊢ t₁ ∷ A → Γ ⊢ t₂ ∷ A → Γ ⊢ if t then t₁ else t₂ ∷ A
  ⊢unit : ∀ {Γ} → Γ ⊢ unit ∷ Unit
  ⊢true : ∀ {Γ} → Γ ⊢ true ∷ Bool
  ⊢false : ∀ {Γ} → Γ ⊢ false ∷ Bool

module Typing-Tests where

  test-0 : Z ⊢ unit ∷ Unit
  test-0 = ⊢unit

  test-1 : Z ⊢ ƛ Unit ⊸ # 0 ∷ Unit => Unit
  test-1 = ⊢ƛ (⊢# Z)

  test-2 : Z ⊢ (ƛ Unit ⊸ # 0) ∙ unit ∷ Unit
  test-2 = test-1 ∙ test-0

data Progress (t : Term) : Set where
  step : ∀{t₁} → t ~> t₁ → Progress t
  done : Value t → Progress t

progress : ∀{t A} → Z ⊢ t ∷ A → Progress t
progress (⊢ƛ _) = done V-ƛ 
progress (⊢L ∙ ⊢R) with progress ⊢L
... | step x₁ = step (ξ-∙₁ x₁)
... | done V-ƛ with progress ⊢R  -- Only lambda values match the type.
...   | step x₂ = step (ξ-∙₂ x₂)
...   | done v₂ = step (β-ƛ v₂)
progress (if ⊢B then ⊢T else ⊢E) with progress ⊢B
... | step x = step (ξ-ite x)
... | done V-true = step β-true
... | done V-false = step β-false
progress ⊢unit = done V-unit
progress ⊢true = done V-true
progress ⊢false = done V-false

{-
preservation : ∀{t₁ t₂ Γ A} → Γ ⊢ t₁ ∷ A → t₁ ~> t₂ → Γ ⊢ t₂ ∷ A
preservation (t₁₁ ∙ t₁₂) (ξ-∙₁ p) = preservation t₁₁ p ∙ t₁₂
preservation (t₁₁ ∙ t₁₂) (ξ-∙₂ p) = t₁₁ ∙ preservation t₁₂ p
preservation (⊢ƛ t₁₁ ∙ ⊢ƛ t₁₂) (β-ƛ _) = {!!}
preservation (⊢ƛ t₁₁ ∙ ⊢unit) (β-ƛ _) = {!!}
-}
