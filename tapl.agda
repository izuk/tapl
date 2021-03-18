module tapl where

open import Data.Nat using (ℕ; _≟_; _<?_; _+_; suc; zero)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

Id : Set
Id = ℕ

infixr 7 _=>_

data Type : Set where
  _=>_ : Type → Type → Type
  Unit : Type

infix  5 ƛ_⊸_
infix 7 _∙_
infix  9 #_

data Term : Set where
  #_ : Id → Term
  ƛ_⊸_ :  Type → Term → Term
  _∙_ :  Term → Term → Term
  unit : Term

data Value : Term → Set where
  V-ƛ : ∀ {A t} → Value (ƛ A ⊸ t)
  V-unit : Value unit

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
    fn _ t = t

_[_:=_] : Term → Id → Term → Term
(# x) [ y := v ] with x ≟ y
... | yes _ = v
... | no _ = # x
(ƛ A ⊸ t) [ y := v ] = ƛ A ⊸ t [ 1 := shift suc v ]
(L ∙ M) [ y := v ] = L [ y := v ] ∙ M [ y := v ]
t [ _ := _ ] = t

infix 4 _~>_

dec : ℕ → ℕ
-- TODO: Find a way to remove the zero case.
dec zero = zero
dec (suc x) = x

data _~>_ : Term → Term → Set where
  ξ-∙₁ : ∀ {t₁ t₂ t} → t₁ ~> t₂ → t₁ ∙ t ~> t₂ ∙ t
  ξ-∙₂ : ∀ {t t₁ t₂} → t₁ ~> t₂ → t ∙ t₁ ~> t ∙ t₂
  β-ƛ : ∀ {A t₁ t} → Value t → (ƛ A ⊸ t₁) ∙ t ~> shift dec (t₁ [ 0 := shift suc t ])

module Evaluation-Tests where

  id : Term
  id = ƛ Unit ⊸ # 0

  const : Term
  const = ƛ Unit ⊸ unit

  test-0 : (id ∙ unit) ~> unit
  test-0 = β-ƛ V-unit

  test-1 : (const ∙ unit) ~> unit
  test-1 = β-ƛ V-unit

  app : Term
  app = ƛ (Unit => Unit) ⊸ (# 0) ∙ unit

  test-2 : (app ∙ id) ~> id ∙ unit
  test-2 = β-ƛ V-ƛ

  test-3 : const ∙ (id ∙ unit) ~> const ∙ unit
  test-3 = ξ-∙₂ test-0

infixl 5  _,_

data Context : Set where
  Z : Context
  _,_ : Context → Type → Context

infix  4  _∋_∷_

data _∋_∷_ : Context → Id → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ 0 ∷ A
  S : ∀ {Γ x A B} → Γ ∋ x ∷ A → Γ , B ∋ suc x ∷ A

infix  4  _⊢_∷_

data _⊢_∷_ : Context → Term → Type → Set where
  ⊢# : ∀ {Γ x A} → Γ ∋ x ∷ A → Γ ⊢ # x ∷ A
  ⊢ƛ : ∀ {Γ t A B} → Γ , A ⊢ t ∷ B → Γ ⊢ (ƛ A ⊸ t) ∷ A => B
  _∙_ : ∀ {Γ t₁ t₂ A B} → Γ ⊢ t₁ ∷ A => B → Γ ⊢ t₂ ∷ A → Γ ⊢ t₁ ∙ t₂ ∷ B
  ⊢unit : ∀ {Γ} → Γ ⊢ unit ∷ Unit

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
progress ⊢unit = done V-unit

