module Language.Ref where

open import Data.Nat using (ℕ; suc; pred; zero; compare; less; equal; greater)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

infixr 7 _=>_

data Type : Set where
  _=>_ : Type → Type → Type
  Unit : Type
  Bool : Type
  Ref : Type → Type

infix 9 #_
infix 9 ‼_
infix 5 ƛ_⊸_
infix 7 _∙_
infix 6 if_then_else_
infix 8 !_
infix 7 _:=_

data Term : Set where
  #_ : ℕ → Term
  ƛ_⊸_ :  Type → Term → Term
  _∙_ :  Term → Term → Term
  if_then_else_ : Term → Term → Term → Term
  unit : Term
  true : Term
  false : Term
  ref : Term → Term
  ‼_ : ℕ → Term
  !_ : Term → Term
  _:=_ : Term → Term → Term

data Value : Term → Set where
  V-ƛ : ∀ {A t} → Value (ƛ A ⊸ t)
  V-unit : Value unit
  V-true : Value true
  V-false : Value false
  V-‼ : ∀ {l} → Value (‼ l)

subst : Term → Term → Term
subst v = fn 0
  where
    fn : ℕ → Term → Term
    fn k (# x) with compare k x
    ... | less _ _ = # (pred x)
    ... | equal _ = v
    ... | greater _ _ = # x
    fn k (ƛ A ⊸ t) = ƛ A ⊸ (fn (suc k) t)
    fn k (L ∙ M) = (fn k L) ∙ (fn k M)
    fn k (if t then t₁ else t₂) = if (fn k t) then (fn k t₁) else (fn k t₂)
    fn k (ref t) = ref (fn k t)
    fn k (! t) = ! (fn k t)
    fn k (t := t₁) = (fn k t) := (fn k t₁)
    fn _ t = t

infix 3 ⟨_,_⟩

record Store : Set where
  constructor ⟨_,_⟩
  field
    free : ℕ
    set : ℕ → Term

infix 4 _||_

record State : Set where
  constructor _||_
  field
    term : Term
    μ : Store

ε : Store
ε = ⟨ zero , (λ{ _ → unit }) ⟩

infix 2 _~>_

alloc : Store → Term → State
alloc ⟨ l , f ⟩ t = ⟨ suc l , f' ⟩ || ‼ l
  where
    f' : ℕ → Term
    f' l' with l Data.Nat.≟ l'
    ... | yes _ = t
    ... | no _ = f l'

lookup : Store → ℕ → Term
lookup ⟨ _ , f ⟩ l = f l

update : Store → ℕ → Term → Store
update ⟨ l , f ⟩ l₁ t = ⟨ l , f' ⟩
  where
    f' : ℕ → Term
    f' l' with l₁ Data.Nat.≟ l'
    ... | yes _ = t
    ... | no _ = f l'

data _~>_ : State → State → Set where
  ξ-∙₁ : ∀ {σ₁ σ₂ t₁ t₂ t} → σ₁ || t₁ ~> ⟨ σ₂ , t₂ ⟩ → ⟨ σ₁ , t₁ ∙ t ⟩ ~> ⟨ σ₂ , t₂ ∙ t ⟩
  ξ-∙₂ : ∀ {σ₁ σ₂ t t₁ t₂} → ⟨ σ₁ , t₁ ⟩ ~> ⟨ σ₂ , t₂ ⟩ → ⟨ σ₁ , t ∙ t₁ ⟩ ~> ⟨ σ₂ , t ∙ t₂ ⟩
  ξ-ite : ∀ {σ σ' t t' t₁ t₂} → ⟨ σ , t ⟩ ~> ⟨ σ' , t' ⟩ → ⟨ σ , if t then t₁ else t₂ ⟩ ~> ⟨ σ' , if t' then t₁ else t₂ ⟩
  β-ƛ : ∀ {σ A t₁ t} → Value t → ⟨ σ , (ƛ A ⊸ t₁) ∙ t ⟩ ~> ⟨ σ , subst t t₁ ⟩
  β-true : ∀ {σ t₁ t₂} → ⟨ σ , if true then t₁ else t₂ ⟩ ~> ⟨ σ , t₁ ⟩
  β-false : ∀ {σ t₁ t₂} → ⟨ σ , if false then t₁ else t₂ ⟩ ~> ⟨ σ , t₂ ⟩
  ξ-ref : ∀ {σ₁ σ₂ t₁ t₂} → ⟨ σ₁ , t₁ ⟩ ~> ⟨ σ₂ , t₂ ⟩ → ⟨ σ₁ , ref t₁ ⟩ ~> ⟨ σ₂ , ref t₂ ⟩
  β-ref : ∀ {σ t} → Value t → ⟨ σ , ref t ⟩ ~> alloc σ t
  ξ-lookup : ∀ {σ₁ σ₂ t₁ t₂} → ⟨ σ₁ , t₁ ⟩ ~> ⟨ σ₂ , t₂ ⟩ → ⟨ σ₁ , ! t₁ ⟩ ~> ⟨ σ₂ , ! t₂ ⟩
  β-lookup : ∀ {σ l} → ⟨ σ , ! (‼ l) ⟩ ~> ⟨ σ , lookup σ l ⟩
  ξ-update₁ : ∀ {σ₁ σ₂ t₁₁ t₁₂ t₂} → ⟨ σ₁ , t₁₁ ⟩ ~> ⟨ σ₁ , t₁₂ ⟩ → ⟨ σ₂ , t₁₁ := t₂ ⟩ ~> ⟨ σ₂ , t₁₂ := t₂ ⟩
  ξ-update₂ : ∀ {σ₁ σ₂ t₁ t₂₁ t₂₂} → ⟨ σ₁ , t₂₁ ⟩ ~> ⟨ σ₂ , t₂₂ ⟩ → ⟨ σ₁ , t₁ := t₂₁ ⟩ ~> ⟨ σ₂ , t₁ := t₂₂ ⟩
  β-update : ∀ {σ l t} → ⟨ σ , ‼ l := t ⟩ ~> ⟨ update σ l t , unit ⟩

{--
data _~>_ : (Store × Term) → (Store × Term) → Set where
  ξ-∙₁ : ∀ {t₁ t₂ t} → t₁ ~> t₂ → t₁ ∙ t ~> t₂ ∙ t
  ξ-∙₂ : ∀ {t t₁ t₂} → t₁ ~> t₂ → t ∙ t₁ ~> t ∙ t₂
  ξ-ite : ∀ {t t' t₁ t₂} → t ~> t' → if t then t₁ else t₂ ~> if t' then t₁ else t₂
  β-ƛ : ∀ {A t₁ t} → Value t → (ƛ A ⊸ t₁) ∙ t ~> subst t t₁
  β-true : ∀ {t₁ t₂} → if true then t₁ else t₂ ~> t₁
  β-false : ∀ {t₁ t₂} → if false then t₁ else t₂ ~> t₂
  ξ-ref : ∀ {t₁ t₂} → t₁ ~> t₂ → ref t₁ ~> ref t₂
  β-ref : ∀ {t} → ref t ~> ‼ 0
  ξ-lookup : ∀ {t₁ t₂} → t₁ ~> t₂ → ! t₁ ~> ! t₂
  β-lookup : ∀ {l : ℕ} → ! (‼ l) ~> unit
  ξ-update₁ : ∀ {t₁₁ t₁₂ t₂} → t₁₁ ~> t₁₂ → t₁₁ := t₂ ~> t₁₂ := t₂
  ξ-update₂ : ∀ {t₁ t₂₁ t₂₂} → t₂₁ ~> t₂₂ → t₁ := t₂₁ ~> t₁ := t₂₂
  β-update : ∀ {t₁ t₂} → t₁ := t₂ ~> unit
--}

open import Function using (_∘_)

import Normalization
open module Normalization-Unit = Normalization State (Value ∘ proj₂) _~>_

import Context
open module Context-Bool = Context Type

infix  4  _⊢_∷_

data _⊢_∷_ : Context → Term → Type → Set where
  ⊢# : ∀ {Γ x A} → Γ ∋ x ∷ A → Γ ⊢ # x ∷ A
  ⊢ƛ : ∀ {Γ t A B} → Γ , A ⊢ t ∷ B → Γ ⊢ (ƛ A ⊸ t) ∷ A => B
  _∙_ : ∀ {Γ t₁ t₂ A B} → Γ ⊢ t₁ ∷ A => B → Γ ⊢ t₂ ∷ A → Γ ⊢ t₁ ∙ t₂ ∷ B
  if_then_else_ : ∀ {Γ t t₁ t₂ A} → Γ ⊢ t ∷ Bool → Γ ⊢ t₁ ∷ A → Γ ⊢ t₂ ∷ A → Γ ⊢ if t then t₁ else t₂ ∷ A
  ⊢ref : ∀ {Γ t A} → Γ ⊢ t ∷ A → Γ ⊢ ref t ∷ Ref A
  ⊢lookup : ∀ {Γ t A } → Γ ⊢ t ∷ Ref A → Γ ⊢ ! t ∷ A
  ⊢update : ∀ {Γ t₁ t₂ A} → Γ ⊢ t₁ ∷ Ref A → Γ ⊢ t₂ ∷ A → Γ ⊢ t₁ := t₂ ∷ Unit
  ⊢unit : ∀ {Γ} → Γ ⊢ unit ∷ Unit
  ⊢true : ∀ {Γ} → Γ ⊢ true ∷ Bool
  ⊢false : ∀ {Γ} → Γ ⊢ false ∷ Bool
  
progress : ∀{t A} → Z ⊢ t ∷ A → Progress ⟨ ε , t ⟩
progress (⊢ƛ _) = done V-ƛ 
progress (⊢L ∙ ⊢R) with progress ⊢L
... | step x₁ = step (ξ-∙₁ x₁)
... | done V-ƛ with progress ⊢R
...   | step x₂ = step (ξ-∙₂ x₂)
...   | done v₂ = step (β-ƛ v₂)
progress (if ⊢B then ⊢T else ⊢E) with progress ⊢B
... | step x = step (ξ-ite x)
... | done V-true = step β-true
... | done V-false = step β-false
progress ⊢unit = done V-unit
progress ⊢true = done V-true
progress ⊢false = done V-false
progress (⊢ref x) with progress x
... | step x₁ = step (ξ-ref x₁)
... | done x₁ = step β-ref
progress (⊢lookup x) with progress x
... | step x₁ = step (ξ-lookup x₁)
... | done V-‼ = step β-lookup
progress (⊢update x x₁) with progress x
... | step x₂ = step (ξ-update₁ x₂)
... | done V-‼ with progress x₁
...   | step x₃ = step (ξ-update₂ x₃)
...   | done x₃ = step β-update

{-
preservation : ∀{t₁ t₂ Γ A} → Γ ⊢ t₁ ∷ A → t₁ ~> t₂ → Γ ⊢ t₂ ∷ A
preservation (t₁₁ ∙ t₁₂) (ξ-∙₁ p) = preservation t₁₁ p ∙ t₁₂
preservation (t₁₁ ∙ t₁₂) (ξ-∙₂ p) = t₁₁ ∙ preservation t₁₂ p
preservation (⊢ƛ t₁₁ ∙ ⊢ƛ t₁₂) (β-ƛ _) = {!!}
preservation (⊢ƛ t₁₁ ∙ ⊢unit) (β-ƛ _) = {!!}
-}

infix 4 _,,_

_,,_ : (t₁ : Term) → Term → Term
t₁ ,, t₂ = (ƛ Unit ⊸ t₂) ∙ t₁

module Tests where

  id : Term
  id = ƛ Unit ⊸ # 0

  const : Term
  const = ƛ Unit ⊸ unit

  test-0 : ⟨ ε , (id ∙ unit) ⟩ ~> ⟨ ε , unit ⟩
  test-0 = β-ƛ V-unit

  test-1 : ⟨ ε , (const ∙ unit) ⟩ ~> ⟨ ε , unit ⟩
  test-1 = β-ƛ V-unit

  app : Term
  app = ƛ (Unit => Unit) ⊸ # 0 ∙ unit

  test-2 : ⟨ ε , (app ∙ id) ⟩ ~~> ⟨ ε , unit ⟩
  test-2 =
    begin
      ⟨ ε , app ∙ id ⟩
    ~>⟨ β-ƛ V-ƛ ⟩
      ⟨ ε , id ∙ unit ⟩
    ~>⟨ β-ƛ V-unit ⟩
      ⟨ ε , unit ⟩
    ∎

  test-3 : ∀ {t} → Value t → ⟨ ε , ! (ref t) ⟩ ~~> ⟨ _ , t ⟩
  test-3 {t} v =
    begin
      ⟨ ε , ! (ref t) ⟩
    ~>⟨ ξ-lookup (β-ref v) ⟩
      ⟨ ⟨ 1 , _ ⟩ , ! (‼ zero) ⟩
    ~>⟨ β-lookup ⟩
      ⟨ ⟨ 1 , _ ⟩ , t ⟩
    ∎
