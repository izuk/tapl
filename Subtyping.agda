module Subtyping where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix 4 _=>_

data Type : Set where
  _=>_ : Type → Type → Type
  Top : Type

infix 3 _<:_

data _<:_ : Type → Type → Set where
  s-refl : ∀ {S} → S <: S
  s-trans : ∀ {S T U} → S <: U → U <: T → S <: T
  s-top : ∀ {S} → S <: Top
  s-arrow : ∀ {S₁ S₂ T₁ T₂} → T₁ <: S₁ → S₂ <: T₂ → S₁ => S₂ <: T₁ => T₂

data Term : Set where
  #_ : ℕ → Term
  ƛ_∷_⊸_ : ℕ → Type → Term → Term
  _∘_ : Term → Term → Term

data Value : Term → Set where
  v-ƛ : ∀ {x T t} → Value (ƛ x ∷ T ⊸ t)

data Context : Set where
  Ø : Context
  _,_∷_ : Context → ℕ → Type → Context

infix 4 _∷_∈_

data _∷_∈_ : ℕ → Type → Context → Set where
  Z : ∀ {Γ x T} → x ∷ T ∈ Γ , x ∷ T
  S : ∀ {Γ x T x₁ T₁} → x ∷ T ∈ Γ → x ∷ T ∈ Γ , x₁ ∷ T₁

data _:-_∷_ : Context → Term → Type → Set where
  t-var : ∀ {Γ x T} → x ∷ T ∈ Γ → Γ :- (# x) ∷ T
  t-abs : ∀ {Γ x t₂ T₁ T₂} → (Γ , x ∷ T₁) :- t₂ ∷ T₂ → Γ :- (ƛ x ∷ T₁ ⊸ t₂) ∷ (T₁ => T₂)
  t-app : ∀ {Γ t₁ t₂ T₁₁ T₁₂} → Γ :- t₁ ∷ (T₁₁ => T₁₂) → Γ :- t₂ ∷ T₁₁ → Γ :- (t₁ ∘ t₂) ∷ T₁₂
  t-sub : ∀ {Γ t S T} → Γ :- t ∷ S → S <: T → Γ :- t ∷ T

lemma-inversion₁ : {S T₁ T₂ : Type}
  → S <: T₁ => T₂
  → Σ[ (S₁ , S₂) ∈ (Type × Type) ] (S ≡ (S₁ => S₂)) × (T₁ <: S₁) × (S₂ <: T₂)
lemma-inversion₁ (s-refl {T₁ => T₂}) = (T₁ , T₂) , (refl , s-refl , s-refl)
lemma-inversion₁ (s-arrow {S₁} {S₂} T₁<:S₁ S₂<∶T₂) = (S₁ , S₂) , (refl , T₁<:S₁ , S₂<∶T₂)
lemma-inversion₁ (s-trans S<:U U<:T₁=>T₂) with lemma-inversion₁ U<:T₁=>T₂
... | (U₁ , U₂) , (refl , T₁<:U₁ , U₂<:T₂) with lemma-inversion₁ S<:U
... | (S₁ , S₂) , (refl , U₂<:S₁ , S₂<:U₂) = (S₁ , S₂) , (refl , s-trans T₁<:U₁ U₂<:S₁ , s-trans S₂<:U₂ U₂<:T₂)

lemma₁ : ∀ {Γ x s₂ S₁ T₁ T₂}
  → Γ :- (ƛ x ∷ S₁ ⊸ s₂) ∷ (T₁ => T₂)
  → (T₁ <: S₁) × ((Γ , x ∷ S₁) :- s₂ ∷ T₂)
lemma₁ (t-abs J) = s-refl , J
lemma₁ (t-sub J U<:T) with lemma-inversion₁ U<:T
... | (U₁ , U₂) , refl , T₁<:U₁ , U₂<:T₂ with lemma₁ J
... | U₁<:S₁ , J₁ = s-trans T₁<:U₁ U₁<:S₁ , t-sub J₁ U₂<:T₂

lemma-canonical₁ : ∀ {Γ t T₁ T₂}
  → Γ :- t ∷ (T₁ => T₂)
  → Value t
  → Σ[ (x , T , t₁) ∈ (ℕ × Type × Term) ] (t ≡ ƛ x ∷ T ⊸ t₁)
lemma-canonical₁ (t-abs {_} {x} {s} {T₁} _) _ = (x , T₁ , s) , refl
lemma-canonical₁ (t-sub J S<:T₁=>T₂) v with lemma-inversion₁ S<:T₁=>T₂
... | _ , refl , _ = lemma-canonical₁ J v
