module Subtyping where

open import Data.Nat using (ℕ; _≥_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

infix 4 _=>_

-- Records are sorted by index.
-- `free` picks out the next available index.
-- Adding to a record requires a proof that the new index is free.

data Rec (A : Set) : Set
free : ∀ {A} → Rec A → ℕ

data Rec A where
  Ø : Rec A
  _,_∷_⟨_⟩ : (ρ : Rec A) → (l : ℕ) → A → (l ≥ free ρ) → Rec A

free Ø = zero
free (_ , l ∷ _ ⟨ _ ⟩) = suc l

data _∷_‼_ {A : Set} : ℕ → A → Rec A → Set where
  Z : ∀ {ρ l x m} → l ∷ x ‼ (ρ , l ∷ x ⟨ m ⟩)
  S : ∀ {ρ l x l₁ x₁ m} → l ∷ x ‼ ρ → l ∷ x ‼ (ρ , l₁ ∷ x₁ ⟨ m ⟩)

data Type : Set where
  _=>_ : Type → Type → Type
  ⟦_⟧ : Rec Type → Type
  Top : Type

infix 3 _<:_

data _<:_ : Type → Type → Set where
  s-refl : ∀ {S} → S <: S
  s-trans : ∀ {S T U} → S <: U → U <: T → S <: T
  s-top : ∀ {S} → S <: Top
  s-arrow : ∀ {S₁ S₂ T₁ T₂} → T₁ <: S₁ → S₂ <: T₂ → S₁ => S₂ <: T₁ => T₂
  s-rcdwidth : ∀ {ρ l T m} → ⟦ ρ , l ∷ T ⟨ m ⟩ ⟧ <: ⟦ ρ ⟧
  s-rcddepth : ∀ {ρ₁ ρ₂ l T₁ T₂ m₁ m₂} → ⟦ ρ₁ ⟧ <: ⟦ ρ₂ ⟧ → T₁ <: T₂ → ⟦ ρ₁ , l ∷ T₁ ⟨ m₁ ⟩ ⟧ <: ⟦ ρ₂ , l ∷ T₂ ⟨ m₂ ⟩ ⟧

lemma-inversion₁ : ∀ {S T₁ T₂}
  → S <: T₁ => T₂
  → Σ[ (S₁ , S₂) ∈ (Type × Type) ] (S ≡ (S₁ => S₂)) × (T₁ <: S₁) × (S₂ <: T₂)
lemma-inversion₁ (s-refl {T₁ => T₂}) = (T₁ , T₂) , (refl , s-refl , s-refl)
lemma-inversion₁ (s-arrow {S₁} {S₂} T₁<:S₁ S₂<∶T₂) = (S₁ , S₂) , (refl , T₁<:S₁ , S₂<∶T₂)
lemma-inversion₁ (s-trans S<:U U<:T₁=>T₂) with lemma-inversion₁ U<:T₁=>T₂
... | (U₁ , U₂) , (refl , T₁<:U₁ , U₂<:T₂) with lemma-inversion₁ S<:U
... | (S₁ , S₂) , (refl , U₂<:S₁ , S₂<:U₂) = (S₁ , S₂) , (refl , s-trans T₁<:U₁ U₂<:S₁ , s-trans S₂<:U₂ U₂<:T₂)

lemma-inversion₂ : ∀ {ρ S}
  → S <: ⟦ ρ ⟧
  → Σ[ ψ ∈ Rec Type ] (S ≡ ⟦ ψ ⟧)
lemma-inversion₂ (s-refl {⟦ ρ ⟧}) = ρ , refl
lemma-inversion₂ (s-trans S<:U U<:⟦ρ⟧) with lemma-inversion₂ U<:⟦ρ⟧
... | ψ , refl with lemma-inversion₂ S<:U
... | ψ₁ , refl = ψ₁ , refl
lemma-inversion₂ (s-rcdwidth {ρ} {l} {T} {m}) = (ρ , l ∷ T ⟨ m ⟩) , refl
lemma-inversion₂ (s-rcddepth {ρ₁} {_} {l} {T₁} {_} {m₁} {_} _ _) = (ρ₁ , l ∷ T₁ ⟨ m₁ ⟩) , refl

lemma-record : ∀ {ρ ψ l T} → ⟦ ρ ⟧ <: ⟦ ψ ⟧ → l ∷ T ‼ ψ → Σ[ S ∈ Type ] (l ∷ S ‼ ρ) × (S <: T)
lemma-record s-refl (Z {x = T}) = T , Z , s-refl
lemma-record s-refl (S {x = T} l∷T‼ψ) = T , S l∷T‼ψ , s-refl
lemma-record (s-trans ⟦ρ⟧<:U U<:⟦ψ⟧) l∷T‼ψ with lemma-inversion₂ U<:⟦ψ⟧
... | ψ₁ , refl with lemma-record U<:⟦ψ⟧ l∷T‼ψ
... | T₁ , l∷T₁‼ψ₁ , T₁<:T with lemma-record ⟦ρ⟧<:U l∷T₁‼ψ₁
... | S₁ , l∷S₁‼ρ , S₁<:T₁ = S₁ , l∷S₁‼ρ , s-trans S₁<:T₁ T₁<:T
lemma-record s-rcdwidth (Z {x = T}) = T , S Z , s-refl
lemma-record s-rcdwidth (S {x = T} l∷T‼ψ) = T , (S (S l∷T‼ψ)) , s-refl
lemma-record (s-rcddepth {T₁ = S₁} _ S₁<:T) Z = S₁ , Z , S₁<:T
lemma-record (s-rcddepth ⟦ρ₁⟧<:⟦ψ₁⟧ _) (S l∷T‼ψ) with lemma-record ⟦ρ₁⟧<:⟦ψ₁⟧ l∷T‼ψ
... | S₂ , l∷S₂‼ρ₁ , S₂<:T = S₂ , S l∷S₂‼ρ₁ , S₂<:T

data Term : Set where
  #_ : ℕ → Term
  ƛ_∷_⊸_ : ℕ → Type → Term → Term
  _∘_ : Term → Term → Term
  ⟦_⟧ : Rec Term → Term
  _‼_ : Term → ℕ → Term

data Value : Term → Set where
  v-ƛ : ∀ {x T t} → Value (ƛ x ∷ T ⊸ t)
  v-rcd : ∀ {ρ} → Value ⟦ ρ ⟧

data Context : Set where
  Ø : Context
  _,_∷_ : Context → ℕ → Type → Context

infix 4 _∷_∈_

data _∷_∈_ : ℕ → Type → Context → Set where
  Z : ∀ {Γ x T} → x ∷ T ∈ Γ , x ∷ T
  S : ∀ {Γ x T y T₁} → x ∷ T ∈ Γ → ¬ (x ≡ y) → x ∷ T ∈ Γ , y ∷ T₁

data _:-_∷_ : Context → Term → Type → Set where
  t-var : ∀ {Γ x T} → x ∷ T ∈ Γ → Γ :- (# x) ∷ T
  t-abs : ∀ {Γ x t₂ T₁ T₂} → (Γ , x ∷ T₁) :- t₂ ∷ T₂ → Γ :- (ƛ x ∷ T₁ ⊸ t₂) ∷ (T₁ => T₂)
  t-app : ∀ {Γ t₁ t₂ T₁₁ T₁₂} → Γ :- t₁ ∷ (T₁₁ => T₁₂) → Γ :- t₂ ∷ T₁₁ → Γ :- (t₁ ∘ t₂) ∷ T₁₂
  t-sub : ∀ {Γ t S T} → Γ :- t ∷ S → S <: T → Γ :- t ∷ T
  t-rcd : ∀ {Γ r ρ t T l m₁ m₂} → Γ :- ⟦ r ⟧ ∷ ⟦ ρ ⟧ → Γ :- t ∷ T → Γ :- ⟦ r , l ∷ t ⟨ m₁ ⟩ ⟧ ∷ ⟦ ρ , l ∷ T ⟨ m₂ ⟩ ⟧
  t-proj : ∀ {Γ t ρ T l} → Γ :- t ∷ ⟦ ρ ⟧ → l ∷ T ‼ ρ → Γ :- (t ‼ l) ∷ T

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
lemma-canonical₁ (t-abs {x = x} {t₂ = s} {T₁ = T₁} _) _ = (x , T₁ , s) , refl
lemma-canonical₁ (t-sub J S<:T₁=>T₂) v with lemma-inversion₁ S<:T₁=>T₂
... | _ , refl , _ = lemma-canonical₁ J v

lemma-canonical₂ : ∀ {Γ t ρ}
  → Γ :- t ∷ ⟦ ρ ⟧
  → Value t
  → Σ[ r ∈ Rec Term ] (t ≡ ⟦ r ⟧)
lemma-canonical₂ (t-rcd {r = r} {t = t} {l = l} {m₁ = m₁} _ _) _ = (r , l ∷ t ⟨ m₁ ⟩) , refl
lemma-canonical₂ (t-sub J S<:⟦ρ⟧) v with lemma-inversion₂ S<:⟦ρ⟧
... | _ , refl = lemma-canonical₂ J v
