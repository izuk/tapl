module Subtyping where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)

infix 3 _,_∷_

data Rcd (A : Set) : Set where
  Ø : Rcd A
  _,_∷_ : Rcd A → ℕ → A → Rcd A

infix 4 _∷_∈_

data _∷_∈_ {A : Set} : ℕ → A → Rcd A → Set where
  zero : ∀ {r l x} → l ∷ x ∈ (r , l ∷ x)
  suc : ∀ {r l x l₁ x₁} → l ∷ x ∈ r → ¬ (l ≡ l₁) → l ∷ x ∈ (r , l₁ ∷ x₁)

data All {A : Set} (P : A → Set) : Rcd A → Set where
  all : ∀ {r} → (∀ {l x} → l ∷ x ∈ r → P x) → All P r

rcd-uniq : {A : Set} → {r : Rcd A} → ∀ {l x₁ x₂} → l ∷ x₁ ∈ r → l ∷ x₂ ∈ r → x₁ ≡ x₂
rcd-uniq zero zero = refl
rcd-uniq zero (suc _ ¬l≡l₁) = ⊥-elim (¬l≡l₁ refl)
rcd-uniq (suc _ ¬l≡l₁) zero = ⊥-elim (¬l≡l₁ refl)
rcd-uniq (suc ∈₁ _) (suc ∈₂ _) = rcd-uniq ∈₁ ∈₂

infix 4 _=>_

data Type : Set where
  _=>_ : Type → Type → Type
  ⟨_⟩ : Rcd Type → Type
  Top : Type

infix 3 _<:_

data _<:_ : Type → Type → Set where
  s-refl : ∀ {S} → S <: S
  s-trans : ∀ {S T U} → S <: U → U <: T → S <: T
  s-top : ∀ {S} → S <: Top
  s-arrow : ∀ {S₁ S₂ T₁ T₂} → T₁ <: S₁ → S₂ <: T₂ → S₁ => S₂ <: T₁ => T₂
  s-rcd : ∀ {ρ ψ} → (∀ {l T} → l ∷ T ∈ ψ → Σ[ S ∈ Type ] (l ∷ S ∈ ρ) × (S <: T)) → ⟨ ρ ⟩ <: ⟨ ψ ⟩

lemma-inversion₁ : ∀ {S T₁ T₂}
  → S <: T₁ => T₂
  → Σ[ (S₁ , S₂) ∈ (Type × Type) ] (S ≡ (S₁ => S₂)) × (T₁ <: S₁) × (S₂ <: T₂)
lemma-inversion₁ (s-refl {T₁ => T₂}) = (T₁ , T₂) , (refl , s-refl , s-refl)
lemma-inversion₁ (s-arrow {S₁} {S₂} T₁<:S₁ S₂<∶T₂) = (S₁ , S₂) , (refl , T₁<:S₁ , S₂<∶T₂)
lemma-inversion₁ (s-trans S<:U U<:T₁=>T₂) with lemma-inversion₁ U<:T₁=>T₂
... | (U₁ , U₂) , (refl , T₁<:U₁ , U₂<:T₂) with lemma-inversion₁ S<:U
... | (S₁ , S₂) , (refl , U₂<:S₁ , S₂<:U₂) = (S₁ , S₂) , (refl , s-trans T₁<:U₁ U₂<:S₁ , s-trans S₂<:U₂ U₂<:T₂)

lemma-inversion₂ : ∀ {ρ S}
  → S <: ⟨ ρ ⟩
  → Σ[ ψ ∈ Rcd Type ] (S ≡ ⟨ ψ ⟩)
lemma-inversion₂ (s-refl {⟨ ρ ⟩}) = ρ , refl
lemma-inversion₂ (s-trans S<:U U<:⟨ρ⟩) with lemma-inversion₂ U<:⟨ρ⟩
... | ψ , refl with lemma-inversion₂ S<:U
... | ψ₁ , refl = ψ₁ , refl
lemma-inversion₂ (s-rcd {ρ = ρ} _) = ρ , refl

lemma-record : ∀ {ρ ψ l T}
  → ⟨ ρ ⟩ <: ⟨ ψ ⟩
  → l ∷ T ∈ ψ
  → Σ[ S ∈ Type ] (l ∷ S ∈ ρ) × (S <: T)
lemma-record {T = T} s-refl l∷T∈ψ = T , l∷T∈ψ , s-refl
lemma-record (s-trans ⟨ρ⟩<:U U<:⟨ψ⟩) l∷T∈ψ with lemma-inversion₂ U<:⟨ψ⟩
... | ψ₁ , refl with lemma-record U<:⟨ψ⟩ l∷T∈ψ
... | T₁ , l∷T₁∈ψ₁ , T₁<:T with lemma-record ⟨ρ⟩<:U l∷T₁∈ψ₁
... | S₁ , l∷S₁∈ρ , S₁<:T₁ = S₁ , l∷S₁∈ρ , s-trans S₁<:T₁ T₁<:T
lemma-record (s-rcd P) = P

data Term : Set where
  #_ : ℕ → Term
  ƛ_∷_⊸_ : ℕ → Type → Term → Term
  _∘_ : Term → Term → Term
  ⟨_⟩ : Rcd Term → Term
  _‼_ : Term → ℕ → Term

Context : Set
Context = Rcd Type

data _:-_∷_ : Context → Term → Type → Set where
  t-var : ∀ {Γ x T} → x ∷ T ∈ Γ → Γ :- (# x) ∷ T
  t-abs : ∀ {Γ x t₂ T₁ T₂} → (Γ , x ∷ T₁) :- t₂ ∷ T₂ → Γ :- (ƛ x ∷ T₁ ⊸ t₂) ∷ (T₁ => T₂)
  t-app : ∀ {Γ t₁ t₂ T₁₁ T₁₂} → Γ :- t₁ ∷ (T₁₁ => T₁₂) → Γ :- t₂ ∷ T₁₁ → Γ :- (t₁ ∘ t₂) ∷ T₁₂
  t-sub : ∀ {Γ t S T} → Γ :- t ∷ S → S <: T → Γ :- t ∷ T
  t-rcd : ∀ {Γ ρ r} → (∀ {l T} → l ∷ T ∈ ρ → Σ[ t ∈ Term ] (l ∷ t ∈ r) × (Γ :- t ∷ T)) → Γ :- ⟨ r ⟩ ∷ ⟨ ρ ⟩
  t-proj : ∀ {Γ t ρ T l} → Γ :- t ∷ ⟨ ρ ⟩ → l ∷ T ∈ ρ → Γ :- (t ‼ l) ∷ T

lemma-match : ∀ {Γ r ρ T l}
  → Γ :- ⟨ r ⟩ ∷ ⟨ ρ ⟩
  → l ∷ T ∈ ρ
  → Σ[ t ∈ Term ] (l ∷ t ∈ r) × (Γ :- t ∷ T)
lemma-match (t-sub Γ:-t∷⟨ψ⟩ ⟨ψ⟩<:⟨ρ⟩) l∷T∈ρ with lemma-inversion₂ ⟨ψ⟩<:⟨ρ⟩
... | ψ , refl with lemma-record ⟨ψ⟩<:⟨ρ⟩ l∷T∈ρ
... | S₁ , l∷S₁∈ψ , S₁<:T with lemma-match Γ:-t∷⟨ψ⟩ l∷S₁∈ψ
... | t , l∷t∈r , Γ:-t∷S₁ = t , l∷t∈r , t-sub Γ:-t∷S₁ S₁<:T
lemma-match (t-rcd P) l∷T∈ρ = P l∷T∈ρ

lemma-15'3'3 : ∀ {Γ x S₁ t T₁ T₂}
  → Γ :- (ƛ x ∷ S₁ ⊸ t) ∷ (T₁ => T₂)
  → (T₁ <: S₁) × ((Γ , x ∷ S₁) :- t ∷ T₂)
lemma-15'3'3 (t-abs S₁∷T₂) = s-refl , S₁∷T₂
lemma-15'3'3 (t-sub S₁∷U₁=>U₂ U₁=>U₂<:T₁=>T₂) with lemma-inversion₁ U₁=>U₂<:T₁=>T₂
... | (U₁ , U₂) , refl , T₁<:U₁ , U₂<:T₂ with lemma-15'3'3 S₁∷U₁=>U₂
... | U₁<:S₁ , S₁∷U₂ = s-trans T₁<:U₁ U₁<:S₁ , t-sub S₁∷U₂ U₂<:T₂

data Value : Term → Set where
  v-ƛ : ∀ {x T t} → Value (ƛ x ∷ T ⊸ t)
  v-rcd : ∀ {r} → All Value r → Value ⟨ r ⟩

lemma-canonical₁ : ∀ {Γ t T₁ T₂}
  → Γ :- t ∷ (T₁ => T₂)
  → Value t
  → Σ[ (x , T , t₁) ∈ (ℕ × Type × Term) ] (t ≡ ƛ x ∷ T ⊸ t₁)
lemma-canonical₁ (t-abs {x = x} {t₂ = s} {T₁ = T₁} _) _ = (x , T₁ , s) , refl
lemma-canonical₁ (t-sub J S<:T₁=>T₂) v with lemma-inversion₁ S<:T₁=>T₂
... | _ , refl , _ = lemma-canonical₁ J v

lemma-canonical₂ : ∀ {Γ t ρ}
  → Γ :- t ∷ ⟨ ρ ⟩
  → Value t
  → Σ[ r ∈ Rcd Term ] (t ≡ ⟨ r ⟩)
lemma-canonical₂ (t-rcd {r = r} _) _ = r , refl
lemma-canonical₂ (t-sub J S<:⟨ρ⟩) v with lemma-inversion₂ S<:⟨ρ⟩
... | _ , refl = lemma-canonical₂ J v

postulate [_⊸_]_ : ℕ → Term → Term → Term

postulate lemma-substitution : ∀ {Γ x s t S T} → (Γ , x ∷ S) :- t ∷ T → Γ :- s ∷ S → Γ :- [ x ⊸ s ] t ∷ T

data _⊸_ : Term → Term → Set where
  e-app₁ : ∀ {t₁ t₁' t₂} → t₁ ⊸ t₁' → (t₁ ∘ t₂) ⊸ (t₁' ∘ t₂)
  e-app₂ : ∀ {v₁ t₂ t₂'} → t₂ ⊸ t₂' → Value v₁ → (v₁ ∘ t₂) ⊸ (v₁ ∘ t₂')
  e-appabs : ∀ {x T₁₁ t₁₂ v₂} → Value v₂ → ((ƛ x ∷ T₁₁ ⊸ t₁₂) ∘ v₂) ⊸ ([ x ⊸ v₂ ] t₁₂)
  e-proj : ∀ {t₁ t₁' l} → t₁ ⊸ t₁' → (t₁ ‼ l) ⊸ (t₁' ‼ l)
  e-projrcd : ∀ {r l v} → l ∷ v ∈ r → Value ⟨ r ⟩ → (⟨ r ⟩ ‼ l) ⊸ v
  e-rcd : ∀ {r l t t'} → t ⊸ t' → l ∷ t ∈ r → ⟨ r ⟩ ⊸ ⟨ r , l ∷ t' ⟩

preservation : ∀ {Γ t t' T}
  → Γ :- t ∷ T
  → t ⊸ t'
  → Γ :- t' ∷ T
preservation (t-app t₁∷T₁₁=>T t₂∷T₁₁) (e-app₁ t⊸t') = t-app (preservation t₁∷T₁₁=>T t⊸t') t₂∷T₁₁
preservation (t-app t₁∷T₁₁=>T t₂∷T₁₁) (e-app₂ t⊸t' x) = t-app t₁∷T₁₁=>T (preservation t₂∷T₁₁ t⊸t')
preservation (t-app t₁∷T₁₁=>T t₂∷T₁₁) (e-appabs _) with lemma-15'3'3 t₁∷T₁₁=>T
... | T₁₂<:T₁₁ , T₁₁∷T = lemma-substitution T₁₁∷T (t-sub t₂∷T₁₁ T₁₂<:T₁₁)
preservation (t-sub t∷S S<:T) t⊸t' = t-sub (preservation t∷S t⊸t') S<:T
preservation (t-rcd {Γ = Γ} {ρ = ρ} {r = r} P) (e-rcd {l = l} {t' = t'} t⊸t' l∷t∈r) = t-rcd f
  where
    f : ∀ {l₁ T₁} → l₁ ∷ T₁ ∈ ρ → Σ[ t₁ ∈ Term ] (l₁ ∷ t₁ ∈ (r , l ∷ t')) × (Γ :- t₁ ∷ T₁)
    f {l₁ = l₁} l₁∷T₁∈ρ with l₁ ≟ l | P l₁∷T₁∈ρ
    ... | no ¬l₁≡l | t₁ , l₁∷t₁∈r , t₁∷T₁ = t₁ , (suc l₁∷t₁∈r ¬l₁≡l) , t₁∷T₁
    ... | yes refl | t₁ , l₁∷t₁∈r , t₁∷T₁ with rcd-uniq l₁∷t₁∈r l∷t∈r
    ... | refl = t' , zero , preservation t₁∷T₁ t⊸t'
preservation (t-proj t∷⟨ρ⟩ l∷T∈ρ) (e-proj t⊸t') = t-proj (preservation t∷⟨ρ⟩ t⊸t') l∷T∈ρ
preservation (t-proj ⟨r⟩∷⟨ρ⟩ l∷T∈ρ) (e-projrcd l∷t∈r _) with lemma-match ⟨r⟩∷⟨ρ⟩ l∷T∈ρ
... | t₁ , l∷t₁∈r , t₁∷T with rcd-uniq l∷t₁∈r l∷t∈r
... | refl = t₁∷T

data Progress (t : Term) : Set where
  step : ∀ {t'} → t ⊸ t' → Progress t
  done : Value t → Progress t

progress : ∀{t A} → Ø :- t ∷ A → Progress t
progress (t-abs _) = done v-ƛ
progress (t-app t₁ t₂) with progress t₁
... | step t₁' = step (e-app₁ t₁')
... | done v₁ with progress t₂
... | step t₂' = step (e-app₂ t₂' v₁)
... | done z = {!!}
progress (t-sub z x) = {!!}
progress (t-rcd P) = {!!}
progress (t-proj z x) = {!!}
