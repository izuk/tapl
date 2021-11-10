module Data.Rcd where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≥_; _≟_; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)

infix 3 _,_∷_⟨_⟩
infix 4 _∉_

infix 4 _∷_∈_

data Rcd (A : Set) : Set
data _∉_ {A : Set} : ℕ → Rcd A → Set

data Rcd A where
  Ø : Rcd A
  _,_∷_⟨_⟩ : (r : Rcd A) → (l : ℕ) → (x : A) → (l ∉ r) → Rcd A

data _∉_ where
  zero : ∀ {l} → l ∉ Ø
  suc : ∀ {l l' r l'∉r x} → l ∉ r → l ≢ l' → l ∉ (r , l' ∷ x ⟨ l'∉r ⟩)

data _∷_∈_ {A : Set} : ℕ → (x : A) → Rcd A → Set where
  zero : ∀ {l r x l∉r} → l ∷ x ∈ (r , l ∷ x ⟨ l∉r ⟩)
  suc : ∀ {l l' r x x' l'∉r} → l ∷ x ∈ r → l ∷ x ∈ (r , l' ∷ x' ⟨ l'∉r ⟩)

private
  variable
    A B : Set
    r : Rcd A
    P Q : ℕ → A → Set

map : (A → B) → Rcd A → Rcd B
map-preserves-∉ : ∀ {l} → ∀ {f : A → B} → l ∉ r → l ∉ (map f r)

map f Ø = Ø
map f (r , l ∷ x ⟨ l∉r ⟩) = (map f r) , l ∷ (f x) ⟨ map-preserves-∉ l∉r ⟩

map-preserves-∉ zero = zero
map-preserves-∉ (suc l∉r' l≢l') = suc (map-preserves-∉ l∉r') l≢l'

lemma-rcd-∉ : ∀ {l} → l ∉ r → (∀ {x} → ¬ (l ∷ x ∈ r))
lemma-rcd-∉ (suc _ l≢l) zero = l≢l refl
lemma-rcd-∉ (suc l∉r _) (suc l∷x∈r) = lemma-rcd-∉ l∉r l∷x∈r

lemma-rcd-uniq : ∀ {l x₁ x₂}
  → l ∷ x₁ ∈ r
  → l ∷ x₂ ∈ r
  → x₁ ≡ x₂
lemma-rcd-uniq zero zero = refl
lemma-rcd-uniq (zero {l∉r = l∉r}) (suc l∷∈r) = ⊥-elim (lemma-rcd-∉ l∉r l∷∈r)
lemma-rcd-uniq (suc l'∷∈r) (zero {l∉r = l'∉r}) = ⊥-elim (lemma-rcd-∉ l'∉r l'∷∈r)
lemma-rcd-uniq (suc l∷x₁∈r) (suc l∷x₂∈r) = lemma-rcd-uniq l∷x₁∈r l∷x₂∈r

□ : (ℕ → A → Set) → Rcd A → Set
□ P r = ∀ {l x} → (l ∷ x ∈ r) → P l x

◇ : (ℕ → A → Set) → Rcd A → Set
◇ P r = Σ[ (l , x) ∈ (ℕ × _) ] (l ∷ x ∈ r) × (P l x)

{-

step-inside : ∀ {l x}
  → □ (λ l₁ x₁ → P l₁ x₁ ⊎ Q l₁ x₁) (r , l ∷ x)
  → □ (λ l₁ x₁ → (P l₁ x₁ ⊎ l₁ ≡ l) ⊎ (Q l₁ x₁ × l₁ ≢ l)) r
step-inside {l = l} f {l = l₁} l₁∷x₁∈r with l₁ ≟ l
... | yes l₁≡l = inj₁ (inj₂ l₁≡l)
... | no l₁≢l with f (suc l₁∷x₁∈r l₁≢l)
...   | inj₁ P₁ = inj₁ (inj₁ P₁)
...   | inj₂ Q₁ = inj₂ (Q₁ , l₁≢l)

lemma-rcd-all-or-some : □ (λ l x → P l x ⊎ Q l x) r → □ P r ⊎ ◇ Q r
lemma-rcd-all-or-some {r = Ø} _ = inj₁ λ ()
lemma-rcd-all-or-some {P = P} {r = r , l ∷ x} f with f zero
... | inj₂ Qlx = inj₂ ((l , x) , (zero , Qlx))
... | inj₁ Plx with lemma-rcd-all-or-some (step-inside f)
...   | inj₂ (l₁x₁ , l₁∷x₁∈r , Ql₁x₁ , l₁≢l) = inj₂ (l₁x₁ , suc l₁∷x₁∈r l₁≢l , Ql₁x₁)
...   | inj₁ f+ = inj₁ fₓ
  where
    fₓ : ∀ {l₁ x₁} → l₁ ∷ x₁ ∈ (r , l ∷ x) → P l₁ x₁
    fₓ zero = Plx
    fₓ (suc l₁∷x₁∈r l₁≢l) with f+ l₁∷x₁∈r
    ... | inj₁ Pl₁x₁ = Pl₁x₁
    ... | inj₂ l₁≡l = ⊥-elim (l₁≢l l₁≡l)

⟨_,_⟩ : ∀ {A} → Rcd A → Rcd A → Rcd A
⟨ r₁ , Ø ⟩ = r₁
⟨ r₁ , (r₂ , l ∷ x) ⟩ = ⟨ r₁ , r₂ ⟩ , l ∷ x

-}
