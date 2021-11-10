module Language.Unit where

open import Data.Rcd using (Rcd; Ø; _,_∷_⟨_⟩; _∉_; _∷_∈_)
open import Data.Nat using (ℕ; _≟_; _<?_; suc; pred; zero; compare; less; equal; greater)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  Unit : Type

infix 9 #_
infix 5 ƛ_∷_∙_
infix 7 _∘_

data Term : Set where
  #_ : ℕ → Term
  ƛ_∷_∙_ :  ℕ → Type → Term → Term
  _∘_ :  Term → Term → Term
  unit : Term

data Value : Term → Set where
  V-Abs : ∀ {x A t} → Value (ƛ x ∷ A ∙ t)
  V-Unit : Value unit

infix 5 _[_:=_]

_[_:=_] : Term → ℕ → Term → Term
# x₁ [ x := t ] with x₁ ≟ x
... | yes _ = t
... | no _ = # x₁
(ƛ x₁ ∷ A ∙ t₁) [ x := t ] with x₁ ≟ x
... | yes _ = ƛ x₁ ∷ A ∙ t₁
... | no _ = ƛ x₁ ∷ A ∙ (t₁ [ x := t ])
t₁ ∘ t₂ [ x := t ] = (t₁ [ x := t ]) ∘ (t₂ [ x := t ])
unit [ x := t₁ ] = unit

infix 3 _↝_

data _↝_ : Term → Term → Set where
  E-App₁ : ∀ {t₁ t₂ t} → t₁ ↝ t₂ → t₁ ∘ t ↝ t₂ ∘ t
  E-App₂ : ∀ {t t₁ t₂} → Value t → t₁ ↝ t₂ → t ∘ t₁ ↝ t ∘ t₂
  E-AppAbs : ∀ {x A t₁ t₂} → Value t₂ → (ƛ x ∷ A ∙ t₁) ∘ t₂ ↝ t₁ [ x := t₂ ]

Context : Set
Context = Rcd Type

infix  2  _⊢_∷_

data _⊢_∷_ : Context → Term → Type → Set where
  T-Var : ∀ {Γ x A} → x ∷ A ∈ Γ → Γ ⊢ # x ∷ A
  T-Abs : ∀ {Γ x A t B x∉Γ} → Γ , x ∷ A ⟨ x∉Γ ⟩ ⊢ t ∷ B → Γ ⊢ (ƛ x ∷ A ∙ t) ∷ A ⇒ B
  T-App : ∀ {Γ t₁ t₂ A B} → Γ ⊢ t₁ ∷ A ⇒ B → Γ ⊢ t₂ ∷ A → Γ ⊢ t₁ ∘ t₂ ∷ B
  T-Unit : ∀ {Γ} → Γ ⊢ unit ∷ Unit

data Progress (t : Term) : Set where
  step : ∀ {t'} → t ↝ t' → Progress t
  done : Value t → Progress t

progress : ∀ {t A} → Ø ⊢ t ∷ A → Progress t
progress (T-Abs x) = done V-Abs
progress (T-App t₁ t₂) with progress t₁
... | step t₁↝t₁' = step (E-App₁ t₁↝t₁')
... | done V-Abs with progress t₂
...   | step t₂↝t₂' = step (E-App₂ V-Abs t₂↝t₂')
...   | done v₂ = step (E-AppAbs v₂)
progress T-Unit = done V-Unit

subst-lemma : ∀ {Γ t₁ x t A₁ A x∉Γ}
  → Γ ⊢ t ∷ A
  → Γ , x ∷ A ⟨ x∉Γ ⟩ ⊢ t₁ ∷ A₁
  → Γ ⊢ t₁ [ x := t ] ∷ A₁
subst-lemma {x = x} {t = t} t∷A (T-Var {x = x₁} x₁∷A₁) with x ≟ x₁ | # x₁ [ x := t ]
... | yes _ | z = {!!}
... | no _ | z = {!!}
subst-lemma t∷A (T-Abs q) = {!!}
subst-lemma t∷A (T-App t₁₁∷A₂⇒A₁ t₁₂∷A₂) = T-App (subst-lemma t∷A t₁₁∷A₂⇒A₁) (subst-lemma t∷A t₁₂∷A₂)
subst-lemma t∷A T-Unit = T-Unit

preservation : ∀ {Γ t t' A} → Γ ⊢ t ∷ A → t ↝ t' → Γ ⊢ t' ∷ A
preservation (T-App t₁ t₂) (E-App₁ t₁↝t₁') = T-App (preservation t₁ t₁↝t₁') t₂
preservation (T-App t₁ t₂) (E-App₂ _ t₂↝t₂') = T-App t₁ (preservation t₂ t₂↝t₂')
preservation (T-App (T-Abs t₁∷A₁) t∷A) (E-AppAbs _) = subst-lemma t∷A t₁∷A₁

