module Context (Type : Set) where

open import Data.Nat using (ℕ; suc; zero)

infixl 5  _,_

data Context : Set where
  Ø : Context
  _,_ : Context → Type → Context

infix  4  _∋_∷_

data _∋_∷_ : Context → ℕ → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ zero ∷ A
  S : ∀ {Γ x A B} → Γ ∋ x ∷ A → Γ , B ∋ suc x ∷ A
