module Normalization (Term : Set) (Value : Term → Set) (_~>_ : Term → Term → Set) where

infix  2 _~~>_
infix  1 begin_
infixr 2 _~>⟨_⟩_
infix  3 _∎

data _~~>_ : Term → Term → Set where
  _∎ : ∀ (t) → t ~~> t
  _~>⟨_⟩_ : ∀ t₁ {t₂ t₃} → t₁ ~> t₂ → t₂ ~~> t₃ → t₁ ~~> t₃

begin_ : ∀ {t₁ t₂} → t₁ ~~> t₂ → t₁ ~~> t₂
begin D = D

data Progress (t : Term) : Set where
  step : ∀{t₁} → t ~> t₁ → Progress t
  done : Value t → Progress t

data Finished (t : Term) : Set where
  done : Value t → Finished t
  out-of-gas : Finished t
  
data Steps (t : Term) : Set where
  steps : ∀ {t₁} → t ~~> t₁ → Finished t₁ → Steps t
