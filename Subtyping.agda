module Subtyping where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

infix 2 _,_

data ∑ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → ∑ A B

syntax ∑ A (λ x → B) = ∃[ x ∈ A ] B

infixl 2 _&_
infixl 2 _×_

record _&_ (A B : Set) : Set where
  constructor _×_
  field
    fst : A
    snd : B

infix 4 _=>_

data Type : Set where
  _=>_ : Type → Type → Type
  Top : Type

infix 3 _<:_

data _<:_ : Type → Type → Set where
  s-refl : {S : Type} → S <: S
  s-trans : {S T U : Type} → S <: U → U <: T → S <: T
  s-top : {S : Type} → S <: Top
  s-arrow : {S₁ S₂ T₁ T₂ : Type} → T₁ <: S₁ → S₂ <: T₂ → S₁ => S₂ <: T₁ => T₂

lemma-inversion₁ : {S T₁ T₂ : Type}
  → S <: T₁ => T₂
  → ∃[ (S₁ × S₂) ∈ (Type & Type) ] ((S ≡ (S₁ => S₂)) & (T₁ <: S₁) & (S₂ <: T₂))
lemma-inversion₁ (s-refl {T₁ => T₂}) = (T₁ × T₂) , (refl × s-refl × s-refl)
lemma-inversion₁ (s-arrow {S₁} {S₂} T₁<:S₁ S₂<∶T₂) = (S₁ × S₂) , (refl × T₁<:S₁ × S₂<∶T₂)
lemma-inversion₁ (s-trans S<:U U<:T₁=>T₂) with lemma-inversion₁ U<:T₁=>T₂
... | (U₁ × U₂) , (refl × T₁<:U₁ × U₂<:T₂)  with lemma-inversion₁ S<:U
... | (S₁ × S₂) , (refl × U₂<:S₁ × S₂<:U₂) = (S₁ × S₂) , (refl × s-trans T₁<:U₁ U₂<:S₁ × s-trans S₂<:U₂ U₂<:T₂)
