module utils where

open import Data.Product using (Σ; _,_) public
open import Function using (_∘_) public
open import Level using (Level; _⊔_; Lift; lift)
                  renaming (zero to lzero; suc to lsuc) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open Σ renaming (proj₁ to π₀; proj₂ to π₁) public

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

data inv {α β} {I : Set α} {J : Set β} (e : J → I) : I → Set β where
  ok : (j : J) → inv e (e j)


obj : {I : Set} → (I → Set₁) → Set₁
obj {I} X = (i : I) → Σ Set (λ A → A → X i)

_⟶̊_ : {I : Set} → (I → Set₁) → (I → Set₁) → Set₁
_⟶̊_ {I} X Y = (i : I) → X i → Y i

_⟶̃_ : ∀ {I} {X : I → Set₁} → obj X → obj X → Set₁
_⟶̃_ {I} {X} a b = (i : I) → Σ (π₀ (a i) → π₀ (b i)) λ h → π₁ (b i) ∘ h ≡ π₁ (a i)
