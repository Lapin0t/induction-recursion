module utils where

open import Data.Product using (Σ; _,_) public
open import Function using (_∘_) public
open import Level using (Level; _⊔_; Lift; lift) renaming (zero to lzero; suc to lsuc) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong) public

-- Common stuff

open Σ renaming (proj₁ to π₀; proj₂ to π₁) public

data ⊥ : Set where
data ⊤ : Set where tt : ⊤


-- Power sets

--pow : (X : Set) → Set₁
--pow X = Σ Set λ A → X → A

_⟶̊_ : ∀ {α β} {I : Set} → (I → Set α) → (I → Set β) → Set (α ⊔ β)
_⟶̊_ {I = I} X Y = (i : I) → X i → Y i
