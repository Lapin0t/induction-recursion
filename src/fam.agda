module fam where

open import utils


record Fam {α} (X : Set α) : Set (lsuc lzero ⊔ α) where
  constructor _,_
  field
    Code : Set
    decode : Code → X
open Fam public


-- Postcomposition
_•_ : ∀ {α} {X Y : Set α} → (X → Y) → Fam X → Fam Y
Code (f • F) = Code F
decode (f • F) = f ∘ decode F


-- Morphisms
_⟶̃_ : ∀ {α} {X : Set α} → Fam X → Fam X → Set α
(c₀ , d₀) ⟶̃ (c₁ , d₁) = Σ (c₀ → c₁) λ h → d₁ ∘ h ≡ d₀


π : (A : Set) {X : A → Set₁} (B : (a : A) → Fam (X a)) → Fam ((a : A) → X a)
Code (π A B) = (a : A) → Code (B a)
decode (π A B) f a = decode (B a) (f a)


σ : {X : Set₁} {Y : X → Set₁} → (A : Fam X) → (B : (x : X) → Fam (Y x)) → Fam (Σ X Y)
Code (σ A B) = Σ (Code A) λ a → Code (B (decode A a))
decode (σ A B) (a , b) = (decode A a , decode (B _) b)


𝔽 : (X : Fam Set₁) → Set₁
𝔽 (Code , decode) = (c : Code) → Fam (decode c)

_⇒_ : {X : Fam Set₁} → 𝔽 X → 𝔽 X → Set₁
_⇒_ {X} F G = (x : Code X) → F x ⟶̃ G x
