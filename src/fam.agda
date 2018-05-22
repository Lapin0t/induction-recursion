module fam where

open import prelude


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
(C₀ , d₀) ⟶̃ (C₁ , d₁) = Σ (C₀ → C₁) λ h → d₁ ∘ h ≡ d₀


π : (A : Set) {X : A → Set₁} (B : (a : A) → Fam (X a)) → Fam ((a : A) → X a)
Code (π A B) = (a : A) → Code (B a)
decode (π A B) f a = decode (B a) (f a)


σ : {X : Set₁} {Y : X → Set₁} → (A : Fam X) → (B : (x : X) → Fam (Y x)) → Fam (Σ X Y)
Code (σ A B) = Σ (Code A) λ a → Code (B (decode A a))
decode (σ A B) (a , b) = (decode A a , decode (B _) b)

-- Monad structure
η : ∀ {α} {X : Set α} → X → Fam X
Code (η x) = ⊤
decode (η x) tt = x

μ : ∀ {α} {X : Set α} → Fam (Fam X) → Fam X
Code (μ (C , d)) = Σ C (Code ∘ d)
decode (μ (C , d)) (c₀ , c₁) = decode (d c₀) c₁


𝔽 : Fam Set₁ → Set₁
𝔽 (I , X) = (i : I) → Fam (X i)

_⇒_ : {X : Fam Set₁} → 𝔽 X → 𝔽 X → Set₁
_⇒_ {(I , _)} F G = (i : I) → F i ⟶̃ G i

η𝔽 : {X : Fam Set₁} → ((i : Code X) → decode X i) → 𝔽 X
η𝔽 x = λ i → η (x i)

μ𝔽 : {X : Fam Set₁} → 𝔽 (Code X , λ x → Fam (decode X x)) → 𝔽 X
μ𝔽 F = λ i → μ (F i)
