module ir where

open import Level using (_⊔_; Lift; lift)
open import Data.Fin using (Fin; zero; suc)
open import Function
open import Relation.Binary.PropositionalEquality


-- UTILS

{-data zero : Set where

data one : Set where
  * : one

data two : Set where
  ff : two
  tt : two-}

infixr 4 _,_
record Σ {α β} (a : Set α) (b : a → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    π₀ : a
    π₁ : b π₀


-- objs
fam : Set₁ → Set₁
fam D = Σ Set (λ A → A → D)

-- arrows
_⟶_ : ∀ {X} → fam X → fam X → Set₁
(A , p) ⟶ (B , q) = Σ (A → B) (λ f → (a : A) → p a ≡ q (f a))

-- Dybjer-Setzer codes

module dybjer-setzer where

  data ds (d e : Set₁) : Set₁ where
    ι : e → ds d e
    σ : (a : Set) → (a → ds d e) → ds d e
    δ : (a : Set) → ((a → d) → ds d e) → ds d e

  ⟦_⟧₀ : ∀ {d e} → ds d e → fam d → Set
  ⟦ ι e ⟧₀ Z = Fin 1
  ⟦ σ A f ⟧₀ Z = Σ A (λ a → ⟦ f a ⟧₀ Z)
  ⟦ δ A F ⟧₀ (U , T) = Σ (A → U) (λ g → ⟦ F (T ∘ g) ⟧₀ (U , T))

  ⟦_⟧₁ : ∀ {d e} → (c : ds d e) → (z : fam d) → ⟦ c ⟧₀ z → e
  ⟦ ι e ⟧₁ Z zero = e
  ⟦ ι e ⟧₁ Z (suc ())
  ⟦ σ A f ⟧₁ Z (a , x) = ⟦ f a ⟧₁ Z x
  ⟦ δ A F ⟧₁ (U , T) (g , x) = ⟦ F (T ∘ g) ⟧₁ (U , T) x

  ⟦_⟧ : ∀ {d e} → ds d e → fam d → fam e
  ⟦ c ⟧ Z = (⟦ c ⟧₀ Z , ⟦ c ⟧₁ Z)

  data μ {D : Set₁} (γ : ds D D) : Set
  out : ∀ {D} → (γ : ds D D) → μ γ → D
  
  data μ γ where
    ⟨_⟩ : ⟦ γ ⟧₀ (μ γ , out γ) → μ γ

  out γ ⟨ t ⟩ = ⟦ γ ⟧₁ (μ γ , out γ) t


module polynomial where

  data poly (D : Set₁) : Set₁
  info : ∀ {D} → poly D → Set₁

  data poly D where
    ι : poly D
    k : (A : Set) → poly D
    σ : (S : poly D) → (info S → poly D) → poly D
    π : (A : Set) → (A → poly D) → poly D

  info {D} ι = D
  info (k A) = Lift A
  info (σ S f) = Σ (info S) (λ x → info (f x))
  info (π A f) = (a : A) → info (f a)

  PN : Set₁ → Set₁ → Set₁
  PN D E = Σ (poly D) (λ c → info c → E)

  ⟦_⟧₀ : ∀ {D} → poly D → fam D → Set
  ⟦_⟧ᵢ : ∀ {D} → (c : poly D) → (x : fam D) → ⟦ c ⟧₀ x → info c

  ⟦ ι ⟧₀ (U , T) = U
  ⟦ k A ⟧₀ X = A
  ⟦ σ S f ⟧₀ X = Σ (⟦ S ⟧₀ X) (λ s → ⟦ f (⟦ S ⟧ᵢ X s) ⟧₀ X)
  ⟦ π A f ⟧₀ X = (a : A) → ⟦ f a ⟧₀ X

  ⟦ ι ⟧ᵢ (U , T) x = T x
  ⟦ k A ⟧ᵢ X a = lift a
  ⟦ σ S f ⟧ᵢ X (s , x) = ⟦ S ⟧ᵢ X s , ⟦ f (⟦ S ⟧ᵢ X s) ⟧ᵢ X x
  ⟦ π A f ⟧ᵢ X g = λ a → ⟦ f a ⟧ᵢ X (g a)

  ⟦_⟧ : ∀ {D E} → PN D E → fam D → fam E
  ⟦ c , α ⟧ Z = (⟦ c ⟧₀ Z , α ∘ (⟦ c ⟧ᵢ Z))

