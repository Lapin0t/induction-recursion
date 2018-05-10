module iir where

open import Function using (_∘_)
open import Level using (Lift; lift; _⊔_; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Σ renaming (proj₁ to π₀; proj₂ to π₁)


-- Utilities

data ⊤ : Set where
  tt : ⊤

module slices where

  slice : ∀ {α} → Set α → Set (α ⊔ suc zero)
  slice X = Σ Set (λ A → A → X)

  infix 30 _⁻¹

  _⁻¹ : ∀ {X} → slice X → (X → Set)
  (A , f)⁻¹ = λ x → Σ A (λ a → f a ≡ x)

  ∃_ : ∀ {X} → (X → Set) → slice X
  ∃_ {X} F = (Σ X F) , π₀

  obj : {I : Set} → (I → Set₁) → Set₁
  obj {I} X = (i : I) → slice (X i)

open slices


module dybjer-setzer {I : Set} where

  data DS (D : I → Set₁) (E : Set₁) : Set₁ where
    ι : (e : E) → DS D E
    σ : (S : Set) → (K : S → DS D E) → DS D E
    δ : (P : Set) → (i : P → I) → (K : ((p : P) → D (i p)) → DS D E) → DS D E

  ⟦_⟧₀ : ∀ {D E} → DS D E → obj D → Set
  ⟦_⟧₁ : ∀ {D E} → (c : DS D E) → (G : obj D) → ⟦ c ⟧₀ G → E

  ⟦ ι e ⟧₀ G = ⊤
  ⟦ σ S K ⟧₀ G = Σ S λ s → ⟦ K s ⟧₀ G
  ⟦ δ P i K ⟧₀ G = Σ ((p : P) → π₀ (G (i p))) λ g → ⟦ K (λ p → π₁ (G (i p)) (g p)) ⟧₀ G

  ⟦ ι e ⟧₁ G tt = e
  ⟦ σ S K ⟧₁ G (s , x) = ⟦ K s ⟧₁ G x
  ⟦ δ P i K ⟧₁ G (g , x) = ⟦ K (λ p → π₁ (G (i p)) (g p)) ⟧₁ G x

  ⟦_⟧ : ∀ {D E} → ((i : I) → DS D (E i)) → obj D → obj E
  ⟦ γ ⟧ G i = ⟦ γ i ⟧₀ G , ⟦ γ i ⟧₁ G

  μD : ∀ {D} → ((i : I) → DS D (D i)) → obj D

  {-# NO_POSITIVITY_CHECK #-}
  data μ {D} (γ : (i : I) → DS D (D i)) (i : I) : Set

  {-# TERMINATING #-}
  decode : ∀ {D} → (γ : (i : I) → DS D (D i)) → (i : I) → μ γ i → D i

  μD γ i = (μ γ i , decode γ i)

  data μ γ i where
    ⟨_⟩ : ⟦ γ i ⟧₀ (μD γ) → μ γ i

  decode γ i ⟨ x ⟩ = ⟦ γ i ⟧₁ (μD γ) x


module polynomial {I : Set} where

  data poly (D : I → Set₁) : Set₁
  info : ∀ {D} → poly D → Set₁

  data poly D where
    ι : I → poly D
    k : (A : Set) → poly D
    σ : (S : poly D) → (f : info S → poly D) → poly D
    π : (P : Set) → (f : P → poly D) → poly D

  info {D} (ι i) = D i
  info (k A) = Lift A
  info (σ S f) = Σ (info S) λ x → info (f x)
  info (π P f) = (p : P) → info (f p)

  PN : (I → Set₁) → Set₁ → Set₁
  PN D E = Σ (poly D) (λ c → info c → E)

  iPN : (I → Set₁) → (I → Set₁) → Set₁
  iPN D E = (i : I) → PN D (E i)

  ⟦_⟧₀ : ∀ {D} → poly D → obj D → Set
  ⟦_⟧₁ : ∀ {D} → (γ : poly D) → (G : obj D) → ⟦ γ ⟧₀ G → info γ

  ⟦ ι i ⟧₀ G = π₀ (G i)
  ⟦ k A ⟧₀ G = A
  ⟦ σ S f ⟧₀ G = Σ (⟦ S ⟧₀ G) λ s → ⟦ f (⟦ S ⟧₁ G s) ⟧₀ G
  ⟦ π P f ⟧₀ G = (p : P) → ⟦ f p ⟧₀ G

  ⟦ ι i ⟧₁ G γ = π₁ (G i) γ
  ⟦ k A ⟧₁ G γ = lift γ
  ⟦ σ S f ⟧₁ G (s , γ) = (⟦ S ⟧₁ G s , ⟦ f (⟦ S ⟧₁ G s) ⟧₁ G γ)
  ⟦ π P f ⟧₁ G γ = λ p → ⟦ f p ⟧₁ G (γ p)

  ⟦_⟧ : ∀ {D E} → iPN D E → obj D → obj E
  ⟦ γ ⟧ G i = (⟦ π₀ (γ i) ⟧₀ G , π₁ (γ i) ∘ ⟦ π₀ (γ i) ⟧₁ G)

  module fix where

    μD : ∀ {D} → iPN D D → obj D

    {-# NO_POSITIVITY_CHECK #-}
    data μ {D} (γ : iPN D D) (i : I) : Set

    {-# TERMINATING #-}
    decode : ∀ {D} → (γ : iPN D D) → (i : I) → μ γ i → D i

    μD γ i = (μ γ i , decode γ i)

    data μ γ i where
      ⟨_⟩ : ⟦ π₀ (γ i) ⟧₀ (μD γ) → μ γ i

    decode γ i ⟨ x ⟩ = π₁ (γ i) (⟦ π₀ (γ i) ⟧₁ (μD γ) x)

  module comp where

    pow : ∀ {D} → (A : Set) → {E : A → Set₁} → ((a : A) → PN D (E a)) → PN D ((a : A) → E a)
    pow A f = (π A (π₀ ∘ f) , λ z a → π₁ (f a) (z a))

    η : ∀ {D E} → E → PN D E
    η e = (k ⊤ , λ _ → e)

    μ : ∀ {D E} → PN D (PN D E) → PN D E
    μ (c , α) = (σ c (λ z → π₀ (α z))) , λ { (c' , α') → π₁ (α c') α' }

    _<$>_ : ∀ {D E F} → (E → F) → PN D E → PN D F
    f <$> c = (π₀ c , f ∘ (π₁ c))

    _>>=_ : ∀ {C D E} → PN C D → ((x : D) → PN C (E x)) → PN C (Σ D E)
    (c , α) >>= h = μ (c , λ x → (π₀ (h (α x)) , λ y → (α x , π₁ (h (α x)) y)))

    _/_ : ∀ {D E} → (c : poly E) → iPN D E → PN D (info c)
    ι i / R = R i
    k A / R = (k A , λ a → a)
    σ S f / R = (S / R) >>= (λ s → f s / R)
    π P f / R = pow P (λ p → f p / R)

    _⊙_ : ∀ {C D E} → iPN D E → iPN C D → iPN C E
    (γ ⊙ R) i = π₁ (γ i) <$> (π₀ (γ i) / R)
