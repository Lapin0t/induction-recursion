module iir {I : Set} where

open import utils


------------------------------------------------------------------------
-- Codes.

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


σ′ : ∀ {D} → (S : poly D) → (f : info S → poly D) → poly D
σ′ = σ
σ″ : ∀ {D} → (A : Set) → (f : A → poly D) → poly D
σ″ a b = σ (k a) (b ∘ Lift.lower)
π′ : ∀ {D} → (P : Set) → (f : P → poly D) → poly D
π′ = π

syntax σ a (λ x → b) = ⟨ x ∶ a ⟩× b
syntax σ′ a (λ _ → b) = ⟨ a ⟩× b
syntax σ″ a (λ x → b ) = ⟨k x ∶ a ⟩× b
syntax π a (λ x → b) = ⟨ x ∶ a ⟩⇒ b
syntax π′ a (λ _ → b) = ⟨ a ⟩⇒ b


------------------------------------------------------------------------
-- Expression of FCT definitions as a functors.


FCT* : (I → Set₁) → Set₁ → Set₁
FCT* D E = Σ (poly D) (λ c → info c → E)

FCT : {J : Set} → (I → Set₁) → (J → Set₁) → Set₁
FCT {J} D E = (j : J) → FCT* D (E j)

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

⟦_⟧ : ∀ {J D E} → FCT D E → obj D → obj {J} E
⟦ γ ⟧ G j = ⟦ π₀ (γ j) ⟧₀ G , π₁ (γ j) ∘ ⟦ π₀ (γ j) ⟧₁ G


------------------------------------------------------------------------
-- Composition of codes

pow : ∀ {D} (A : Set) {E : A → Set₁} → ((a : A) → FCT* D (E a)) → FCT* D ((a : A) → E a)
pow A f = (π A (π₀ ∘ f) , λ z a → π₁ (f a) (z a))

η : ∀ {D E} → E → FCT* D E
η e = (k ⊤ , λ _ → e)

μ' : ∀ {D E} → FCT* D (FCT* D E) → FCT* D E
μ' (c , α) = (σ c (λ z → π₀ (α z))) , λ { (c' , α') → π₁ (α c') α' }

_<$>_ : ∀ {D E F} → (E → F) → FCT* D E → FCT* D F
f <$> c = (π₀ c , f ∘ (π₁ c))

_>>=_ : ∀ {C D E} → FCT* C D → ((x : D) → FCT* C (E x)) → FCT* C (Σ D E)
(c , α) >>= h = μ' (c , λ x → (π₀ (h (α x)) , λ y → (α x , π₁ (h (α x)) y)))

_/_ : ∀ {D E} → (c : poly E) → FCT D E → FCT* D (info c)
ι i / R = R i
k A / R = (k A , λ a → a)
σ S f / R = (S / R) >>= (λ s → f s / R)
π P f / R = pow P (λ p → f p / R)

_⊙_ : ∀ {J C D} {E : J → _} → FCT D E → FCT C D → FCT C E
(γ ⊙ R) i = π₁ (γ i) <$> (π₀ (γ i) / R)


------------------------------------------------------------------------
-- Initial algebra and code interpretation

IIR : (I → Set₁) → Set₁
IIR D = FCT D D

μ-dec : ∀ {D} → IIR D → obj D
{-# NO_POSITIVITY_CHECK #-}
data μ {D} (γ : IIR D) (i : I) : Set
{-# TERMINATING #-}
dec : ∀ {D} → (γ : IIR D) → (i : I) → μ γ i → D i

μ-dec γ i = (μ γ i , dec γ i)

data μ γ i where
  ⟨_⟩ : ⟦ π₀ (γ i) ⟧₀ (μ-dec γ) → μ γ i

dec γ i ⟨ x ⟩ = π₁ (γ i) (⟦ π₀ (γ i) ⟧₁ (μ-dec γ) x)


--fmap : ∀ {D E} {X Y : obj D} (γ : FCT D E) → (X ⟶̃ Y) → ⟦ γ ⟧ X ⟶̃ ⟦ γ ⟧ Y
--fmap γ f i with γ i
--...        | ι i′ , α = π₀ (f i′) , {!   !}
--...        | k A , α = (λ a → a) , {!   !}
--...        | σ A B , α = {!   !} , {!   !}
--...        | π A B , α = (λ f a → {! fmap (B a , ?)  !}) , {!   !}
