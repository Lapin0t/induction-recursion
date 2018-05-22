module iir where

open import prelude
open import fam using (Fam; Code; decode; _,_; 𝔽; _•_; _⇒_; _⟶̃_)


------------------------------------------------------------------------
-- Codes.


data poly (X : Fam Set₁) : Set₁
info : {X : Fam Set₁} → poly X → Set₁

data poly X where
  ι : Code X → poly X
  κ : (A : Set) → poly X
  σ : (A : poly X) → (B : info A → poly X) → poly X
  π : (A : Set) → (B : A → poly X) → poly X

info {X} (ι i) = decode X i
info (κ A) = Lift A
info (σ A B) = Σ (info A) λ x → info (B x)
info (π A B) = (a : A) → info (B a)



------------------------------------------------------------------------
-- Expression of IIR definitions as a functors.


record IIR (X Y : Fam Set₁) : Set₁ where
  constructor _,_
  field
    node : (y : Code Y) → poly X
    emit : (y : Code Y) → info (node y) → decode Y y
open IIR public

⟦_⟧ᵢ : ∀ {X} → (p : poly X) → 𝔽 X → Fam (info p)

⟦ ι i ⟧ᵢ F = F i
⟦ κ A ⟧ᵢ F = (A , lift)
⟦ σ A B ⟧ᵢ F = fam.σ (⟦ A ⟧ᵢ F) λ a → ⟦ B a ⟧ᵢ F
⟦ π A B ⟧ᵢ F = fam.π A λ a → ⟦ B a ⟧ᵢ F

⟦_⟧ : {X Y : Fam Set₁} → (α : IIR X Y) → 𝔽 X → 𝔽 Y
⟦ node , emit ⟧ F j = emit j • ⟦ node j ⟧ᵢ F

⟦_⟧[_]ᵢ : ∀ {X} (p : poly X) {F G : 𝔽 X} → F ⇒ G → ⟦ p ⟧ᵢ F ⟶̃ ⟦ p ⟧ᵢ G
⟦ ι i ⟧[ m ]ᵢ = m i
⟦ κ A ⟧[ m ]ᵢ = (λ a → a) , refl
π₀ ⟦ σ A B ⟧[ m ]ᵢ (c₀ , c₁) with ⟦ A ⟧[ m ]ᵢ
...  | (h , eq) = h c₀ , subst (λ h₁ → Code (⟦ B (h₁ c₀) ⟧ᵢ _)) (sym eq)
                               (π₀ ⟦ B (decode (⟦ A ⟧ᵢ _) c₀) ⟧[ m ]ᵢ c₁)
π₁ ⟦ σ A B ⟧[ m ]ᵢ = funext λ { (c₀ , c₁) → {!aux ? ?  !} }
  where aux : ∀ {α β} {A : Set α} {B₀ B₁ : A → Set β} {x : Σ A B₀} {y : Σ A B₁} → π₀ x ≡ π₀ y → π₁ x ≡ π₁ y → x ≡ y
        aux = ?
π₀ ⟦ π A B ⟧[ m ]ᵢ h a = π₀ ⟦ B a ⟧[ m ]ᵢ (h a)
π₁ ⟦ π A B ⟧[ m ]ᵢ = funext λ h → funext λ a → cong (λ f → f (h a))
                                                    (π₁ ⟦ B a ⟧[ m ]ᵢ)

⟦_⟧[_] : ∀ {X Y} (α : IIR X Y) {F G : 𝔽 X} → (F ⇒ G) → ⟦ α ⟧ F ⇒ ⟦ α ⟧ G
π₀ (⟦ α ⟧[ m ] j) = π₀ ⟦ node α j ⟧[ m ]ᵢ
π₁ (⟦ α ⟧[ m ] j) = cong (λ f x → emit α j (f x)) (π₁ ⟦ node α j ⟧[ m ]ᵢ)


------------------------------------------------------------------------
-- Initial algebra and Code interpretation

μ : ∀ {X} → IIR X X → 𝔽 X

{-# NO_POSITIVITY_CHECK #-}
data μ-C {X} (α : IIR X X) (i : Code X) : Set

{-# TERMINATING #-}
μ-d : ∀ {X} → (α : IIR X X) → (i : Code X) → μ-C α i → decode X i

Code (μ α i) = μ-C α i
decode (μ α i) = μ-d α i

data μ-C α i where
  ⟨_⟩ : Code (⟦ α ⟧ (μ α) i) → μ-C α i

μ-d α i ⟨ c ⟩ = emit α i (decode (⟦ node α i ⟧ᵢ (μ α)) c)


------------------------------------------------------------------------
-- Composition of Codes

module composition where
  IIR* : Fam Set₁ → Set₁ → Set₁
  IIR* X Y = Σ (poly X) λ n → info n → Y

  ↑ : ∀ {X Y} → ((j : Code Y) → IIR* X (decode Y j)) → IIR X Y
  node (↑ F) j = π₀ (F j)
  emit (↑ F) j y = π₁ (F j) y

  η : ∀ {X Y} → Y → IIR* X Y
  η y = κ ⊤ , λ _ → y

  μ' : ∀ {X Y} → IIR* X (IIR* X Y) → IIR* X Y
  μ' (n₀ , e₀) = (σ n₀ (λ z → π₀ (e₀ z))) , λ { (n₁ , e₁) → π₁ (e₀ n₁) e₁ }

  pow : ∀ {X} (A : Set) {B : A → Set₁} → ((a : A) → IIR* X (B a)) → IIR* X ((a : A) → B a)
  pow A f = (π A (π₀ ∘ f) , λ z a → π₁ (f a) (z a))

  _<$>_ : ∀ {X Y Z} → (Y → Z) → IIR* X Y → IIR* X Z
  f <$> (n , e) = (n , f ∘ e)

  _>>=_ : ∀ {C D E} → IIR* C D → ((x : D) → IIR* C (E x)) → IIR* C (Σ D E)
  (n , e) >>= h = μ' (n , λ x → (π₀ (h (e x)) , λ y → (e x , π₁ (h (e x)) y)))

  _/_ : ∀ {X Y} → (p : poly Y) → IIR X Y → IIR* X (info p)
  ι i / R = (node R i , emit R i)
  κ A / R = (κ A , λ a → a)
  σ A B / R = (A / R) >>= (λ a → B a / R)
  π A B / R = pow A (λ a → B a / R)

  _⊙_ : ∀ {X Y Z} → IIR Y Z → IIR X Y → IIR X Z
  γ ⊙ R = ↑ λ j → emit γ j <$> (node γ j / R)
