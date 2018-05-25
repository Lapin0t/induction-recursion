{-# OPTIONS --experimental-irrelevance #-}
module ornaments.iir where

open import Agda.Builtin.TrustMe using (primTrustMe)
open import ornaments.prelude
open import ornaments.fam using (Fam; Code; decode; _,_; 𝔽; _>>_; _⇒_; _⟶̃_; _⊙_)


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
⟦ σ A B ⟧ᵢ F = ornaments.fam.σ (⟦ A ⟧ᵢ F) λ a → ⟦ B a ⟧ᵢ F
⟦ π A B ⟧ᵢ F = ornaments.fam.π A λ a → ⟦ B a ⟧ᵢ F

⟦_⟧ : {X Y : Fam Set₁} → (α : IIR X Y) → 𝔽 X → 𝔽 Y
⟦ node , emit ⟧ F j = emit j >> ⟦ node j ⟧ᵢ F

⟦_⟧[_]ᵢ : ∀ {X} (p : poly X) {F G : 𝔽 X} → F ⇒ G → ⟦ p ⟧ᵢ F ⟶̃ ⟦ p ⟧ᵢ G
⟦ ι i ⟧[ φ ]ᵢ = φ i
⟦ κ A ⟧[ φ ]ᵢ = (λ a → a) , λ _ → refl
π₀ ⟦ σ A B ⟧[ φ ]ᵢ (a , b) =
  (π₀ ⟦ A ⟧[ φ ]ᵢ a ,
   subst (λ x → Code (⟦ B x ⟧ᵢ _)) (sym (π₁ ⟦ A ⟧[ φ ]ᵢ a))
         (π₀ ⟦ B (decode (⟦ A ⟧ᵢ _) a) ⟧[ φ ]ᵢ b))
π₁ ⟦ σ A B ⟧[ φ ]ᵢ (a , b) =
  cong-Σ (π₁ ⟦ A ⟧[ φ ]ᵢ a)
         (trans (cong₂ (λ x y → decode (⟦ B x ⟧ᵢ _) y) (π₁ ⟦ A ⟧[ φ ]ᵢ a)
                       (subst-elim _ (sym (π₁ ⟦ A ⟧[ φ ]ᵢ a))))
                (π₁ ⟦ B (decode (⟦ A ⟧ᵢ _) a) ⟧[ φ ]ᵢ b))
π₀ ⟦ π A B ⟧[ φ ]ᵢ b = λ a → π₀ ⟦ B a ⟧[ φ ]ᵢ (b a)
π₁ ⟦ π A B ⟧[ φ ]ᵢ b = funext λ a → π₁ ⟦ B a ⟧[ φ ]ᵢ (b a)

⟦_⟧[_] : ∀ {X Y} (α : IIR X Y) {F G : 𝔽 X} → (F ⇒ G) → ⟦ α ⟧ F ⇒ ⟦ α ⟧ G
π₀ (⟦ α ⟧[ φ ] j) = π₀ ⟦ node α j ⟧[ φ ]ᵢ
π₁ (⟦ α ⟧[ φ ] j) x = cong (emit α j) (π₁ ⟦ node α j ⟧[ φ ]ᵢ x)


------------------------------------------------------------------------
-- Initial algebra and Code interpretation

module sized where
  μ : ∀ {X} → IIR X X → Size → 𝔽 X

  {-# NO_POSITIVITY_CHECK #-}
  data μ-C {X} (α : IIR X X) (s : Size) (i : Code X) : Set

  μ-d : ∀ {X} → (α : IIR X X) → {s : Size} → (i : Code X) → μ-C α s i → decode X i

  Code (μ α s i) = μ-C α s i
  decode (μ α s i) = μ-d α i

  data μ-C α s i where
    ⟨_⟩ : ∀ {t : Size< s} → Code (⟦ α ⟧ (μ α t) i) → μ-C α s i

  μ-d α i ⟨ c ⟩ = emit α i (decode (⟦ node α i ⟧ᵢ (μ α _)) c)


  -- catamorphism for μ α
  fold : ∀ {X s} (α : IIR X X) {F : 𝔽 X} → (⟦ α ⟧ F ⇒ F) → μ α s ⇒ F
  π₀ (fold α φ i) ⟨ x ⟩ = π₀ (φ i) (π₀ (⟦ α ⟧[ fold α φ ] i) x)
  π₁ (fold α φ i) ⟨ x ⟩ = trans (π₁ (φ i) (π₀ rec x)) (π₁ rec x)
    where rec : _
          rec = ⟦ α ⟧[ fold α φ ] i


------------------------------------------------------------------------
-- Composition of Codes

module composition where
  IIR* : Fam Set₁ → Set₁ → Set₁
  IIR* X Y = Σ (poly X) λ n → info n → Y

  --↑ : ∀ {X Y} → ((j : Code Y) → IIR* X (decode Y j)) → IIR X Y
  --node (↑ F) j = π₀ (F j)
  --emit (↑ F) j y = π₁ (F j) y

  eta : ∀ {X Y} → Y → IIR* X Y
  eta y = κ ⊤ , λ _ → y

  mu : ∀ {X Y} → IIR* X (IIR* X Y) → IIR* X Y
  mu (n₀ , e₀) = (σ n₀ (λ z → π₀ (e₀ z))) , λ { (n₁ , e₁) → π₁ (e₀ n₁) e₁ }

  pow : ∀ {X} (A : Set) {B : A → Set₁} → ((a : A) → IIR* X (B a)) → IIR* X ((a : A) → B a)
  pow A f = (π A (π₀ ∘ f) , λ z a → π₁ (f a) (z a))

  --_<$>_ : ∀ {X Y Z} → (Y → Z) → IIR* X Y → IIR* X Z
  --f <$> (n , e) = (n , f ∘ e)

  _>>=_ : ∀ {C D E} → IIR* C D → ((x : D) → IIR* C (E x)) → IIR* C (Σ D E)
  (n , e) >>= h = mu (n , λ x → (π₀ (h (e x)) , λ y → (e x , π₁ (h (e x)) y)))

  _/_ : ∀ {X Y} → (p : poly Y) → IIR X Y → IIR* X (info p)
  ι i / R = (node R i , emit R i)
  κ A / R = (κ A , λ a → a)
  σ A B / R = (A / R) >>= (λ a → B a / R)
  π A B / R = pow A (λ a → B a / R)

  _⊙'_ : ∀ {X Y Z} → IIR Y Z → IIR X Y → IIR X Z
  node (γ ⊙' R) j = π₀ (node γ j / R)
  emit (γ ⊙' R) j = emit γ j ∘ π₁ (node γ j / R)
  --↑ λ j → emit γ j <$> (node γ j / R)
