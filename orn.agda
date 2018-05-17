module orn {I J : Set} where

open import utils
open import iir


module _ {X : I → Set₁} {Y : J → Set₁} where

  data p-orn (e : J → I) (E : Y ⟶̊ (X ∘ e)) : poly X → Set₁
  info+ : ∀ {e E γ} → p-orn e E γ → Set₁
  info↓ : ∀ {e E γ} (o : p-orn e E γ) → info+ o → info γ

  data p-orn e E where
    -- structure preserving
    ι : {i : I} → inv e i → p-orn e E (ι i)
    k : (A : Set) → p-orn e E (k A)
    σ : ∀ {P Q} → (A : p-orn e E P) → (B : (x : info+ A) → p-orn e E (Q (info↓ A x))) → p-orn e E (σ P Q)
    π : (A : Set) → ∀ {P} → ((a : A) → p-orn e E (P a)) → p-orn e E (π A P)

    -- insertions/deletions
    add : (A : poly Y) → ∀ {P} → (info A → p-orn e E P) → p-orn e E P  -- OPTION 1
    add-k : (A : Set) → ∀ {P} → (A → p-orn e E P) → p-orn e E P        -- OPTION 2, no new recursive positions
    del-k : ∀ {A B} → (a : A) → p-orn e E (B (lift a)) → p-orn e E (σ (k A) B)

  info+ {e} (ι (ok j)) = Y j
  info+ (k A) = Lift A
  info+ (σ A B) = Σ (info+ A) (λ a → info+ (B a))
  info+ (π A B) = (a : A) → info+ (B a)
  info+ (add A B) = Σ (info A) (λ a → info+ (B a))
  info+ (add-k A B) = Σ A (λ a → info+ (B a))
  info+ (del-k _ o) = info+ o

  info↓ {E = E} (ι (ok j)) y = E j y
  info↓ (k A) a = a
  info↓ (σ A B) (a , b) = info↓ A a , info↓ (B a) b
  info↓ (π A B) f = λ a → info↓ (B a) (f a)
  info↓ (add A B) (a , b) = info↓ (B a) b
  info↓ (add-k A B) (a , b) = info↓ (B a) b
  info↓ (del-k a o) x = lift a , info↓ o x


  -- interpret back to plain poly
  ⌊_⌋₀ : ∀ {e E γ} → p-orn e E γ → poly Y
  info↑ : ∀ {e E γ} → (o : p-orn e E γ) → info ⌊ o ⌋₀ → info+ o

  ⌊ ι (ok j) ⌋₀ = ι j
  ⌊ k A ⌋₀ = k A
  ⌊ σ A B ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B (info↑ A a) ⌋₀
  ⌊ π A B ⌋₀ = π A λ a → ⌊ B a ⌋₀
  ⌊ add A B ⌋₀ = σ A λ a → ⌊ B a ⌋₀
  ⌊ add-k A B ⌋₀ = σ (k A) λ { (lift a) → ⌊ B a ⌋₀ }
  ⌊ del-k _ o ⌋₀ = ⌊ o ⌋₀

  info↑ (ι (ok _)) x = x
  info↑ (k A) x = x
  info↑ (σ A B) (a , b) = info↑ A a , info↑ (B _) b
  info↑ (π A B) f = λ a → info↑ (B a) (f a)
  info↑ (add A B) (a , b) = a , info↑ (B a) b
  info↑ (add-k A B) (lift a , b) = a , info↑ (B a) b
  info↑ (del-k a o) x = info↑ o x

  orn : (e : J → I) → (E : Y ⟶̊ (X ∘ e)) → FCT X X → Set₁
  orn e E γ = (j : J) → Σ (p-orn e E (π₀ (γ (e j)))) λ o → (x : info+ o) → inv (E j) (π₁ (γ (e j)) (info↓ o x))

  ⌊_⌋ : ∀ {e E γ} → orn e E γ → FCT Y Y
  ⌊_⌋ {e} {E} {γ} o j = ⌊ π₀ (o j) ⌋₀ , λ x → lem (π₁ (o j) (info↑ (π₀ (o j)) x))
    where
      lem : ∀ {α β} {A : Set α} {B : Set β} {f : A → B} {y : B} → inv f y → A
      lem (ok x) = x
