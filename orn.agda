module orn {I J : Set} {X : I → Set₁} where

open import utils
open import iir


data orn* {D : I → Set₁} (e : J → I) : poly D → Set₁
x-info : ∀ {D e γ} → orn* {D} e γ → Set₁
info-↓ : ∀ {D e γ} (o : orn* {D} e γ) → x-info o → info γ

data orn* {D} e where
  -- structure preserving
  ι : {i : I} → inv e i → orn* e (ι i)
  k : (A : Set) → orn* e (k A)
  σ : ∀ {P Q} → (A : orn* e P) → (B : (x : x-info A) → orn* e (Q (info-↓ A x))) → orn* e (σ P Q)
  π : (A : Set) → ∀ {P} → ((a : A) → orn* e (P a)) → orn* e (π A P)

  -- insertions/deletions
  add : (A : poly (D ∘ e)) → ∀ {P} → (info A → orn* e P) → orn* e P  -- OPTION 1
  add-k : (A : Set) → ∀ {P} → (A → orn* e P) → orn* e P              -- OPTION 2, no new recursive positions
  del-k : ∀ {A B} → (a : A) → orn* e (B (lift a)) → orn* e (σ (k A) B)

x-info {D} {e} (ι (ok j)) = D (e j)
x-info (k A) = Lift A
x-info (σ A B) = Σ (x-info A) (λ a → x-info (B a))
x-info (π A B) = (a : A) → x-info (B a)
x-info (add A B) = Σ (info A) (λ a → x-info (B a))
x-info (add-k A B) = Σ A (λ a → x-info (B a))
x-info (del-k _ o) = x-info o

info-↓ (ι (ok _)) x = x
info-↓ (k A) a = a
info-↓ (σ A B) (a , b) = info-↓ A a , info-↓ (B a) b
info-↓ (π A B) f = λ a → info-↓ (B a) (f a)
info-↓ (add A B) (a , b) = info-↓ (B a) b
info-↓ (add-k A B) (a , b) = info-↓ (B a) b
info-↓ (del-k a o) x = lift a , info-↓ o x


-- interpret back to plain poly
⌊_⌋₀ : ∀ {D e γ} → orn* {D} e γ → poly (D ∘ e)
info-↑ : ∀ {D e γ} → (o : orn* {D} e γ) → info ⌊ o ⌋₀ → x-info o

⌊ ι (ok j) ⌋₀ = ι j
⌊ k A ⌋₀ = k A
⌊ σ A B ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B (info-↑ A a) ⌋₀
⌊ π A B ⌋₀ = π A λ a → ⌊ B a ⌋₀
⌊ add A B ⌋₀ = σ A λ a → ⌊ B a ⌋₀
⌊ add-k A B ⌋₀ = σ (k A) λ { (lift a) → ⌊ B a ⌋₀ }
⌊ del-k _ o ⌋₀ = ⌊ o ⌋₀

info-↑ (ι (ok _)) x = x
info-↑ (k A) x = x
info-↑ (σ A B) (a , b) = info-↑ A a , info-↑ (B _) b
info-↑ (π A B) f = λ a → info-↑ (B a) (f a)
info-↑ (add A B) (a , b) = a , info-↑ (B a) b
info-↑ (add-k A B) (lift a , b) = a , info-↑ (B a) b
info-↑ (del-k a o) x = info-↑ o x


{-⌊_⌋₁ : ∀ {D E e} {γ : FCT* D E} → orn* e (π₀ γ) → FCT* (D ∘ e) E
⌊_⌋₁ {γ = (c , α)} o = ⌊ o ⌋₀ , λ x → α (info-↓ o (info-↑ o x))

-- full ornaments
orn : ∀ {D E} → (J → I) → (FCT* D E) → Set₁
orn e γ = Σ (orn* e (π₀ γ)) λ o → x-info o → {!  π₁ γ!}-}
