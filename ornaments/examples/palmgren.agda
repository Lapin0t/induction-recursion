module ornaments.examples.palmgren where

open import ornaments.prelude
open import ornaments.iir

--open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
open import Data.Nat --renaming (_⊔_ to _⊔ℕ_; zero to zz; suc to suc)
open import Data.Fin renaming (inject₁ to inj)

O : ∀ {n} → (i : Fin n) → Set₁
F : ∀ {n} → (i : Fin n) → Set₁

O zero = Set
O (suc i) = F i → F i
F i = Σ Set (λ A → A → O i)

inj-eq : ∀ {n} → (i : Fin n) → O (inj i) ≡ O i
inj-eq zero = refl
inj-eq (suc i) = cong (λ e → (λ x → x → x) (Σ Set (λ A → A → e))) (inj-eq i)

↓ : ∀ {n} {i : Fin n} → O (inj i) → O i
↓ {i = i} x = subst (λ s → s) (inj-eq i) x

↑ : ∀ {n} {i : Fin n} → O i → O (inj i)
↑ {i = i} x = subst (λ s → s) (sym (inj-eq i)) x

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

module _ {n : ℕ} {A : Fin (suc n) → Set} {B : (i : Fin (suc n)) → A i → O i} where

  data constr : Set where
    nn σσ ππ ww : constr
    Ȧ Ḃ ap₀ ap₁ abs : constr

  code : IIR (O {suc n}) (O {suc n})
  code = λ i → (U i , T i)
    where
      U : Fin (suc n) → poly (O {suc n})
      T : (i : Fin (suc n)) → info (U i) → O i
      u-aux : _ → _

      U i = σ (κ constr) (u-aux i)

      u-aux i (lift nn) = κ (i ≡ zero)
      u-aux i (lift σσ) = ⟨ κ (i ≡ zero) ⟩× ⟨ a ∶ ι zero ⟩× ⟨ a ⟩⇒ ι zero
      u-aux i (lift ππ) = ⟨ κ (i ≡ zero) ⟩× ⟨ a ∶ ι zero ⟩× ⟨ a ⟩⇒ ι zero
      u-aux i (lift ww) = ⟨ κ (i ≡ zero) ⟩× ⟨ a ∶ ι zero ⟩× ⟨ a ⟩⇒ ι zero
      u-aux i (lift Ȧ) =  ⟨ κ (i ≡ zero) ⟩× κ (Fin (suc n))
      u-aux i (lift Ḃ) = κ (A i)
      u-aux i (lift ap₀) = ⟨ κ (i ≡ zero) ⟩× ⟨κ j ∶ Fin n ⟩× ⟨ f ∶ ι (suc j) ⟩×
        ⟨ a ∶ ι zero ⟩× ⟨ a ⟩⇒ ι (inj j)
      u-aux i (lift ap₁) = ⟨κ j ∶ Fin n ⟩× ⟨ κ (i ≡ inj j) ⟩× ⟨ f ∶ ι (suc j) ⟩×
        ⟨ a ∶ ι zero ⟩× ⟨ b ∶ ⟨ a ⟩⇒ ι (inj j) ⟩× κ (π₀ (f (a , λ x → ↓ (b x))))
      u-aux i (lift abs)

      T i (lift nn , lift refl) = ℕ
      T i (lift σσ , lift refl , a , b) = Σ a b
      T i (lift ππ , lift refl , a , b) = (x : a) → b x
      T i (lift ww , lift refl , a , b) = W a b
      T i (lift Ȧ , lift refl , lift j) = A j
      T i (lift Ḃ , lift a) = B i a
      T i (lift ap₀ , lift refl , lift j , f , a , b) = π₀ (f (a , λ x → ↓ (b x)))
      T i (lift ap₁ , lift j , lift refl , f , a , b , lift x) =
        ↑ (π₁ (f (a , λ x → ↓ (b x))) x)
      T i (lift abs , _)

  U : Fin (suc n) → Set
  U = μ code

  T : (i : Fin (suc n)) → U i → O i
  T = dec code
