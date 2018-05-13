module iir where

open import Function using (_∘_)
open import Level using (Lift; lift)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open Σ renaming (proj₁ to π₀; proj₂ to π₁)


-- Utilities

data ⊤ : Set where
  tt : ⊤

data inv {α β} {I : Set α} {J : Set β} (e : J → I) : I → Set β where
  ok : (j : J) → inv e (e j)

obj : {I : Set} → (I → Set₁) → Set₁
obj {I} X = Σ Set (λ A → A → Σ I X)


module irish {I : Set} where

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

  PN : (I → Set₁) → (I → Set₁) → Set₁
  PN D E = Σ (poly D) (λ γ → info γ → Σ I E)

  ⟦_⟧₀ : ∀ {D} → poly D → obj D → Set
  ⟦_⟧₁ : ∀ {D} → (γ : poly D) → (G : obj D) → ⟦ γ ⟧₀ G → info γ

  ⟦ ι i ⟧₀ (X , F) = inv (π₀ ∘ F) i
  ⟦ k A ⟧₀ G = A
  ⟦ σ S f ⟧₀ G = Σ (⟦ S ⟧₀ G) λ s → ⟦ f (⟦ S ⟧₁ G s) ⟧₀ G
  ⟦ π P f ⟧₀ G = (p : P) → ⟦ f p ⟧₀ G

  ⟦ ι _ ⟧₁ G (ok x) = π₁ (π₁ G x)
  ⟦ k A ⟧₁ G a = lift a
  ⟦ σ S f ⟧₁ G (s , γ) = ⟦ S ⟧₁ G s , ⟦ f (⟦ S ⟧₁ G s) ⟧₁ G γ
  ⟦ π P f ⟧₁ G γ = λ p → ⟦ f p ⟧₁ G (γ p)

  module _ where

    ⟦_⟧ : ∀ {D E} → PN D E → obj D → obj E
    ⟦ γ , α ⟧ G = ⟦ γ ⟧₀ G , λ x → α (⟦ γ ⟧₁ G x)

  module fix where

    μ-dec : ∀ {D} → PN D D → obj D
    {-# NO_POSITIVITY_CHECK #-}
    data μ {D} (γ : PN D D) : I → Set
    {-# TERMINATING #-}
    dec : ∀ {D} → (γ : PN D D) → {i : I} → μ γ i → D i

    μ-dec γ = (Σ I (μ γ) , λ { (i , x) → i , dec γ x})

    data μ γ where
      ⟨_⟩ : (x : ⟦ π₀ γ ⟧₀ (μ-dec γ)) → μ γ (π₀ (π₁ γ (⟦ π₀ γ ⟧₁ (μ-dec γ) x)))

    dec γ ⟨ x ⟩ = π₁ (π₁ γ (⟦ π₀ γ ⟧₁ (μ-dec γ) x))

  open fix public

  module comp where

    xPN : (D : I → Set₁) → Set₁ → Set₁
    xPN D E = Σ (poly D) (λ c → info c → E)

    pow : ∀ {D} (X : Set) {E : X → Set₁} → ((x : X) → xPN D (E x)) → xPN D ((x : X) → E x)
    pow X f = (π X (π₀ ∘ f) , λ z x → π₁ (f x) (z x))

    η : ∀ {D E} → E → xPN D E
    η e = k ⊤ , λ _ → e

    μ' : ∀ {D E} → xPN D (xPN D E) → xPN D E
    μ' (c , α) = (σ c λ z → π₀ (α z)) , λ { (c' , α') → π₁ (α c') α' }

    _<$>_ : ∀ {D E F} → (E → F) → xPN D E → xPN D F
    f <$> γ = π₀ γ , f ∘ (π₁ γ)

    _>>=_ : ∀ {C D E} → xPN C D → ((x : D) → xPN C (E x)) → xPN C (Σ D E)
    (γ , α) >>= h = μ' (γ , λ x → (π₀ (h (α x)) , λ y → (α x , π₁ (h (α x)) y)))

    _/_ : ∀ {D E} → (c : poly E) → PN D E → xPN D (info c)
    ι i / R = (σ (π₀ R) λ x → k (π₀ (π₁ R x) ≡ i)) , λ { (x , lift refl) → π₁ (π₁ R x) }
    k A / R = k A , λ a → a
    σ S f / R = (S / R) >>= (λ s → f s / R)
    π P f / R = pow P (λ p → f p / R)

    _⊙_ : ∀ {C D E} → PN D E → PN C D → PN C E
    (γ ⊙ R) = π₁ γ <$> (π₀ γ / R)

open irish

module palmgren where

    open import Level using (Level) renaming (zero to ℓz; suc to ℓs)
    open import Data.Nat renaming (_⊔_ to _⊔ℕ_; zero to zz; suc to ss)
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

    module _ {n : ℕ} {A : Fin (ss n) → Set} {B : (i : Fin (ss n)) → A i → O i} where

      pattern nn = zero
      pattern σσ = suc zero
      pattern ππ = suc (suc zero)
      pattern ww = suc (suc (suc zero))
      pattern Ȧ = suc (suc (suc (suc zero)))
      pattern Ḃ = suc (suc (suc (suc (suc zero))))
      pattern ap₀ = suc (suc (suc (suc (suc (suc zero)))))
      pattern ap₁ = suc (suc (suc (suc (suc (suc (suc zero))))))
      pattern abs = suc (suc (suc (suc (suc (suc (suc (suc ())))))))

      code : PN (O {ss n}) (O {ss n})
      code = (γ , α)
        where
          γ : _
          γ-aux : _
          α : info γ → _

          γ = σ (k (Fin 8)) γ-aux

          γ-aux (lift nn) = k ⊤
          γ-aux (lift σσ) = σ (ι zero) λ a → π a λ _ → ι zero
          γ-aux (lift ππ) = σ (ι zero) λ a → π a λ _ → ι zero
          γ-aux (lift ww) = σ (ι zero) λ a → π a λ _ → ι zero
          γ-aux (lift Ȧ) = k (Fin (ss n))
          γ-aux (lift Ḃ) = σ (k (Fin (ss n))) λ { (lift i) → k (A i) }
          γ-aux (lift ap₀) = σ (k (Fin n)) λ { (lift j) → σ (ι (suc j)) λ f → σ (ι zero) λ a → π a λ _ → ι (inj j)}
          γ-aux (lift ap₁) = σ (k (Fin n)) λ { (lift j) → σ (ι (suc j)) λ f → σ (ι zero) λ a → σ (π a λ _ → ι (inj j)) λ b → k (π₀ (f (a , λ x → ↓ (b x)))) }
          γ-aux (lift abs)

          α (lift nn , lift _) = (zero , ℕ)
          α (lift σσ , (a , b)) = (zero , Σ a b)
          α (lift ππ , (a , b)) = (zero , ((x : a) → b x))
          α (lift ww , (a , b)) = (zero , W a b)
          α (lift Ȧ , lift i) = (zero , A i)
          α (lift Ḃ , (lift i , lift a)) = (i , B i a)
          α (lift ap₀ , (lift _ , (f , (a , b)))) = (zero , π₀ (f (a , λ x → ↓ (b x))))
          α (lift ap₁ , (lift i , (f , (a , (b , lift x))))) = (inj i , ↑ (π₁ (f (a , λ x → ↓ (b x))) x))
          α (lift abs , _)

      U : Fin (ss n) → Set
      U = μ code

      T : {i : Fin (ss n)} → U i → O i
      T = dec code
