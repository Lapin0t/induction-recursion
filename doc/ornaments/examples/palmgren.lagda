\begin{code}
module ornaments.examples.palmgren where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.iir

--open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
open import Data.Nat renaming (zero to zz; suc to ss)
open import Data.Fin renaming (inject₁ to inj)

toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zz    = refl
toℕ-fromℕ (ss n) = cong ss (toℕ-fromℕ n)

O″ : ℕ → Set₁
F″ : (n : ℕ) → Set₁

O″ zz = Set
O″ (ss n) = F″ n → F″ n

F″ n = Σ Set (λ A → A → O″ n)

O′ : ∀ {n} → (i : Fin n) → Set₁
F : ∀ {n} → (i : Fin n) → Set₁

O′ i = O″ (toℕ i)
F i = F″ (toℕ i)
--O′ (suc i) = F i → F i
--F i = Σ Set (λ A → A → O′ i)

O : ℕ → Fam Set₁
Code (O n) = Fin n
decode (O n) = O′

inj-eq : ∀ {n} → (i : Fin n) → O′ (inj i) ≡ O′ i
inj-eq zero = refl
inj-eq (suc i) = cong (λ e → (λ x → x → x) (Σ Set (λ A → A → e))) (inj-eq i)

↓ : ∀ {n} {i : Fin n} → O′ (inj i) → O′ i
↓ {i = i} x = subst (λ s → s) (inj-eq i) x

↑ : ∀ {n} {i : Fin n} → O′ i → O′ (inj i)
↑ {i = i} x = subst (λ s → s) (sym (inj-eq i)) x

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

module _ {n : ℕ} (A : Fin (ss n) → Set) (B : (i : Fin (ss n)) → A i → O′ i) where

  data constr : Set where
    n₀ n₁ σσ ππ ww : constr
    Ȧ Ḃ ap₀ ap₁ : constr

  code : IIR (O (ss n)) (O (ss n))
  code = U , T
    where
      U : Fin (ss n) → poly (O (ss n))
      T : (i : Fin (ss n)) → info (U i) → O′ i

      U i = σ (κ constr) λ {
        (lift n₀)   → κ (i ≡′ zero);
        (lift n₁)   → κ (i ≡′ zero);
        (lift σσ)   → σ (κ (i ≡′ zero)) λ _ → σ (ι zero) λ a → π a λ _ → ι zero;
        (lift ππ)   → σ (κ (i ≡′ zero)) λ _ → σ (ι zero) λ a → π a λ _ → ι zero;
        (lift ww)   → σ (κ (i ≡′ zero)) λ _ → σ (ι zero) λ a → π a λ _ → ι zero;
        (lift Ȧ)    → σ (κ (i ≡′ zero)) λ _ → κ (Fin (ss n));
        (lift Ḃ)    → κ (A i);
        (lift ap₀)  → σ (κ (i ≡′ zero)) λ _ → σ (κ (Fin n)) λ j →
          σ (ι (suc (lower j))) λ f → σ (ι zero) λ a → π a λ _ → ι (inj (lower j));
        (lift ap₁)  → σ (κ (Fin n)) λ j → σ (κ (i ≡ inj (lower j))) λ _ →
          σ (ι (suc (lower j))) λ f → σ (ι zero) λ a → σ (π a (λ _ →
          ι (inj (lower j)))) λ b → κ (π₀ (f (a , λ x → ↓ (b x)))) }

      T _ (lift n₀ , lift refl)                                 = ⊥
      T _ (lift n₁ , lift refl)                                 = ⊤
      T _ (lift σσ , lift refl , a , b)                         = Σ a b
      T _ (lift ππ , lift refl , a , b)                         = (x : a) → b x
      T _ (lift ww , lift refl , a , b)                         = W a b
      T _ (lift Ȧ , lift refl , lift j)                         = A j
      T _ (lift Ḃ , lift a)                                     = B _ a
      T _ (lift ap₀ , lift refl , lift j , f , a , b)           = π₀ (f (a , λ x → ↓ (b x)))
      T _ (lift ap₁ , lift j , lift refl , f , a , b , lift x)  = ↑ (π₁ (f (a , λ x → ↓ (b x))) x)

  U : {_ : Size} → Fin (ss n) → Set
  U {s} = μ-C code {s}

  T : {s : Size} → (i : Fin (ss n)) → U {s} i → O′ i
  T = μ-d code

  OP : {_ : Size} → (i : Fin (ss n)) → Σ Set (λ a → a → O′ i)
  OP i = (U i , T i)

  OP′ : {_ : Size} → F″ n
  OP′ = subst F″ (toℕ-fromℕ _) (OP (fromℕ n))
  --OP′ (ss n) = {!   !}

Q : ∀ {n : ℕ} → (F″ n → O″ n) → O″ (ss n)
Q f x = ⊤ , λ _ → f x

Q₁ : O″ 1
Q₁ (A , B) = OP A′ B′ zero
  where
    A′ : Fin (ss zz) → _
    A′ zero = A
    A′ (suc ())

    B′ : (i : Fin (ss zz)) → A′ i → O′ i
    B′ zero a = B a
    B′ (suc ())

Q₂′ : F″ 1 → O″ 1
Q₂′ (I , J) (A , B) = OP A′ B′ zero
  where
    A′ : Fin 2 → _
    A′ zero = A
    A′ (suc zero) = I
    A′ (suc (suc ()))

    B′ : (i : Fin 2) → A′ i → O′ i
    B′ zero a = B a
    B′ (suc zero) i x = J i x
    B′ (suc (suc ()))

Q₂ : O″ 2
Q₂ = Q Q₂′
{-π₀ (Q₂ (I , J)) = ⊤
π₁ (Q₂ (I , J)) _ (A , B) = OP A′ B′ zero-}

Q₃′ : F″ 2 → O″ 2
π₀ (Q₃′ (I , J) (A , B)) = ⊤
π₁ (Q₃′ (X , Y) (I , J)) _ (A , B) = {!   !}
  where
    A′ : Fin 3 → _
    A′ zero = A
    A′ (suc zero) = I
    A′ (suc (suc zero)) = X
    A′ (suc (suc (suc ())))

    B′ : (i : Fin 3) → A′ i → O′ i
    B′ zero a = B a
    B′ (suc zero) i z = J i z
    B′ (suc (suc zero)) x z = Y x z
    B′ (suc (suc (suc ())))

Q₄′ : F″ 3 → O″ 3
π₀ (Q₄′ _ _) = ⊤
π₁ (Q₄′ (X , Y) (I , J)) _ (A , B) = OP A′ B′ (suc zero)
  where
    A′ : Fin 4 → _
    A′ zero = ⊤
    A′ (suc zero) = A
    A′ (suc (suc zero)) = I
    A′ (suc (suc (suc zero))) = X
    A′ (suc (suc (suc (suc ()))))

    B′ : (i : Fin 4) → A′ i → O′ i
    B′ zero = λ _ → ⊤
    B′ (suc zero) = B
    B′ (suc (suc zero)) = J
    B′ (suc (suc (suc zero))) = Y
    B′ (suc (suc (suc (suc ()))))
--lem : ∀ {n i} → (P : ∀ {n} → Fin n → Set) → 
--lem : ∀ {α} (P : ∀ {n} → Fin (ss n) → Set α) {i} → P (inj i) → P

A′ : ∀ {n} → F″ (ss n) → F″ n → Fin (ss n) → Set
B′ : ∀ {n X Y} → (i : Fin (ss n)) → A′ X Y i → O″ (toℕ i)

A′ {zz} (I , J) (A , B) i = {! A  !}
A′ {ss n} (I , J) (A , B) i = {! A′  !}
B′ = ?

Q′ : (n : ℕ) → F″ n → O″ n
Q′ zz _ = ⊤
Q′ (ss n) X Y = OP′ (A′ X Y) B′

--Q zz = ⊤
--π₀ (Q (ss n) (I , J)) = ⊤
--π₁ (Q (ss n) (I , J)) _ = {!  OP′ !}
--Q i (I , J) = fold′ O′ (λ { j x (A , B) → {! !} }) ⊤ i
--Q {_} zero (I , J) = ⊤
--Q (suc i) (I , J) x = fold′ O′ {!   !} {!   !} {! i  !} {!   !}

{-SUPER : (n : ℕ) → Σ Set (λ A → A → O′ (fromℕ n))
SUPER n = (A (fromℕ n) , B (fromℕ n))
  where
    A : ∀ {n} → Fin (ss n) → Set
    B : ∀ {n} → (i : Fin (ss n)) → A i → O′ i

    A {zz} _ = ⊤
    A {ss n} zero = ⊤
    A {ss n} (suc i) = U A B i

    B {_} zero a = ⊤
    B {zz} (suc i) _ (a , b) = a , b
    B {ss n} (suc i) a (x , y) = (U {!   !} {!   !} {!   !}) , {!   !}-}

\end{code}
