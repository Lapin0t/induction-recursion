module ornaments.examples.foo where

open import ornaments.prelude
open import ornaments.iir
open import ornaments.fam hiding (σ; π; μ)


nil : Fam Set₁
nil = ⊤ , λ _ → Lift ⊤

data two : Set where true false : two

nat-code : IIR nil nil
node nat-code _ = σ (κ two) λ { (lift true) → κ ⊤;
                           (lift false) → ι tt }
emit nat-code _ = λ _ → lift tt

nat : Set
nat = μ-C nat-code tt

ze : nat
ze = ⟨ true , tt ⟩

su : nat → nat
su n = ⟨ false , n ⟩

W-code : (A : Set) → (B : A → Set) → IIR nil nil
node (W-code A B) _ = σ (κ A) λ { (lift a) → π (B a) λ _ → ι tt }
emit (W-code A B) _ = λ _ → lift tt

W : (A : Set) → (B : A → Set) → Set
W A B = μ-C (W-code A B) tt

sup : ∀ {A B} → (a : A) → (B a → W A B) → W A B
sup a f = ⟨ a , f ⟩

--data Wᵢ {I : Set} (A : I → Set) (B : {i : I} → A i → Fam I) : I → Set where
--  supᵢ : {i : I} → (a : A i) → ((c : Code (B a)) → Wᵢ A B (decode (B a) c)) → Wᵢ A B i

Wᵢ-code : {I : Set} → (A : I → Set) → (B : {i : I} → A i → Fam I) → IIR (I , λ _ → Lift ⊤) (I , λ _ → Lift ⊤)
node (Wᵢ-code {I} A B) i = σ (κ (A i)) λ { (lift a) → π (Code (B a)) λ c → ι (decode (B a) c) }
emit (Wᵢ-code A B) _ _ = lift tt

Wᵢ : {I : Set} → (A : I → Set) → (B : {i : I} → A i → Fam I) → I → Set
Wᵢ A B = μ-C (Wᵢ-code A B)

supᵢ : ∀ {I A} {B : {i : I} → A i → _} {i : I} → (a : A i) → ((b : Code (B a)) → Wᵢ A B (decode (B a) b)) → Wᵢ A B i
supᵢ a f = ⟨ a , f ⟩
