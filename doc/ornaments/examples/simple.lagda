\begin{code}
module ornaments.examples.simple where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.pow
open import ornaments.iir
open import ornaments.orn


! : ∀ {A : Set} → A → Set₁
! _ = Lift ⊤

!! : ISet
!! = ⊤ , !

data two : Set where tt ff : two

pattern `_ x = _ , x

nat-c : IIR !! !!
node nat-c _ = σ (κ two) (λ { (lift tt) → κ ⊤; (lift ff) → ι * })
emit nat-c _ _ = lift *

nat : {_ : Size} → Set
nat {s} = μ-C nat-c {s} *

pattern ze = ⟨ tt , * ⟩
pattern su n = ⟨ ff , n ⟩

list-o : (X : Set) → orn (λ _ → ⊤ , λ _ _ → Lift ⊤) (λ _ → ⊤ , λ _ _ → Lift ⊤) nat-c
node (list-o X) _ = σ (κ two) (λ { (lift tt) → κ ⊤;
                                   (lift ff) → add-κ X (λ _ → ι (* , *)) })
emit (list-o X) j x = lift *

list : Set → {_ : Size} → Set
list X {s} = μ-C ⌊ list-o X ⌋ {s} (* , *)

\end{code}
