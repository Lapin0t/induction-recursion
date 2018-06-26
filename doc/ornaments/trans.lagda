%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.trans where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.iir
open import ornaments.induction

record nat-t {α X Y} (γ δ : IIR {α} X Y) : Set (lsuc α) where
  field
    η : (F : 𝔽 X) → ⟦ γ ⟧ F ⇒ ⟦ δ ⟧ F
    η-nat : ∀ {A B} (f : A ⇒ B) → η B ⊙ ⟦ γ ⟧[ f ] ≡ ⟦ δ ⟧[ f ] ⊙ η A
open nat-t public

foo : ∀ {α X} {γ δ : IIR {α} X X} (n : nat-t γ δ) {s} → μ γ {s} ⇒ μ δ {s}
foo {γ = γ} n i ⟨ x ⟩ =
  let y , p = (η n (μ _) ⊙ ⟦ γ ⟧[ foo n ]) i x in ⟨ y ⟩ , p
\end{code}
