%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.coinduction where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.iir hiding (α; β; γ; δ; ε; X; Y)

variable
  {α β γ δ ε} : Level
  {X} : ISet α β
  ..{s} : Size
\end{code}


\begin{code}
{-# NO_POSITIVITY_CHECK #-}
record ν-c {α β γ} {X : ISet α β} (ρ : IIR γ X X) (i : Code X) : Set γ

{-# TERMINATING #-}
ν-d : (ρ : IIR γ X X) (i : Code X) → ν-c ρ i → decode X i

ν : (ρ : IIR γ X X) → 𝔽 γ X
Code   (ν α i) = ν-c α i
decode (ν α i) = ν-d α i
\end{code}


\begin{code}
record ν-c ρ i where
  constructor ⟨_⟩
  coinductive
  field
    force : Code (⟦ ρ ⟧ (ν ρ) i)
open ν-c public

ν-d ρ i x = decode (⟦ ρ ⟧ (ν ρ) i) (force x)

unroll : (ρ : IIR γ X X) → ν ρ ⇒ ⟦ ρ ⟧ (ν ρ)
unroll ρ i x = force x , refl

record coalg {-<-}{α β γ} (δ : Level) {X : ISet α β}{->-}(ρ : IIR γ X X) : Set (α ⊔ β ⊔ lsuc δ ⊔ γ) where
  field
    obj : 𝔽 δ X
    mor : obj ⇒ ⟦ ρ ⟧ obj
open coalg public

{-# TERMINATING #-}
unfold : {ρ : IIR γ X X} (φ : coalg δ ρ) → obj φ ⇒ ν ρ
unfoldm : {ρ : IIR γ X X} (φ : coalg δ ρ) → ⟦ ρ ⟧ (obj φ) ⇒ ν ρ

unfold φ = unfoldm φ ⊙ mor φ
unfoldm {ρ = ρ} φ i x = let y , p = ⟦ ρ ⟧[ unfold φ ] i x in ⟨ y ⟩ , p

\end{code}
