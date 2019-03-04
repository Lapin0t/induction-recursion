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
  --..{s} : Size
\end{code}


\begin{code}
ν : (ρ : IIR γ X X) {s : Size} → 𝔽 γ X

{-# NO_POSITIVITY_CHECK #-}
data ν-c-aux {α β γ} {X : ISet α β} (ρ : IIR γ X X) {s : Size} (i : Code X) : Set γ where
  con : {t : Size< s} → Code (⟦ ρ ⟧ (ν ρ {t}) i) → ν-c-aux ρ i

record ν-c {α β γ} {X : ISet α β} (ρ : IIR γ X X) {s : Size} (i : Code X) : Set γ where
  constructor ⟨_⟩
  coinductive
  field
    force : ν-c-aux ρ {s} i
open ν-c public

ν-d : (ρ : IIR γ X X) {s : Size} (i : Code X) → ν-c ρ {s} i → decode X i
ν-d ρ i x with force x
...       | con {t} a = decode (⟦ ρ ⟧ (ν ρ {t}) i) a


Code   (ν ρ {s} i) = ν-c ρ {s} i
decode (ν ρ {s} i) = ν-d ρ {s} i
\end{code}


\begin{code}
{-unroll : (ρ : IIR γ X X) → ν ρ ⇒ ⟦ ρ ⟧ (ν ρ)
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
-}
\end{code}
