%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.induction {α β} where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.iir
\end{code}


------------------------------------------------------------------------
-- Initial algebra and Code interpretation

%<*init-alg-def>
\begin{code}
μ : {-<-}{X : ISet α β} →{->-} IIR X X → {-<-}{_ : Size} →{->-} 𝔽 X

{-<-}
{-# NO_POSITIVITY_CHECK #-}
{->-}
data μ-c {-<-}{X : ISet α β}{->-} (γ : IIR X X) {-<-}{s : Size}{->-} (i : Code X) : Set α

μ-d : {-<-}{X : ISet α β} →{->-} (γ : IIR X X) → {-<-}{s : Size} → {->-}(i : Code X) → μ-c γ {-<-}{s}{->-} i → decode X i

Code    (μ γ {-<-}{s}{->-} i)  = μ-c γ {-<-}{s}{->-} i
decode  (μ γ i)  = μ-d γ i

\end{code}
%</init-alg-def>


%<*init-alg-impl>
\begin{code}
data μ-c γ {-<-}{s}{->-} i where
  ⟨_⟩ : {-<-}∀ {t : Size< s} →{->-} Code (⟦ γ ⟧ (μ γ {-<-}{t}{->-}) i) → μ-c γ i

μ-d γ i ⟨ c ⟩ = emit γ i (decode (⟦ node γ i ⟧ᵢ (μ γ)) c)

roll : {-<-}∀ {X} {γ : IIR X X} {s} {t : Size< s} → {->-}⟦ γ ⟧ (μ γ{-<-}{t}{->-}) ⇒ μ γ{-<-}{s}{->-}
roll i x = ⟨ x ⟩ , refl

unroll-c : ∀ {X} {γ : IIR X X} {s} {_ : Size< s} (i : Code X) → μ-c γ {s} i → Σ (Size< s) (λ t → Code (⟦ γ ⟧ (μ γ {t}) i))
unroll-c _ ⟨ x ⟩ = _ , x

unroll-d : ∀ {X} {γ : IIR X X} {s} {_ : Size< s} (i : Code X) → (x : μ-c γ {s} i) → μ-d γ i x ≡ decode (⟦ γ ⟧ (μ γ) i) (π₁ $ unroll-c i x)
unroll-d _ ⟨ _ ⟩ = refl


\end{code}
%</init-alg-impl>

%<*alg>
\begin{code}
record alg {-<-}{X : ISet α β} {->-}(γ : IIR X X) : Set (lsuc α ⊔ β) where
  constructor _,_
  field
    obj : 𝔽 X
    mor : ⟦ γ ⟧ obj ⇒ obj
open alg public
\end{code}
%</alg>

%<*cata>
\begin{code}
fold : {-<-}∀ {X} {γ : IIR X X} {->-}(φ : alg γ) {-<-}{s} {->-}→ μ γ {-<-}{s}{->-} ⇒ obj φ
mfold : {-<-}∀ {X} {γ : IIR X X} {->-}(φ : alg γ) {-<-}{s} {->-}→ μ γ {-<-}{s} {->-}⇒ ⟦ γ ⟧ (obj φ)

fold φ = mor φ ⊙ mfold φ
mfold {-<-}{γ = γ} {->-}φ i ⟨ x ⟩ = ⟦ γ ⟧[ fold φ ] i x

--mfold-comp : {-<-}∀ {X} {α : IIR X X} {->-}(φ : alg α) {-<-}{s : Size} {t : Size< s} {->-}→ mfold φ {-<-}{s} {->-}⊙ in' ≡ ⟦ α ⟧[ fold φ {-<-}{t} {->-}]
--mfold-comp φ = funext λ i → funext λ x → cong-Σ refl (uoip _ _)

--fold-comp : {-<-}∀ {X} {α : IIR X X} {->-}(φ : alg α) {-<-}{s : Size} {t : Size< s} {->-}→ fold φ {-<-}{s} {->-}⊙ in' ≡ mor φ ⊙ ⟦ α ⟧[ fold φ {-<-}{t} {->-}]
--fold-comp {-<-}{α = α} {->-}φ = trans (⊙-assoc{-<-}{f = in'} {g = mfold φ} {h = mor φ}{->-}) (cong (λ x → mor φ ⊙ x) (mfold-comp φ))
\end{code}
%</cata>


%<*ind-all>
\begin{code}
all :  {-<-}∀ {δ} {X : ISet α β} {->-} (γ : poly X) {-<-}{D : 𝔽 X}{->-} → (P : {-<-}{i : Code X} →{->-} Code (D i) → Set δ) → Code (⟦ γ ⟧ᵢ D) → Set (α ⊔ δ)
all (ι i)    P x        = Lift α (P x)
all (κ A)    P x        = ⊤
all (σ A B)  P (a , b)  = Σ (all A P a) λ _ → all (B (decode (⟦ A ⟧ᵢ _) a)) P b
all (π A B)  P f        = (a : A) → all (B a) P (f a)
\end{code}
%</ind-all>

%<*ind-everywhere>
\begin{code}
every :  {-<-}∀ {δ X} {->-}(γ : poly X) {-<-}{D : 𝔽 X}{->-} → (P : {-<-}{i : Code X} →{->-} Code (D i) → Set δ) →
         ({-<-}∀ {i}{->-} (x : Code (D i)) → P x) → (xs : Code (⟦ γ ⟧ᵢ D)) → all γ P xs
every (ι i)    _ p x        = lift $ p x
every (κ A)    P _ _        = *
every (σ A B)  P p (a , b)  = every A P p a , every (B (decode (⟦ A ⟧ᵢ _) a)) P p b
every (π A B)  P p f        = λ a → every (B a) P p (f a)
\end{code}
%</ind-everywhere>


%<*induction>
\begin{code}
induction :  {-<-}∀ {δ X} {->-}(γ : IIR X X) (P : {-<-}∀ {s i} →{->-} Code (μ γ {-<-}{s}{->-} i) → Set δ) →
             ({-<-}∀ {s} {t : Size< s} {i}{->-} (xs : Code (⟦ γ ⟧ (μ γ {-<-}{t}{->-}) i)) → all (node γ i) P xs → P (⟨_⟩ {-<-}{s = s}{->-} xs)) →
             {-<-}∀ {s i} {->-}(x : Code (μ γ {-<-}{s}{->-} i)) → P x
induction γ P p ⟨ xs ⟩ = p xs (every (node γ _) P (induction γ P p) xs)
\end{code}
%</induction>
