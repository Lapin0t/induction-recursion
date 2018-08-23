%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.induction where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.iir hiding (α; β; γ; δ; ε; X; Y)

variable
  {α β γ δ ε} : Level
  {X} : ISet α β
  ..{s} : Size
\end{code}


------------------------------------------------------------------------
-- Initial algebra and Code interpretation

%<*init-alg>
\begin{code}
μ : (ρ : IIR γ X X) {-<-}..{s : Size}{->-}→ 𝔽 γ X
{-<-}
{-# NO_POSITIVITY_CHECK #-}
{->-}
data μ-c {-<-}{α β γ} {X : ISet α β}{->-}(ρ : IIR γ X X){-<-}..{s : Size}{->-}(i : Code X) : Set γ where
  ⟨_⟩ : {-<-}..{t : Size< s} →{->-}Code (⟦ ρ ⟧ (μ ρ{-<-}{t}{->-}) i) → μ-c ρ {-<-}{s}{->-}i

μ-d : (ρ : IIR γ X X) (i : Code X) → μ-c ρ {-<-}{s}{->-}i → decode X i
μ-d ρ i ⟨ x ⟩ = decode (⟦ ρ ⟧ (μ ρ) i) x

Code (μ ρ {-<-}{s}{->-}i) = μ-c ρ {-<-}{s}{->-}i
decode (μ ρ i) = μ-d ρ i
\end{code}
%</init-alg>

%<*init-alg-in>
\begin{code}
roll : {-<-}{ρ : IIR γ X X} ..{s : Size} ..{t : Size< s} → {->-}⟦ ρ ⟧ (μ ρ{-<-}{t}{->-}) ⇒ μ ρ{-<-}{s}{->-}
roll _ x = ⟨ x ⟩ , refl
\end{code}
%</init-alg-in>



%<*alg>
\begin{code}
record alg {-<-}{α β γ} (δ : Level) {X : ISet α β}{->-}(ρ : IIR γ X X) : Set (α ⊔ β ⊔ lsuc δ ⊔ γ) where
  constructor _,_
  field
    obj : 𝔽 δ X
    mor : ⟦ ρ ⟧ obj ⇒ obj
open alg public
\end{code}
%</alg>

%<*cata>
\begin{code}
fold : {-<-}{ρ : IIR γ X X}{->-}(φ : alg δ ρ) → μ ρ {-<-}{s}{->-}⇒ obj φ
foldm : {-<-}{ρ : IIR γ X X}{->-}(φ : alg δ ρ) → μ ρ {-<-}{s}{->-}⇒ ⟦ ρ ⟧ (obj φ)

fold φ = mor φ ⊙ foldm φ
foldm {ρ = ρ} φ i ⟨ x ⟩ = ⟦ ρ ⟧[ fold φ ] i x
\end{code}
%</cata>


%<*cata-prop>
\begin{code}
foldm-⊙ : {-<-}{ρ : IIR γ X X} {->-}(φ : alg δ ρ) {-<-}..{s : Size} ..{t : Size< s}{->-}→ foldm {-<-}{s = s}{->-}φ ⊙ roll {-<-}{ρ = ρ} {s} {t}{->-}≡ ⟦ ρ ⟧[ fold {-<-}{s = t}{->-}φ ]
foldm-⊙ φ = funext (λ i → funext (λ x → cong-Σ refl (uoip _ _)))

fold-⊙ : {-<-}{ρ : IIR γ X X} {->-}(φ : alg δ ρ) {-<-}..{s : Size} ..{t : Size< s} {->-}→ fold {-<-}{s = s}{->-}φ ⊙ roll {-<-}{ρ = ρ} {s} {t}{->-}≡ mor φ ⊙ ⟦ ρ ⟧[ fold {-<-}{s = t}{->-}φ ]
fold-⊙ φ = trans {-<-}({->-}⊙-assoc{-<-}{f = roll} {g = foldm φ} {h = mor φ}){->-} (cong (_⊙_ $ mor φ) (foldm-⊙ φ))
\end{code}
%</cata-prop>


%<*ind-all>
\begin{code}
all : {-<-}{X : ISet α β}{->-}(ρ : poly γ X){-<-}{F : 𝔽 ε X}{->-} (P : {i : Code X} → Code (F i) → Set δ) → Code (⟦ ρ ⟧₀ F) → Set (α ⊔ γ ⊔ δ)
all {-<-}{α = α}{γ = γ}{->-}(ι i)    P (lift x)        = Lift (α ⊔ γ) (P x)
all (κ A)    P x        = ⊤
all (σ A B)  P (a , b)  = Σ (all A P a) λ _ → all (B (decode (⟦ A ⟧₀ _) a)) P b
all (π A B)  P f        = (a : A) → all (B a) P (f a)
\end{code}
%</ind-all>

%<*ind-every>
\begin{code}
every :  (ρ : poly γ X) {-<-}{D : 𝔽 ε X}{->-} → (P : {i : Code X} → Code (D i) → Set δ) →
         ({i : Code X} (x : Code (D i)) → P x) → (xs : Code (⟦ ρ ⟧₀ D)) → all ρ P xs
every (ι i)    _ p (lift x) = lift $ p x
every (κ A)    P _ _        = *
every (σ A B)  P p (a , b)  = every A P p a , every (B (decode (⟦ A ⟧₀ _) a)) P p b
every (π A B)  P p f        = λ a → every (B a) P p (f a)
\end{code}
%</ind-every>


%<*induction>
\begin{code}
induction :  (ρ : IIR γ X X) (P : {-<-}..{s : Size}{i : Code X} → {->-}Code (μ ρ {s} i) → Set δ)
             (p : {-<-}..{s : Size}..{t : Size< s}{i : Code X}{->-}(xs : Code (⟦ ρ ⟧ (μ ρ {t}) i)) → all (node ρ i) P xs → P (⟨_⟩ {s = s} xs)) →
             {-<-}..{s : Size}{i : Code X}{->-}(x : Code (μ ρ {s} i)) → P x
induction ρ P p ⟨ x ⟩ = p x (every (node ρ _) P (induction ρ P p) x)
\end{code}
%</induction>
