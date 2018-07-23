%include agda.fmt
%include ornaments.fmt

\begin{code}
{--# OPTIONS --experimental-irrelevance #-}
module ornaments.induction where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.iir hiding (α; β; γ; δ; ε; X; Y)

variable
  {α β γ δ ε} : Level
  {X} : ISet α β
  ..{s} : Size
--  .{t} : Size< s
\end{code}


------------------------------------------------------------------------
-- Initial algebra and Code interpretation

%<*init-alg-def>
\begin{code}

μ : (ρ : IIR γ X X) ..{s : Size} → 𝔽 γ X

{-# NO_POSITIVITY_CHECK #-}
data μ-c {α β γ} {X : ISet α β} (ρ : IIR γ X X) ..{s : Size} (i : Code X) : Set γ where
  ⟨_⟩ : ..{t : Size< s} → Code (⟦ ρ ⟧ (μ ρ {t}) i) → μ-c ρ {s} i

μ-d : (ρ : IIR γ X X) (i : Code X) → μ-c ρ {s} i → decode X i
μ-d ρ i ⟨ x ⟩ = decode (⟦ ρ ⟧ (μ ρ) i) x

Code (μ ρ {s} i) = μ-c ρ {s} i
decode (μ ρ i) = μ-d ρ i


--.μ-sz : {ρ : IIR γ X X} {s : _} {i : _} → μ-c ρ {s} i → Size< s
--μ-sz (⟨_⟩ {t} _) = irr-ax t

roll : {ρ : IIR γ X X} ..{s : Size} ..{t : Size< s} → ⟦ ρ ⟧ (μ ρ {t}) ⇒ μ ρ {s}
roll _ x = ⟨ x ⟩ , refl

--uroll : {X : ISet α β} {ρ : IIR X X} .{s : Size} .{t : Size} → μ ρ {s} ⇒ ⟦ ρ ⟧ (μ ρ {t})
--uroll _ ⟨ x ⟩ = x , refl

--unroll : {ρ : IIR γ X X} {F : 𝔽 γ X} → ({t : Size< s} → ⟦ ρ ⟧ (μ ρ {t}) ⇒ F) → μ ρ {s} ⇒ F
--unroll f i ⟨ x ⟩ = f i x
--unroll : {X : ISet α β} {ρ : IIR X X} {s : _} → μ ρ {s} ⇒ ⟦ ρ ⟧ (μ ρ {s})
--unroll _ ⟨ x ⟩ = {! x  !} , {!   !}

{-module _ {X : ISet α β} (ρ : IIR X X) where

  c⟦_⟧ : poly X → Set α
  d⟦_⟧ : (τ : poly X) → c⟦ τ ⟧ → info τ

  data μ-c (τ : poly X) : Set α where
    ⟨_⟩ : c⟦ τ ⟧ → μ-c τ

  μ-d : (i : Code X) → μ-c (node ρ i) → decode X i
  μ-d i ⟨ x ⟩ = emit ρ i $ d⟦ node ρ i ⟧ x

  c⟦ ι i   ⟧ = μ-c (node ρ i)
  c⟦ κ A   ⟧ = A
  c⟦ σ A B ⟧ = Σ c⟦ A ⟧ λ a → c⟦ B (d⟦ A ⟧ a) ⟧
  c⟦ π A B ⟧ = (a : A) → c⟦ B a ⟧

  d⟦ ι i   ⟧ x = lift $ μ-d i x
  d⟦ κ A   ⟧ x = lift x
  d⟦ σ A B ⟧ x = d⟦ A ⟧ (π₀ x) , d⟦ B _ ⟧ (π₁ x)
  d⟦ π A B ⟧ x = λ a → d⟦ B a ⟧ (x a)

  μ : 𝔽 X
  μ i = μ-c (node ρ i) , μ-d i

  --eq₀ : (τ : poly X) → (x : c⟦ τ ⟧) → Σ (Code (⟦ τ ⟧ᵢ μ)) λ y → decode (⟦ τ ⟧ᵢ μ) y ≡ d⟦ τ ⟧ x
  eq₀ : (τ : poly X) → c⟦ τ ⟧ ≡ Code (⟦ τ ⟧ᵢ μ)
  eq₁ : (τ : poly X) → d⟦ τ ⟧ ≡ decode (⟦ τ ⟧ᵢ μ)

  eq₀ (ι i) = refl
  eq₀ (κ A) = refl
  eq₀ (σ A B) with ⟦ A ⟧ᵢ μ | eq₀ A | eq₁ A
  eq₀ (σ A B) | _ | refl | refl = cong (Σ c⟦ A ⟧) (funext λ a → eq₀ (B (d⟦ A ⟧ a)))
  eq₀ (π A B) = cong (λ f → (a : A) → f a) (funext λ a → eq₀ (B a))

  eq₁ (ι i) = refl
  eq₁ (κ A) = refl
  eq₁ (σ A B) = ?
  eq₁ (π A B) = funext₁ (eq₀ (π A B)) λ x → funext λ a → {! eq₁ (B a)  !}

  {-eq₀ (ι i) x = x , refl --x
  eq₀ (κ A) x = x , refl --x
  eq₀ (σ A B) x =
    let B' x = ⟦ B x ⟧ᵢ μ in
    let a , p = eq₀ A (π₀ x) in
    let b , q = eq₀ (B _) (π₁ x) in
    (a , subst (Code ∘ B') (sym p) b) ,
    cong-Σ p (trans (cong₂ (decode ∘ B') p (subst-elim _ $ sym p)) q)
  eq₀ (π A B) x = (λ a → π₀ $ eq₀ (B a) (x a)) , (funext (λ a → π₁ $ eq₀ (B a) (x a)))
  --eq₁ : {τ : poly X} (x : c⟦ τ ⟧) → d⟦ τ ⟧ x ≡ decode (⟦ τ ⟧ᵢ μ) (subst (λ s → s) (eq₀ {τ}) x)-}

  --eq₀ {ι i} = refl
  --eq₀ {κ A} = refl
  --eq₀ {σ A B} = cong₂ Σ (eq₀ {A}) (funext₁ (eq₀ {A}) λ x → {! cong ()  !})
  --eq₀ {π A B} = cong (λ x → (a : A) → x a) (funext (λ a → eq₀ {B a}))

  --eq₁ {ι i} x = refl
  --eq₁ {κ A} x = refl
  --eq₁ {σ A B} = {!   !}
  --eq₁ {π A B} x = funext (λ a → {! eq₁ {B a} (x a) !})-}

--μ : {-<-}{X : ISet α β} →{->-} IIR X X → 𝔽 X

--data μ-c {-<-}{X : ISet α β}{->-} (γ : IIR X X) (i : Code X) : Set α

--μ-d : {-<-}{X : ISet α β} →{->-} (γ : IIR X X) → {-<-}{s : Size} → {->-}(i : Code X) → μ-c γ {-<-}{s}{->-} i → decode X i

--Code    (μ γ {-<-}{s}{->-} i)  = μ-c γ {-<-}{s}{->-} i
--decode  (μ γ i)  = μ-d γ i

\end{code}
%</init-alg-def>


%<*init-alg-impl>
\begin{code}
--data μ-c γ i where
--  ⟨_⟩ : C⟦ γ ⟧μ i (μ γ {-<-}{t}{->-}) i) → μ-c γ i

--μ-d γ i ⟨ c ⟩ = emit γ i (decode (⟦ node γ i ⟧ᵢ (μ γ)) c)

--roll : {-<-}∀ {X} {γ : IIR X X} {s} {t : Size< s} → {->-}⟦ γ ⟧ (μ γ{-<-}{t}{->-}) ⇒ μ γ{-<-}{s}{->-}
--roll i x = ⟨ x ⟩ , refl

--unroll : ∀ {X} {γ : IIR X X} → μ γ ⇒ ⟦ γ ⟧ (μ γ)
--unroll ⟨ x ⟩ = x , refl

--unroll-c : ∀ {X} {γ : IIR X X} {s : Size} {_ : Size< s} (i : Code X) → μ-c γ {s} i → Σ (Size< s) (λ t → Code (⟦ γ ⟧ (μ γ {t}) i))
--unroll-c _ ⟨ x ⟩ = _ , x

--unroll-d : ∀ {X} {γ : IIR X X} {s} {_ : Size< s} (i : Code X) → (x : μ-c γ {s} i) → μ-d γ i x ≡ decode (⟦ γ ⟧ (μ γ) i) (π₁ $ unroll-c i x)
--unroll-d _ ⟨ _ ⟩ = refl


\end{code}
%</init-alg-impl>

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

fold {ρ = ρ} φ = mor φ ⊙ foldm φ
foldm {ρ = ρ} φ i ⟨ x ⟩ = ⟦ ρ ⟧[ fold φ ] i x


--mfold-comp : {-<-}∀ {X} {α : IIR X X} {->-}(φ : alg α) {-<-}{s : Size} {t : Size< s} {->-}→ mfold φ {-<-}{s} {->-}⊙ in' ≡ ⟦ α ⟧[ fold φ {-<-}{t} {->-}]
--mfold-comp φ = funext λ i → funext λ x → cong-Σ refl (uoip _ _)

--fold-comp : {-<-}∀ {X} {α : IIR X X} {->-}(φ : alg α) {-<-}{s : Size} {t : Size< s} {->-}→ fold φ {-<-}{s} {->-}⊙ in' ≡ mor φ ⊙ ⟦ α ⟧[ fold φ {-<-}{t} {->-}]
--fold-comp {-<-}{α = α} {->-}φ = trans (⊙-assoc{-<-}{f = in'} {g = mfold φ} {h = mor φ}{->-}) (cong (λ x → mor φ ⊙ x) (mfold-comp φ))
\end{code}
%</cata>


%<*ind-all>
\begin{code}
all : {-<-}{X : ISet α β}{->-}(ρ : poly γ X){-<-}{F : 𝔽 ε X}{->-} (P : {i : Code X} → Code (F i) → Set δ) → Code (⟦ ρ ⟧₀ F) → Set (α ⊔ γ ⊔ δ)
all {-<-}{α = α}{γ = γ}{->-}(ι i)    P (lift x)        = Lift (α ⊔ γ) (P x)
all (κ A)    P x        = ⊤
all (σ A B)  P (a , b)  = Σ (all A P a) λ _ → all (B (decode (⟦ A ⟧₀ _) a)) P b
all (π A B)  P f        = (a : A) → all (B a) P (f a)
\end{code}
%</ind-all>

%<*ind-everywhere>
\begin{code}
every :  (ρ : poly γ X) {-<-}{D : 𝔽 ε X}{->-} → (P : {i : Code X} → Code (D i) → Set δ) →
         ({i : Code X} (x : Code (D i)) → P x) → (xs : Code (⟦ ρ ⟧₀ D)) → all ρ P xs
every (ι i)    _ p (lift x) = lift $ p x
every (κ A)    P _ _        = *
every (σ A B)  P p (a , b)  = every A P p a , every (B (decode (⟦ A ⟧₀ _) a)) P p b
every (π A B)  P p f        = λ a → every (B a) P p (f a)
\end{code}
%</ind-everywhere>


%<*induction>
\begin{code}
induction :  (ρ : IIR γ X X) (P : {-<-}..{s : Size}{i : Code X} → {->-}Code (μ ρ {s} i) → Set δ)
             (p : {-<-}..{s : Size}..{t : Size< s}{i : Code X}{->-}(xs : Code (⟦ ρ ⟧ (μ ρ {t}) i)) → all (node ρ i) P xs → P (⟨_⟩ {s = s} xs)) →
             {-<-}..{s : Size}{i : Code X}{->-}(x : Code (μ ρ {s} i)) → P x
induction ρ P p ⟨ x ⟩ = p x (every (node ρ _) P (induction ρ P p) x)
\end{code}
%</induction>
