%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.iir where

open import Agda.Builtin.TrustMe using (primTrustMe)
open import ornaments.prelude
open import ornaments.fam using (Fam; Code; decode; _,_; 𝔽; _>>_; _⇒_; _⟶̃_)
\end{code}


------------------------------------------------------------------------
-- Codes.


%<*codes>
\begin{code}
data poly (X : Fam Set₁) : Set₁
info : {-<-}{X : Fam Set₁} →{->-} poly X → Set₁

data poly X where
  ι : Code X → poly X
  κ : (A : Set) → poly X
  σ : (A : poly X) → (B : info A → poly X) → poly X
  π : (A : Set) → (B : A → poly X) → poly X

info {-<-}{X} {->-}(ι i)      = decode X i
info (κ A)      = Lift A
info (σ A B)    = Σ (info A) λ x → info (B x)
info (π A B)    = (a : A) → info (B a)
\end{code}
%</codes>



------------------------------------------------------------------------
-- Expression of IIR definitions as a functors.

%<*iir>
\begin{code}
record IIR (X Y : Fam Set₁) : Set₁ where
  constructor _,_
  field
    node : (j : Code Y) → poly X
    emit : (j : Code Y) → info (node j) → decode Y j
\end{code}
%</iir>
\begin{code}
open IIR public
\end{code}


%<*fam-info>
\begin{code}
⟦_⟧ᵢ : {-<-}∀ {X} →{->-} (γ : poly X) → 𝔽 X → Fam (info γ)
⟦ ι i    ⟧ᵢ F = F i
⟦ κ A    ⟧ᵢ F = (A , lift)
⟦ σ A B  ⟧ᵢ F = ornaments.fam.σ (⟦ A ⟧ᵢ F) λ a → ⟦ B a ⟧ᵢ F
⟦ π A B  ⟧ᵢ F = ornaments.fam.π A λ a → ⟦ B a ⟧ᵢ F
\end{code}
%</fam-info>

%<*fct-obj>
\begin{code}
⟦_⟧ : {-<-}{X Y : Fam Set₁} →{->-} (α : IIR X Y) → 𝔽 X → 𝔽 Y
⟦ α ⟧ F j = emit α j >> ⟦ node α j ⟧ᵢ F
\end{code}
%</fct-obj>

%format Bᵢ = "\FCT{Bᵢ}"
%format aux-a = "\FCT{aux\!\!-\!\!a}"
%format aux-b = "\FCT{aux\!\!-\!\!b}"
%format aux = "\FCT{aux}"
%<*fct-hom-i>
\begin{code}
⟦_⟧[_]ᵢ : {-<-}∀ {X}{->-} (p : poly X) {-<-}{F G : 𝔽 X}{->-} → F ⇒ G → ⟦ p ⟧ᵢ F ⟶̃ ⟦ p ⟧ᵢ G
⟦ ι i    ⟧[ φ ]ᵢ = φ i
⟦ κ A    ⟧[ φ ]ᵢ = (λ a → a) , (λ _ → refl)
⟦ σ A B  ⟧[ φ ]ᵢ =
  (λ { (a , b) →
         π₀ aux-a a ,
         subst (Code ∘ Bᵢ) (sym (π₁ aux-a a)) (π₀ (aux-b a) b) }) ,
  (λ { (a , b) → cong-Σ
         (π₁ aux-a a)
         (trans (cong₂ (decode ∘ Bᵢ) (π₁ aux-a a) (subst-elim _ (sym (π₁ aux-a a))))
                (π₁ (aux-b a) b)) })
  where
    Bᵢ : (x : _) → Fam (info (B x))
    Bᵢ x = ⟦ B x ⟧ᵢ _

    aux-a : ⟦ A ⟧ᵢ _ ⟶̃ ⟦ A ⟧ᵢ _
    aux-a = ⟦ A ⟧[ φ ]ᵢ

    aux-b : (a : _) → ⟦ B _ ⟧ᵢ _ ⟶̃ ⟦ B _ ⟧ᵢ _
    aux-b a = ⟦ B (decode (⟦ A ⟧ᵢ _) a) ⟧[ φ ]ᵢ

⟦ π A B  ⟧[ φ ]ᵢ = (S (π₀ ∘ aux) , funext ∘ (S (π₁ ∘ aux)))
  where aux : (a : A) → ⟦ B a ⟧ᵢ _ ⟶̃ ⟦ B a ⟧ᵢ _
        aux a = ⟦ B a ⟧[ φ ]ᵢ
\end{code}
%</fct-hom-i>

%<*fct-hom>
\begin{code}
⟦_⟧[_] : {-<-}∀ {X Y}{->-} (α : IIR X Y) {-<-}{F G : 𝔽 X}{->-} → F ⇒ G → ⟦ α ⟧ F ⇒ ⟦ α ⟧ G
⟦ α ⟧[ φ ] j = π₀ ⟦ node α j ⟧[ φ ]ᵢ , cong (emit α j) ∘ (π₁ ⟦ node α j ⟧[ φ ]ᵢ)
\end{code}
%</fct-hom>


------------------------------------------------------------------------
-- Initial algebra and Code interpretation

%<*init-alg-def>
\begin{code}
μ : {-<-}∀ {X} →{->-} IIR X X → {-<-}{_ : Size} →{->-} 𝔽 X

{-<-}
{-# NO_POSITIVITY_CHECK #-}
{->-}
data μ-C {-<-}{X}{->-} (α : IIR X X) {-<-}{s : Size}{->-} (i : Code X) : Set

μ-d : {-<-}∀ {X} →{->-} (α : IIR X X) {-<-}→ {s : Size}{->-} → (i : Code X) → μ-C α {-<-}{s}{->-} i → decode X i

Code    (μ α {-<-}{s}{->-} i)  = μ-C α {-<-}{s}{->-} i
decode  (μ α i)  = μ-d α i
\end{code}
%</init-alg-def>


%<*init-alg-impl>
\begin{code}
data μ-C α {-<-}{s}{->-} i where
  ⟨_⟩ : {-<-}∀ {t : Size< s} →{->-} Code (⟦ α ⟧ (μ α {-<-}{t}{->-}) i) → μ-C α i

μ-d α i ⟨ c ⟩ = emit α i (decode (⟦ node α i ⟧ᵢ (μ α)) c)
\end{code}
%</init-alg-impl>

%format mfold = "\FCT{mfold}"
%<*cata>
\begin{code}
fold : {-<-}∀ {X s}{->-} (α : IIR X X) {-<-}{F : 𝔽 X}{->-} → ⟦ α ⟧ F ⇒ F → μ α {-<-}{s}{->-} ⇒ F
π₀ (fold α φ i) ⟨ x ⟩ = π₀ (φ i) (π₀ (⟦ α ⟧[ fold α φ ] i) x)
π₁ (fold α φ i) ⟨ x ⟩ = trans (π₁ (φ i) (π₀ mfold x)) (π₁ mfold x)
  where
    mfold : _
    mfold = ⟦ α ⟧[ fold α φ ] i
\end{code}
%</cata>


------------------------------------------------------------------------
-- Composition of Codes

\begin{code}
module composition where
\end{code}

%<*iir-star>
\begin{code}
  IIR* : Fam Set₁ → Set₁ → Set₁
  IIR* X Y = Σ (poly X) λ n → info n → Y
\end{code}
%</iir-star>

%<*iir-eta>
\begin{code}
  eta : {-<-}∀ {X Y} →{->-} Y → IIR* X Y
  eta y = κ ⊤ , λ _ → y
\end{code}
%</iir-eta>

%<*iir-mu>
\begin{code}
  mu : {-<-}∀ {X Y} →{->-} IIR* X (IIR* X Y) → IIR* X Y
  mu (n₀ , e₀) = σ n₀ (λ z → π₀ (e₀ z)) , λ { (n₁ , e₁) → π₁ (e₀ n₁) e₁ }
\end{code}
%</iir-mu>

%format pow = "\FCT{pow}"

%<*iir-pow>
\begin{code}
  pow : {-<-}∀ {X}{->-} (A : Set) {-<-}{B : A → Set₁}{->-} → ((a : A) → IIR* X (B a)) →
    IIR* X ((a : A) → B a)
  pow A f = π A (π₀ ∘ f) , λ z a → π₁ (f a) (z a)
\end{code}
%</iir-pow>

%<*iir-bind>
\begin{code}
  _>>=_ : {-<-}∀ {C D E} →{->-} IIR* C D → ((x : D) → IIR* C (E x)) → IIR* C (Σ D E)
  (n , e) >>= h = mu (n , λ x → π₀ (h (e x)) , λ y → e x , π₁ (h (e x)) y)
\end{code}
%</iir-bind>

%<*iir-subst>
\begin{code}
  _/_ : {-<-}∀ {X Y} →{->-} (p : poly Y) → IIR X Y → IIR* X (info p)
  ι i    / R = (node R i , emit R i)
  κ A    / R = (κ A , λ a → a)
  σ A B  / R = (A / R) >>= (λ a → B a / R)
  π A B  / R = pow A (λ a → B a / R)
\end{code}
%</iir-subst>

%<*iir-comp>
\begin{code}
  _⊙'_ : {-<-}∀ {X Y Z} →{->-} IIR Y Z → IIR X Y → IIR X Z
  node  (γ ⊙' R) j = π₀ (node γ j / R)
  emit  (γ ⊙' R) j = emit γ j ∘ π₁ (node γ j / R)
\end{code}
%</iir-comp>

\begin{code}
module induction where
\end{code}

%<*ind-all>
\begin{code}
  all :  {-<-} ∀ {X} {->-} (γ : poly X) {-<-}{D : 𝔽 X}{->-} → (P : {-<-}{i : Code X} →{->-} Code (D i) → Set) → Code (⟦ γ ⟧ᵢ D) → Set
  all (ι i)    P x        = P x
  all (κ A)    P x        = ⊤
  all (σ A B)  P (a , b)  = Σ (all A P a) λ _ → all (B (decode (⟦ A ⟧ᵢ _) a)) P b
  all (π A B)  P f        = (a : A) → all (B a) P (f a)
\end{code}
%</ind-all>

%<*ind-everywhere>
\begin{code}
  every :  {-<-}∀ {X} {->-}(γ : poly X) {-<-}{D : 𝔽 X}{->-} → (P : {-<-}{i : Code X} →{->-} Code (D i) → Set) →
           ({-<-}∀ {i}{->-} (x : Code (D i)) → P x) → (xs : Code (⟦ γ ⟧ᵢ D)) → all γ P xs
  every (ι i)    _ p x        = p x
  every (κ A)    P _ _        = *
  every (σ A B)  P p (a , b)  = every A P p a , every (B (decode (⟦ A ⟧ᵢ _) a)) P p b
  every (π A B)  P p f        = λ a → every (B a) P p (f a)
\end{code}
%</ind-everywhere>


%<*induction>
\begin{code}
  induction :  {-<-}∀ {X} {->-}(γ : IIR X X) (P : {-<-}∀ {s i} →{->-} Code (μ γ {-<-}{s}{->-} i) → Set) →
               ({-<-}∀ {s} {t : Size< s} {i}{->-} (xs : Code (⟦ γ ⟧ (μ γ {-<-}{t}{->-}) i)) → all (node γ i) P xs → P (⟨_⟩ {-<-}{s = s}{->-} xs)) →
               {-<-}∀ {s i} {->-}(x : Code (μ γ {-<-}{s}{->-} i)) → P x
  induction γ P p ⟨ xs ⟩ = p xs (every (node γ _) P (induction γ P p) xs)
\end{code}
%</induction>
