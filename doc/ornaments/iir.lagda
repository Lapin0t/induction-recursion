%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.iir {α β} where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
\end{code}


------------------------------------------------------------------------
-- Codes.


%<*codes>
\begin{code}
data poly (X : ISet α β) : Set (lsuc α ⊔ β)
info : {-<-}∀ {X} →{->-} poly X → Set (α ⊔ β)

data poly X where
  ι : Code X → poly X
  κ : (A : Set α) → poly X
  σ : (A : poly X) → (B : info A → poly X) → poly X
  π : (A : Set α) → (B : A → poly X) → poly X

info {-<-}{X} {->-}(ι i)      = Lift α (decode X i)
info (κ A)      = Lift β A
info (σ A B)    = Σ (info A) λ x → info (B x)
info (π A B)    = (a : A) → info (B a)
\end{code}
%</codes>



------------------------------------------------------------------------
-- Expression of IIR definitions as a functors.

%<*iir>
\begin{code}
record IIR (X Y : ISet α β) : Set (lsuc α ⊔ β) where
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
⟦_⟧ᵢ : {-<-}∀ {X} →{->-} (γ : poly X) → 𝔽 X → Fam α (info γ)
⟦ ι i    ⟧ᵢ F = lift >> F i
⟦ κ A    ⟧ᵢ F = A , lift
⟦ σ A B  ⟧ᵢ F = ornaments.fam.σ (⟦ A ⟧ᵢ F) λ a → ⟦ B a ⟧ᵢ F
⟦ π A B  ⟧ᵢ F = ornaments.fam.π A λ a → ⟦ B a ⟧ᵢ F
\end{code}
%</fam-info>

%<*fct-obj>
\begin{code}
⟦_⟧ : {-<-}∀ {X Y} →{->-} (γ : IIR X Y) → 𝔽 X → 𝔽 Y
⟦ γ ⟧ F j = emit γ j >> ⟦ node γ j ⟧ᵢ F
\end{code}
%</fct-obj>

%format Bᵢ = "\FCT{Bᵢ}"
%format aux-a = "\FCT{aux\!\!-\!\!a}"
%format aux-b = "\FCT{aux\!\!-\!\!b}"
%format aux = "\FCT{aux}"
%<*fct-hom-i>
\begin{code}
⟦_⟧[_]ᵢ : {-<-}∀ {X}{->-} (γ : poly X) {-<-}{F G : 𝔽 X}{->-} → F ⇒ G → ⟦ γ ⟧ᵢ F ⟶̃ ⟦ γ ⟧ᵢ G
⟦ ι i    ⟧[ φ ]ᵢ x = (lift <$>> φ i) $ x
⟦ κ A    ⟧[ φ ]ᵢ a = a , refl
⟦_⟧[_]ᵢ (σ A B) {F} {G} φ (a , b) = --σ→ (λ x → ⟦ B x ⟧ᵢ G) ⟦ A ⟧[ φ ]ᵢ (λ a → ⟦ B (decode (⟦ A ⟧ᵢ F) a) ⟧[ φ ]ᵢ) x
  let Bᵢ x = ⟦ B x ⟧ᵢ _ in
  let (a' , eqa) = ⟦ A ⟧[ φ ]ᵢ a in
  let (b' , eqb) = ⟦ B (decode (⟦ A ⟧ᵢ _) a) ⟧[ φ ]ᵢ b in
  (a' , subst (Code ∘ Bᵢ) (sym eqa) b') ,
  (cong-Σ eqa (trans (cong₂ (decode ∘ Bᵢ) eqa (subst-elim _ $ sym eqa)) eqb))
⟦ π A B  ⟧[ φ ]ᵢ = π→ λ a → ⟦ B a ⟧[ φ ]ᵢ
\end{code}
%</fct-hom-i>

%<*fct-hom>
\begin{code}
⟦_⟧[_] : {-<-}∀ {X Y}{->-} (γ : IIR X Y) {-<-}{F G : 𝔽 X}{->-} → F ⇒ G → ⟦ γ ⟧ F ⇒ ⟦ γ ⟧ G
⟦ γ ⟧[ φ ] j = emit γ j <$>> ⟦ node γ j ⟧[ φ ]ᵢ
\end{code}
%</fct-hom>


------------------------------------------------------------------------
-- Composition of Codes

\begin{code}
module composition where
\end{code}

%<*iir-star>
\begin{code}
  --IIR* : ISet ? (lsuc α) → Set (lsuc α) → Set (lsuc α)
  --IIR* X Y = Σ (poly X) λ n → info n → Y
\end{code}
%</iir-star>

%<*iir-eta>
\begin{code}
  --eta : {-<-}∀ {X Y} →{->-} Y → IIR* X Y
  --eta y = κ ? , λ _ → y
\end{code}
%</iir-eta>

%<*iir-mu>
\begin{code}
  --mu : {-<-}∀ {X Y} →{->-} IIR* X (IIR* X Y) → IIR* X Y
  --mu (n₀ , e₀) = σ n₀ (λ z → π₀ (e₀ z)) , λ { (n₁ , e₁) → π₁ (e₀ n₁) e₁ }
\end{code}
%</iir-mu>

%format pow = "\FCT{pow}"

%<*iir-pow>
\begin{code}
  --pow : {-<-}∀ {X}{->-} (A : Set α) {-<-}{B : A → Set (lsuc α)}{->-} → ((a : A) → IIR* X (B a)) →
  --  IIR* X ((a : A) → B a)
  --pow A f = π A (π₀ ∘ f) , λ z a → π₁ (f a) (z a)
\end{code}
%</iir-pow>

%<*iir-bind>
\begin{code}
  --_>>=_ : {-<-}∀ {C D E} →{->-} IIR* C D → ((x : D) → IIR* C (E x)) → IIR* C (Σ D E)
  --(n , e) >>= h = mu (n , λ x → π₀ (h (e x)) , λ y → e x , π₁ (h (e x)) y)
\end{code}
%</iir-bind>

%<*iir-subst>
\begin{code}
  {-_/_ : {-<-}∀ {X Y} →{->-} (p : poly Y) → IIR X Y → IIR* X (info p)
  ι i    / R = (node R i , emit R i)
  κ A    / R = (κ A , λ a → a)
  σ A B  / R = (A / R) >>= (λ a → B a / R)
  π A B  / R = pow A (λ a → B a / R)-}
\end{code}
%</iir-subst>

%<*iir-comp>
\begin{code}
  --_•_ : {-<-}∀ {X Y Z} →{->-} IIR Y Z → IIR X Y → IIR X Z
  --node  (γ • R) j = π₀ (node γ j / R)
  --emit  (γ • R) j = emit γ j ∘ π₁ (node γ j / R)
\end{code}
%</iir-comp>
