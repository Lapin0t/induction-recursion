%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.iir where

open import ornaments.prelude
open import ornaments.fam renaming (σ to f-σ; π to f-π; σ→ to f-σ→; π→ to f-π→)

variable
  {α} : Level  -- level of the index set
  {β} : Level  -- level of the output set
  {γ} : Level  -- level of the code set
  {δ ε} : Level
  {X Y} : ISet α β
\end{code}


------------------------------------------------------------------------
-- Codes.

%<*codes>
\begin{code}
data poly {-<-}{α β}{->-}(γ : Level) (X : ISet α β) : Set (lsuc α ⊔ β ⊔ lsuc γ)
info : {X : ISet α β} → poly γ X → Set (β ⊔ γ)

data poly γ X where
  ι : Code X → poly γ X
  κ : (A : Set γ) → poly γ X
  σ : (A : poly γ X) (B : info A → poly γ X) → poly γ X
  π : (A : Set γ) (B : A → poly γ X) → poly γ X

info {-<-}{γ = γ}{X}{->-}(ι i)      = Lift γ (decode X i)
info {-<-}{β = β}{->-}(κ A)      = Lift β A
info (σ A B)    = Σ (info A) λ x → info (B x)
info (π A B)    = (a : A) → info (B a)
\end{code}
%</codes>



------------------------------------------------------------------------
-- Expression of IIR definitions as a functors.

%<*iir>
\begin{code}
record IIR {-<-}{α β}{->-}(γ : Level) (X Y : ISet α β) : Set (lsuc α ⊔ β ⊔ lsuc γ) where
  constructor _,_
  field
    node : (j : Code Y) → poly γ X
    emit : (j : Code Y) → info (node j) → decode Y j
\end{code}
%</iir>

\begin{code}
open IIR public
\end{code}

%<*fam-info>
\begin{code}
⟦_⟧₀ : (ρ : poly γ X) → 𝔽 δ X → Fam (γ ⊔ δ) (info ρ)
⟦_⟧₀ {γ = γ} (ι i) F = lift >> lft γ F i
⟦_⟧₀ {δ = δ} (κ A) F = Lift δ A , lift ∘ lower
⟦ σ A B  ⟧₀ F = f-σ (⟦ A ⟧₀ F) λ a → ⟦ B a ⟧₀ F
⟦ π A B  ⟧₀ F = f-π A λ a → ⟦ B a ⟧₀ F
\end{code}
%</fam-info>

%<*fct-obj>
\begin{code}
⟦_⟧ : IIR γ X Y → 𝔽 δ X → 𝔽 (γ ⊔ δ) Y
⟦ ρ ⟧ F = λ j → emit ρ j >> ⟦ node ρ j ⟧₀ F
\end{code}
%</fct-obj>

%<*fct-hom-i>
\begin{code}
⟦_⟧[_]₀ : (ρ : poly γ X){-<-}{F : 𝔽 δ X}{G : 𝔽 ε X}{->-} → F ⇒ G → ⟦ ρ ⟧₀ F ⟶̃ ⟦ ρ ⟧₀ G
⟦ ι i    ⟧[ φ ]₀ = λ x → (lift $ π₀ $ φ i (lower x)) , cong lift $ π₁ $ φ i (lower x)
⟦ κ A    ⟧[ φ ]₀ = λ a → lift $ lower a , refl
⟦ σ A B  ⟧[ φ ]₀ = f-σ→ (λ a → ⟦ B a ⟧₀ _) (λ a → ⟦ B a ⟧₀ _) ⟦ A ⟧[ φ ]₀
                        (λ a → ⟦ B $ decode (⟦ A ⟧₀ _) a ⟧[ φ ]₀)
⟦ π A B  ⟧[ φ ]₀ = f-π→ λ a → ⟦ B a ⟧[ φ ]₀
\end{code}
%</fct-hom-i>

%<*fct-hom>
\begin{code}
⟦_⟧[_] : (ρ : IIR γ X Y) {-<-}{F : 𝔽 δ X}{G : 𝔽 ε X}{->-} → F ⇒ G → ⟦ ρ ⟧ F ⇒ ⟦ ρ ⟧ G
⟦ ρ ⟧[ φ ] j = emit ρ j <$>> ⟦ node ρ j ⟧[ φ ]₀
\end{code}
%</fct-hom>


------------------------------------------------------------------------
-- Composition of Codes

\begin{code}
module composition where
\end{code}

%<*iir-star>
\begin{code}
  IIR* : (γ : Level) → ISet α β → Set β → Set (lsuc α ⊔ β ⊔ lsuc γ)
  IIR* γ X Y = Σ (poly γ X) λ n → info n → Y
\end{code}
%</iir-star>

%<*iir-eta>
\begin{code}
  eta : ∀ {Y} → Y → IIR* γ X Y
  eta y = κ ⊤ , λ _ → y
\end{code}
%</iir-eta>

%<*iir-mu>
\begin{code}
  mu : ∀ {X : ISet α (lsuc α ⊔ β ⊔ lsuc γ)} {Y} → IIR* γ X (IIR* γ X Y) → IIR* γ X Y
  mu (p , e) = σ p (λ x → π₀ (e x)) , λ { (x , y) → π₁ (e x) y }
\end{code}
%</iir-mu>

%format pow = "\FCT{pow}"

%<*iir-pow>
\begin{code}
  pow : {X : ISet α (α ⊔ β)} (A : Set α) {B : A → Set (α ⊔ β)} → ((a : A) → IIR* (α ⊔ γ) X (B a)) → IIR* (α ⊔ γ) X ((a : A) → B a)
  pow {γ = γ} A ρ = π (Lift γ A) (π₀ ∘ ρ ∘ lower) , λ z a → π₁ (ρ a) (z $ lift a)
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
