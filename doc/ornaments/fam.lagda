%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.fam where
open import ornaments.prelude
\end{code}


%<*fam-def>
\begin{code}
record Fam {-<-}{α}{->-} (X : Set α) : Set (lsuc lzero ⊔ α) where
  constructor _,_
  field
    Code : Set
    decode : Code → X
\end{code}
%</fam-def>

\begin{code}
open Fam public
\end{code}

%<*post-comp>
\begin{code}
_>>_ : {-<-}∀ {α} {X Y : Set α} →{->-} (X → Y) → Fam X → Fam Y
Code (f >> F) = Code F
decode (f >> F) = f ∘ decode F
\end{code}
%</post-comp>


%<*morph>
\begin{code}
_⟶̃_ : {-<-}∀ {α} {X : Set α} →{->-} Fam X → Fam X → Set α
(C₀ , d₀) ⟶̃ (C₁ , d₁) = Σ (C₀ → C₁) λ h → ∀ x → d₁ (h x) ≡ d₀ x

_∘̃_ : {-<-}∀ {α} {X : Set α} {F G H : Fam X} →{->-} G ⟶̃ H → F ⟶̃ G → F ⟶̃ H
π₀ (f ∘̃ g) = π₀ f ∘ π₀ g
π₁ (f ∘̃ g) x = trans (π₁ f (π₀ g x)) (π₁ g x)
\end{code}
%</morph>

%<*fam-pi>
%format π  = "\FCT{π}"
\begin{code}
π : (A : Set) {-<-}{X : A → Set₁}{->-} (B : (a : A) → Fam (X a)) → Fam ((a : A) → X a)
Code (π A B) = (a : A) → Code (B a)
decode (π A B) f a = decode (B a) (f a)
\end{code}
%</fam-pi>


%format σ = "\FCT{σ}"
%<*fam-sg>
\begin{code}
σ : {-<-}{X : Set₁} {Y : X → Set₁} →{->-} (A : Fam X) → (B : (x : X) → Fam (Y x)) → Fam (Σ X Y)
Code (σ A B) = Σ (Code A) λ a → Code (B (decode A a))
decode (σ A B) (a , b) = (decode A a , decode (B _) b)
\end{code}
%</fam-sg>

%format η = "\FCT{η}"
%format μ = "\FCT{μ}"
%<*monad>
\begin{code}
η : {-<-}∀ {α} {X : Set α} →{->-} X → Fam X
Code (η x) = ⊤
decode (η x) tt = x

μ : {-<-}∀ {α} {X : Set α} →{->-} Fam (Fam X) → Fam X
Code (μ (C , d)) = Σ C (Code ∘ d)
decode (μ (C , d)) (c₀ , c₁) = decode (d c₀) c₁
\end{code}
%</monad>


-- Indexed fams
𝔽 : Fam Set₁ → Set₁
𝔽 (I , X) = (i : I) → Fam (X i)

_⇒_ : {X : Fam Set₁} → 𝔽 X → 𝔽 X → Set₁
F ⇒ G = (i : _) → F i ⟶̃ G i

infixr 20 _⊙_

_⊙_ : ∀ {X} {F G H : 𝔽 X} → G ⇒ H → F ⇒ G → F ⇒ H
--(f ⊙ g) i = f i ∘̃ g i
π₀ ((a ⊙ b) i) = π₀ (a i) ∘ π₀ (b i)
π₁ ((a ⊙ b) i) x = trans (π₁ (a i) (π₀ (b i) x)) (π₁ (b i) x)

η𝔽 : {X : Fam Set₁} {i : Code X} → decode X i → Fam (decode X i)
η𝔽 x = η x

μ𝔽 : {X : Fam Set₁} → 𝔽 (Code X , λ x → Fam (decode X x)) → 𝔽 X
μ𝔽 F = λ i → μ (F i)
\end{code}
