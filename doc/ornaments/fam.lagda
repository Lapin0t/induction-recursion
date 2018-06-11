%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.fam where
open import ornaments.prelude
\end{code}


%<*fam-def>
\begin{code}
record Fam {-<-}{α} {->-}(X : Set α) : Set (lsuc lzero ⊔ α) where
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
_>>_ : {-<-}∀ {α} {X Y : Set α} → {->-}(X → Y) → Fam X → Fam Y
Code    (f >> F) = Code F
decode  (f >> F) = f ∘ decode F
\end{code}
%</post-comp>


%<*morph>
\begin{code}
_⟶̃_ : {-<-}∀ {α} {X : Set α} → {->-}Fam X → Fam X → Set α
F ⟶̃ G = (i : Code F) → Σ (Code G) λ j → decode G j ≡′ decode F i

_∘̃_ : {-<-}∀ {α} {X : Set α} {F G H : Fam X} → {->-}G ⟶̃ H → F ⟶̃ G → F ⟶̃ H
(f ∘̃ g) x = π₀ $ f $ π₀ $ g x , trans ((π₁ ∘ f) (π₀ $ g x)) (π₁ $ g x)
\end{code}
%</morph>

\begin{code}
∘̃-assoc : ∀ {α} {X : Set α} {F G H I : Fam X} {f : F ⟶̃ G} {g : G ⟶̃ H} {h : H ⟶̃ I} → (h ∘̃ g) ∘̃ f ≡ h ∘̃ (g ∘̃ f)
∘̃-assoc = funext λ x → cong-Σ refl (uoip _ _)
\end{code}

%<*fam-pi>
%format π  = "\FCT{π}"
\begin{code}
π : (A : Set) {-<-}{X : A → Set₁} {->-}(B : (a : A) → Fam (X a)) → Fam ((a : A) → X a)
Code    (π A B)      = (a : A) → Code (B a)
decode  (π A B) f a  = decode (B a) (f a)
\end{code}
%</fam-pi>


%<*fam-sg>
%format σ = "\FCT{σ}"
\begin{code}
σ : {-<-}{X : Set₁} {Y : X → Set₁} → {->-}(A : Fam X) → (B : (x : X) → Fam (Y x)) → Fam (Σ X Y)
Code    (σ A B)          = Σ (Code A) λ a → Code (B (decode A a))
decode  (σ A B) (a , b)  = (decode A a , decode (B _) b)
\end{code}
%</fam-sg>

%<*fam-sg-arr>
\begin{code}
--⇒σ : {X : Set₁} {Y : X → Set₁} {A : Fam X} {B : (x : X) → Fam (Y x)} → σ A B ⟶̃
\end{code}
%</fam-sg-arr>


%format η = "\FCT{η}"
%format μ = "\FCT{μ}"
%<*monad-eta>
\begin{code}
η : {-<-}∀ {α} {X : Set α} → {->-}X → Fam X
Code    (η x)     = ⊤
decode  (η x) _   = x
\end{code}
%</monad-eta>

%<*monad-mu>
\begin{code}
μ : {-<-}∀ {α} {X : Set α} → {->-}Fam (Fam X) → Fam X
Code    (μ (C , d))            = Σ C (Code ∘ d)
decode  (μ (C , d)) (c₀ , c₁)  = decode (d c₀) c₁
\end{code}
%</monad-mu>


%<*ifam>
\begin{code}
𝔽 : Fam Set₁ → Set₁
𝔽 (I , X) = (i : I) → Fam (X i)
\end{code}
%</ifam>

%<*ifam-arr>
\begin{code}
_⇒_ : {-<-}{X : Fam Set₁} → {->-}𝔽 X → 𝔽 X → Set₁
F ⇒ G = (i : _) → F i ⟶̃ G i
\end{code}
%</ifam-arr>

% TODO

\begin{code}
infixr 20 _⊙_

_⊙_ : ∀ {X} {F G H : 𝔽 X} → G ⇒ H → F ⇒ G → F ⇒ H
(f ⊙ g) i = (f i) ∘̃ (g i)


⊙-assoc : ∀ {X} {F G H I : 𝔽 X} {f : F ⇒ G} {g : G ⇒ H} {h : H ⇒ I} → (h ⊙ g) ⊙ f ≡ h ⊙ (g ⊙ f)
⊙-assoc {f = f} {g = g} {h = h} = funext λ i → ∘̃-assoc {f = f i} {g = g i} {h = h i}

{-η𝔽 : {X : Fam Set₁} {i : Code X} → decode X i → Fam (decode X i)
η𝔽 x = η x

μ𝔽 : {X : Fam Set₁} → 𝔽 (Code X , Fam ∘ (decode X)) → 𝔽 X
μ𝔽 F = λ i → μ (F i)-}
\end{code}
