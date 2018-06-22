%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.fam where
open import ornaments.prelude
\end{code}


%<*fam-def>
\begin{code}
record Fam {-<-}{α} {->-}(X : Set (lsuc α)) : Set (lsuc α) where
  constructor _,_
  field
    Code : Set α
    decode : Code → X
\end{code}
%</fam-def>

\begin{code}
open Fam public
\end{code}

%<*fam-set1>
\begin{code}
ISet : (α : Level) → Set (lsuc α)
ISet α = Fam (Set α)

El : ∀ {α} → ISet α → Set α
El A = Σ (Code A) (λ i → decode A i)
\end{code}
%</fam-set1>

%<*morph>
\begin{code}
_⟶̃_ : {-<-}∀ {α X} → {->-}Fam {α} X → Fam {α} X → Set (lsuc α)
F ⟶̃ G = (i : Code F) → Σ (Code G) λ j → decode G j ≡ decode F i

_∘̃_ : {-<-}∀ {α X} {F G H : Fam {α} X} → {->-}G ⟶̃ H → F ⟶̃ G → F ⟶̃ H
(f ∘̃ g) x = π₀ $ f $ π₀ $ g x , trans ((π₁ ∘ f) (π₀ $ g x)) (π₁ $ g x)
\end{code}
%</morph>

\begin{code}
infix 22 _⟶̃_

∘̃-assoc : ∀ {α X} {F G H I : Fam {α} X} {f : F ⟶̃ G} {g : G ⟶̃ H} {h : H ⟶̃ I} → (h ∘̃ g) ∘̃ f ≡ h ∘̃ (g ∘̃ f)
∘̃-assoc = funext λ x → cong-Σ refl (uoip _ _)
\end{code}

%<*post-comp>
\begin{code}
infix 25 _>>_

_>>_ : {-<-}∀ {α} {X Y : Set (lsuc α)} → {->-}(X → Y) → Fam X → Fam Y
Code    (f >> F) = Code F
decode  (f >> F) = f ∘ decode F
\end{code}
%</post-comp>

%<*post-comp-arr>
\begin{code}
_<$>>_ : ∀ {α} {X Y : Set (lsuc α)} (f : X → Y) {A B : Fam X} → A ⟶̃ B → f >> A ⟶̃ f >> B
(f <$>> h) i = π₀ $ h i , cong f (π₁ $ h i)
\end{code}
%</post-comp-arr>


%<*fam-pi>
%format π  = "\FCT{π}"
\begin{code}
π : ∀ {α} (A : Set α) {-<-}{X : A → Set (lsuc α)} {->-}(B : (a : A) → Fam (X a)) → Fam ((a : A) → X a)
Code    (π A B)      = (a : A) → Code (B a)
decode  (π A B) f a  = decode (B a) (f a)
\end{code}
%</fam-pi>


%<*fam-sg>
%format σ = "\FCT{σ}"
\begin{code}
σ : {-<-}∀ {α} {X : Set (lsuc α)} {Y : X → Set (lsuc α)} → {->-}(A : Fam X) → (B : (x : X) → Fam (Y x)) → Fam (Σ X Y)
Code    (σ A B)          = Σ (Code A) λ a → Code (B (decode A a))
decode  (σ A B) (a , b)  = (decode A a , decode (B _) b)
\end{code}
%</fam-sg>

%<*fam-sg-arr>
\begin{code}
σ-⟶̃ : ∀ {α} {X : Set (lsuc α)} {Y : X → Set (lsuc α)} {A₀ A₁ : Fam X} {B₀ B₁ : (x : X) → Fam (Y x)} → (pa : A₀ ⟶̃ A₁) → ((a : Code A₀) → B₀ (decode A₀ a) ⟶̃ B₁ (decode A₀ a)) → σ A₀ B₀ ⟶̃ σ A₁ B₁
σ-⟶̃ {A₀ = A₀} {B₁ = B₁} pa pb (a , b) =
  let a' , eqa = pa a in
  let b' , eqb = pb a b in
  (a' , subst (Code ∘ B₁) (sym eqa) b') ,
  cong-Σ eqa (trans (cong₂ (decode ∘ B₁) eqa (subst-elim _ $ sym eqa)) eqb)
\end{code}
%</fam-sg-arr>


%format η = "\FCT{η}"
%format μ = "\FCT{μ}"
%<*monad-eta>
\begin{code}
--η : {-<-}∀ {α} {X : Set α} → {->-}X → Fam X
--Code    (η x)     = Lift ⊤
--decode  (η x) _   = x
\end{code}
%</monad-eta>

%<*monad-mu>
\begin{code}
--μ : {-<-}∀ {α} {X : Set (lsuc α)} → {->-}Fam (Fam X) → Fam X
--Code    (μ (C , d))            = Σ C (Code ∘ d)
--decode  (μ (C , d)) (c₀ , c₁)  = decode (d c₀) c₁
\end{code}
%</monad-mu>


%<*ifam>
\begin{code}
𝔽 : ∀ {α} → ISet (lsuc α) → Set (lsuc α)
𝔽 (I , X) = (i : I) → Fam (X i)
\end{code}
%</ifam>

%<*ifam-arr>
\begin{code}
_⇒_ : {-<-}∀ {α} {X : ISet (lsuc α)} → {->-}𝔽 X → 𝔽 X → Set (lsuc α)
F ⇒ G = (i : _) → F i ⟶̃ G i
\end{code}
%</ifam-arr>

% TODO

\begin{code}
infixr 20 _⊙_

_⊙_ : ∀ {α} {X : ISet (lsuc α)} {F G H : 𝔽 X} → G ⇒ H → F ⇒ G → F ⇒ H
(f ⊙ g) i = (f i) ∘̃ (g i)


⊙-assoc : ∀ {α} {X : ISet (lsuc α)} {F G H I : 𝔽 X} {f : F ⇒ G} {g : G ⇒ H} {h : H ⇒ I} → (h ⊙ g) ⊙ f ≡ h ⊙ (g ⊙ f)
⊙-assoc {f = f} {g = g} {h = h} = funext λ i → ∘̃-assoc {f = f i} {g = g i} {h = h i}

_>>>_ : {-<-}∀ {α} {X : ISet (lsuc α)} {Y} → {->-}((i : Code X) → decode X i → Y i) → 𝔽 X → 𝔽 (Code X , Y)
(f >>> F) i = f i >> F i

{-η𝔽 : {X : Fam Set₁} {i : Code X} → decode X i → Fam (decode X i)
η𝔽 x = η x

μ𝔽 : {X : Fam Set₁} → 𝔽 (Code X , Fam ∘ (decode X)) → 𝔽 X
μ𝔽 F = λ i → μ (F i)-}
\end{code}
