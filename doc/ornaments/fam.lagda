%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.fam where
open import ornaments.prelude
\end{code}


%<*fam-def>
\begin{code}
record Fam (α : Level) {-<-}{β}{->-}(X : Set β) : Set (lsuc α ⊔ β) where
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
ISet : (α β : Level) → Set (lsuc (α ⊔ β))
ISet α β = Fam α (Set β)

el : ∀ {α β} → ISet α β → Set (α ⊔ β)
el X = (i : Code X) → decode X i

sing : ∀ {α β} → ISet α β → Set (α ⊔ β)
sing X = Σ (Code X) (decode X)
\end{code}
%</fam-set1>

%<*morph>
\begin{code}
_⟶̃_ : {-<-}∀ {α₀ α₁ β} {X : Set β} → {->-}Fam α₀ X → Fam α₁ X → Set (α₀ ⊔ α₁ ⊔ β)
F ⟶̃ G = (i : Code F) → Σ (Code G) λ j → decode G j ≡ decode F i

_∘̃_ : {-<-}∀ {α₀ α₁ α₂ β}{X : Set β}{F : Fam α₀ X}{G : Fam α₁ X}{H : Fam α₂ X} → {->-}G ⟶̃ H → F ⟶̃ G → F ⟶̃ H
(f ∘̃ g) x = π₀ $ f $ π₀ $ g x , trans ((π₁ ∘ f) (π₀ $ g x)) (π₁ $ g x)
\end{code}
%</morph>

\begin{code}
infix 22 _⟶̃_

∘̃-assoc : ∀ {α₀ α₁ α₂ α₃ β}{X : Set β}{F : Fam α₀ X}{G : Fam α₁ X}{H : Fam α₂ X}{I : Fam α₃ X}
          {f : F ⟶̃ G}{g : G ⟶̃ H}{h : H ⟶̃ I} → (h ∘̃ g) ∘̃ f ≡ h ∘̃ (g ∘̃ f)
∘̃-assoc = funext λ x → cong-Σ refl (uoip _ _)
\end{code}

%<*post-comp>
\begin{code}
infix 25 _>>_

_>>_ : {-<-}∀ {α β₀ β₁}{X : Set β₀}{Y : Set β₁}{->-}(f : X → Y) → Fam α X → Fam α Y
Code    (f >> F) = Code F
decode  (f >> F) = f ∘ decode F
\end{code}
%</post-comp>

%<*post-comp-arr>
\begin{code}
_<$>>_ : ∀ {α₀ α₁ β₀ β₁}{X : Set β₀}{Y : Set β₁}(f : X → Y){A : Fam α₀ X}{B : Fam α₁ X} → A ⟶̃ B → f >> A ⟶̃ f >> B
(f <$>> h) i = π₀ $ h i , cong f (π₁ $ h i)
\end{code}
%</post-comp-arr>


%<*fam-pi>
%format π  = "\FCT{π}"
\begin{code}
π : ∀ {α β δ} (A : Set α) {-<-}{X : A → Set δ} {->-}(B : (a : A) → Fam β (X a)) → Fam (α ⊔ β) ((a : A) → X a)
Code    (π A B)      = (a : A) → Code (B a)
decode  (π A B) f a  = decode (B a) (f a)
\end{code}
%</fam-pi>

%<*fam-pi-arr>
\begin{code}
π→ : ∀ {α β₀ β₁ δ} {A : Set α} {X : A → Set δ} {B₀ : (a : A) → Fam β₀ (X a)} {B₁ : (a : A) → Fam β₁ (X a)} → ((a : A) → B₀ a ⟶̃ B₁ a) → π A B₀ ⟶̃ π A B₁
π→ F i = (λ a → π₀ $ F a (i a)) , funext λ a → π₁ $ F a (i a)
\end{code}
%</fam-pi-arr>

%<*fam-sg>
%format σ = "\FCT{σ}"
\begin{code}
σ : {-<-}∀ {α β δ γ} {X : Set δ} {Y : X → Set γ} → {->-}(A : Fam α X) → (B : (x : X) → Fam β (Y x)) → Fam (α ⊔ β) (Σ X Y)
Code    (σ A B)          = Σ (Code A) λ a → Code (B (decode A a))
decode  (σ A B) (a , b)  = decode A a , decode (B _) b
\end{code}
%</fam-sg>

%<*fam-sg-arr>
\begin{code}
σ→ : ∀ {α₀ α₁ β₀ β₁ δ γ} {X : Set δ} {Y : X → Set γ} {A₀ : Fam α₀ X} {A₁ : Fam α₁ X} {B₀ : (x : X) → Fam β₀ (Y x)} (B₁ : (x : X) → Fam β₁ (Y x)) →
     A₀ ⟶̃ A₁ → ((a : Code A₀) → B₀ (decode A₀ a) ⟶̃ B₁ (decode A₀ a)) → σ A₀ B₀ ⟶̃ σ A₁ B₁
σ→ B₁ F G (a , b) =
  let a' , p = F a in
  let b' , q = G a b in
  (a' , subst (Code ∘ B₁) (sym p) b') , cong-Σ p (trans (cong₂ (decode ∘ B₁) p (subst-elim _ $ sym p)) q)
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
𝔽 : ∀ {α β} → (γ : Level) → ISet α β → Set (α ⊔ β ⊔ lsuc γ)
𝔽 γ (I , X) = (i : I) → Fam γ (X i)
\end{code}
%</ifam>

%<*ifam-arr>
\begin{code}
_⇒_ : {-<-}∀ {α β γ₀ γ₁} {X : ISet α β} → {->-}𝔽 γ₀ X → 𝔽 γ₁ X → Set (α ⊔ β ⊔ γ₀ ⊔ γ₁) --Set (α ⊔ β)
F ⇒ G = (i : _) → F i ⟶̃ G i
\end{code}
%</ifam-arr>

% TODO

\begin{code}

π₀>_ : ∀ {α β γ δ}{X : ISet α β}{B : (i : _) → decode X i → Set δ} → 𝔽 γ (Code X , λ i → Σ (decode X i) (B i)) → 𝔽 γ X
(π₀> F) i = π₀ >> F i

infixr 20 _⊙_

_⊙_ : ∀ {α β γ} {X : ISet α β} {F G H : 𝔽 γ X} → G ⇒ H → F ⇒ G → F ⇒ H
(f ⊙ g) i = (f i) ∘̃ (g i)

⊙-assoc : ∀ {α β γ} {X : ISet α β} {F G H I : 𝔽 γ X} {f : F ⇒ G} {g : G ⇒ H} {h : H ⇒ I} → (h ⊙ g) ⊙ f ≡ h ⊙ (g ⊙ f)
⊙-assoc {f = f} {g = g} {h = h} = funext λ i → ∘̃-assoc {f = f i} {g = g i} {h = h i}

--_>>>_ : {-<-}∀ {α β γ} {X : ISet α β} {Y : Code X → Set γ} → {->-}((i : Code X) → decode X i → Y i) → 𝔽 X → 𝔽 (Code X , Y)
--(f >>> F) i = f i >> F i



{-η𝔽 : {X : Fam Set₁} {i : Code X} → decode X i → Fam (decode X i)
η𝔽 x = η x

μ𝔽 : {X : Fam Set₁} → 𝔽 (Code X , Fam ∘ (decode X)) → 𝔽 X
μ𝔽 F = λ i → μ (F i)-}


record _⊂_ {α β δ γ} (X : ISet α δ) (Y : ISet β γ) : Set (α ⊔ β ⊔ δ ⊔ γ) where
  constructor _,_
  field
    up : Code X → Code Y
    down : (i : Code X) → decode Y (up i) → decode X i
open _⊂_ public

\end{code}
