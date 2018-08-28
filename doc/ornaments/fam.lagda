%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.fam where
open import ornaments.prelude

variable
  {α₀ α₁ α₂ α₃} : Level
  {β₀ β₁} : Level
  {γ₀ γ₁} : Level
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

%<*iset>
\begin{code}
ISet : (α β : Level) → Set _
ISet α β = Fam α (Set β)
\end{code}
%</iset>

\begin{code}
el : ∀ {α β} → ISet α β → Set _
el X = (i : Code X) → decode X i

sing : ∀ {α β} → ISet α β → Set _
sing X = Σ (Code X) (decode X)
\end{code}

%<*morph>
\begin{code}
_⟶̃_ : {-<-}∀ {α₀ α₁ β} {X : Set β} → {->-}Fam α₀ X → Fam α₁ X → Set _
F ⟶̃ G = (i : Code F) → Σ (Code G) λ j → decode G j ≡ decode F i
\end{code}
%</morph>

\begin{code}
_∘̃_ : {-<-}∀ {α₀ α₁ α₂ β}{X : Set β}{F : Fam α₀ X}{G : Fam α₁ X}{H : Fam α₂ X} → {->-}G ⟶̃ H → F ⟶̃ G → F ⟶̃ H
(f ∘̃ g) x = π₀ $ f $ π₀ $ g x , trans ((π₁ ∘ f) (π₀ $ g x)) (π₁ $ g x)

infix 22 _⟶̃_

∘̃-assoc : ∀ {α₀ α₁ α₂ α₃ β}{X : Set β}{F : Fam α₀ X}{G : Fam α₁ X}{H : Fam α₂ X}{I : Fam α₃ X}
          {f : F ⟶̃ G}{g : G ⟶̃ H}{h : H ⟶̃ I} → (h ∘̃ g) ∘̃ f ≡ h ∘̃ (g ∘̃ f)
∘̃-assoc = funext λ x → cong-Σ refl (uoip _ _)
\end{code}


%<*pcomp>
\begin{code}
_<<_ : {-<-}∀ {α β₀ β₁}{X : Set β₀}{Y : Set β₁}{->-}(f : X → Y) → Fam α X → Fam α Y
f << F = _ , f ∘ decode F
\end{code}
%</pcomp>

%<*pcomp-arr>
\begin{code}
_<<$>_ : {-<-}∀ {α₀ α₁ β₀ β₁}{X : Set β₀}{Y : Set β₁}{->-}(f : X → Y){-<-}{A : Fam α₀ X}{B : Fam α₁ X}{->-} → A ⟶̃ B → f << A ⟶̃ f << B
(f <<$> m) i = let (j , p) = m i in j , cong f p
\end{code}
%</pcomp-arr>


%<*post-comp>
\begin{code}
infix 25 _<<_

_>>_ : {-<-}∀ {α₀ α₁ β}{X : Set β}(F : Fam α₀ X){Y : Set α₁}{->-}(f : Y → Code F) → Fam α₁ X
F >> f = _ , decode F ∘ f

record FCT (α₀ α₁ : Level) {β₀ β₁} (X : Set β₀) (Y : Set β₁) : Set (β₀ ⊔ β₁ ⊔ lsuc (α₀ ⊔ α₁)) where
  field
    omap : Fam α₀ X → Fam α₁ Y
    fmap : {F G : Fam α₀ X} (f : F ⟶̃ G) → omap F ⟶̃ omap G
open FCT public

post-comp : ∀ {α₀ β₀ β₁}{X : Set β₀}{Y : Set β₁}(f : X → Y) → FCT α₀ α₀ X Y
omap (post-comp f) F = _ , f ∘ decode F
fmap (post-comp f) m i = π₀ $ m i , cong f ∘ π₁ $ m i

--f-π : ∀ {α β δ} (A : Set α) {X : A → Set δ}

\end{code}
%</post-comp>

%<*fam-pi>
%format π  = "\FCT{π}"
\begin{code}
π : {-<-}∀ {α β δ}{->-}(A : Set α) {-<-}{X : A → Set δ}{->-}(B : (a : A) → Fam β (X a)) → Fam (α ⊔ β) ((a : A) → X a)
Code    (π A B)      = (a : A) → Code (B a)
decode  (π A B) f a  = decode (B a) (f a)
\end{code}
%</fam-pi>

%<*fam-pi-arr>
\begin{code}
π→ : {-<-}∀ {α β₀ β₁ δ} {A : Set α} {X : A → Set δ} {B₀ : (a : A) → Fam β₀ (X a)} {B₁ : (a : A) → Fam β₁ (X a)} →{->-}((a : A) → B₀ a ⟶̃ B₁ a) → π A B₀ ⟶̃ π A B₁
π→ F i = (λ a → π₀ $ F a (i a)) , funext λ a → π₁ $ F a (i a)
\end{code}
%</fam-pi-arr>

%<*fam-sg>
%format σ = "\FCT{σ}"
\begin{code}
σ : {-<-}∀ {α β δ γ} {X : Set δ} {Y : X → Set γ} → {->-}(A : Fam α X) → (B : (x : X) → Fam β (Y x)) → Fam (α ⊔ β) (Σ X Y)
Code    (σ A B)          = Σ (Code A) λ a → Code (B (decode A a))
decode  (σ A B) (a , b)  = decode A a , decode (B (decode A a)) b
\end{code}
%</fam-sg>

%<*fam-sg-arr>
\begin{code}
σ→ : {-<-}∀ {α₀ α₁ β₀ β₁ δ γ} {X : Set δ} {Y : X → Set γ} {A₀ : Fam α₀ X} {A₁ : Fam α₁ X} (B₀ : (x : X) → Fam β₀ (Y x)) (B₁ : (x : X) → Fam β₁ (Y x)) →
     {->-}A₀ ⟶̃ A₁ → ((a : Code A₀) → B₀ (decode A₀ a) ⟶̃ B₁ (decode A₀ a)) → σ A₀ B₀ ⟶̃ σ A₁ B₁
σ→ _ B₁ F G (a , b) =
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
𝔽 : {-<-}∀ {α β}{->-}(γ : Level) → ISet α β → Set _
𝔽 γ (I , X) = (i : I) → Fam γ (X i)
\end{code}
%</ifam>

%<*ifam-arr>
\begin{code}
_⇒_ : {-<-}∀ {α β γ₀ γ₁} {X : ISet α β} → {->-}𝔽 γ₀ X → 𝔽 γ₁ X → Set _
F ⇒ G = (i : _) → F i ⟶̃ G i
\end{code}
%</ifam-arr>

% TODO

%<*fam-and>
\begin{code}
infix 30 _&_
_&_ : ∀ {α β γ δ₀ δ₁} {I : Set α} {X : I → Set β} {Y : I → Set γ} (F : 𝔽 δ₀ (I , X)) (G : 𝔽 δ₁ (I , Y)) → 𝔽 (δ₀ ⊔ δ₁) (I , X)
Code ((F & G) i) = Code (F i) × Code (G i)
decode ((F & G) i) (x , _) = decode (F i) x


\end{code}
%</fam-and>

\begin{code}
lft : ∀ {α β γ} {X : ISet α β} (γ' : Level) → 𝔽 γ X → 𝔽 (γ ⊔ γ') X
Code (lft γ' F i) = Lift γ' (Code $ F i)
decode (lft γ' F i) (lift x) = decode (F i) x

infix 22 _⇒_
infix 30 π₀<_

_!<_ : ∀ {α β γ δ} {X : ISet α β} {Y : Code X → Set δ} (f : (i : _) → decode X i → Y i) → 𝔽 γ X → 𝔽 γ (Code X , Y)
(f !< F) i = f i << F i

π₀<_ : ∀ {α β γ δ}{X : ISet α β}{B : (i : _) → decode X i → Set δ} → 𝔽 γ (Code X , λ i → Σ (decode X i) (B i)) → 𝔽 γ X
π₀< F = (λ _ → π₀) !< F

infixr 20 _⊙_

_⊙_ : {-<-}∀ {α β γ₀ γ₁ γ₂} {X : ISet α β} {F : 𝔽 γ₀ X} {G : 𝔽 γ₁ X} {H : 𝔽 γ₂ X} →{->-}G ⇒ H → F ⇒ G → F ⇒ H
(f ⊙ g) i = (f i) ∘̃ (g i)

⊙-assoc : ∀ {α β γ₀ γ₁ γ₂ γ₃} {X : ISet α β} {F : 𝔽 γ₀ X} {G : 𝔽 γ₁ X} {H : 𝔽 γ₂ X} {I : 𝔽 γ₃ X} {f : F ⇒ G} {g : G ⇒ H} {h : H ⇒ I} → (h ⊙ g) ⊙ f ≡ h ⊙ (g ⊙ f)
⊙-assoc {f = f} {g = g} {h = h} = funext λ i → ∘̃-assoc {f = f i} {g = g i} {h = h i}

_#_ : ∀ {α₀ α₁ β γ₀ γ₁} {X : ISet α₀ β} {Y : ISet α₁ β} (f : Y ⟶̃ X) → 𝔽 γ₀ X → 𝔽 (γ₀ ⊔ γ₁) Y
Code (_#_ {γ₁ = γ₁} f F j) = Lift γ₁ $ Code (F $ π₀ $ f j)
decode ((f # F) j) (lift x) = subst (λ a → a) (π₁ $ f j) (decode (F $ π₀ $ f j) x)

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
