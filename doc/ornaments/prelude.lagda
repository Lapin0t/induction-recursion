%include agda.fmt

%format Set = "\DATA{Set}"
%format Set₁ = "\DATA{Set₁}"
%format Set₂ = "\DATA{Set₂}"
%format ⊔ = "\FCT{⊔}"
%format _⊔_ = _ ⊔ _
%format Size = "\DATA{Size}"
%format Size< = "\DATA{Size<}"

\begin{code}
module ornaments.prelude where

open import Agda.Primitive public
open import Agda.Builtin.Size hiding (↑_) public
\end{code}


%format Lift = "\DATA{Lift}"
%format lift = "\CON{lift}"
%format lower = "\FCT{lower}"

%<*lift>
\begin{code}
record Lift {-<-}{α β}{->-} (A : Set α) : Set (α ⊔ β) where
  constructor lift
  field lower : A
\end{code}
%</lift>

\begin{code}
open Lift public
\end{code}

%format Σ = "\DATA{Σ}"
%format , = "\CON{,}"
%format _,_ = _ , _
%format π₀ = "\FCT{π₀}"
%format π₁ = "\FCT{π₁}"
%format × = "\DATA{\mathbin{×}}"

%<*sigma>
\begin{code}
record Σ {-<-}{α β}{->-} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀
\end{code}
%</sigma>

\begin{code}
infixr 4 _,_
open Σ public

_×_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
A × B = Σ A λ _ → B
\end{code}


%format ⊥ = "\DATA{⊥}"
%format ⊤ = "\DATA{⊤}"
%format * = "\CON{*}"
%<*prop>
\begin{code}
data ⊥ : Set where
data ⊤ : Set where * : ⊤
\end{code}
%</prop>


%format ≡ = "\DATA{\mathrel{≡}}"
%format refl = "\CON{refl}"
%format subst = "\FCT{subst}"
%format subst-elim = "\FCT{subst-elim}"
%format cong = "\FCT{cong}"
%format trans = "\FCT{trans}"
%format sym = "\FCT{sym}"

%<*equality>
\begin{code}
data _≡_ {-<-}{α} {A : Set α}{->-} (x : A) : {-<-}{B : Set α} →{->-} B → Set α where
  refl : x ≡ x

subst : {-<-}∀ {α β} {A : Set α}{->-} (P : A → Set β) {-<-}{x y} {->-}→ x ≡ y → P x → P y
subst P refl p = p

subst-elim : {-<-}∀ {α β} {A : Set α}{->-} (P : A → Set β) {-<-}{x y}{->-}→ (p : x ≡ y) {-<-}{a : P x}{->-} → subst P p a ≡ a
subst-elim P refl = refl

cong : {-<-}∀ {α β} {A : Set α} {B : A → Set β}{->-} (f : (x : A) → B x) {-<-}{x y}{->-} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {-<-}∀ {α} {A B C : Set α} {x : A} {y : B} {z : C} →{->-} x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {-<-}∀ {α} {A : Set α} {x y : A} →{->-} x ≡ y → y ≡ x
sym refl = refl

\end{code}
%</equality>

\begin{code}
subst₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} (P : (a : A) → B a → Set γ)
           {x₀ x₁ y₀ y₁} → x₀ ≡ x₁ → y₀ ≡ y₁ → P x₀ y₀ → P x₁ y₁
subst₂ P refl refl p = p

cong₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : {a : A} → B a → Set γ} (f : (a : A) → (b : B a) → C b) {x₀ x₁ y₀ y₁} → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
cong₂ f refl refl = refl

cong-Σ : ∀ {α β} {A : Set α} {B : A → Set β} {p₀ p₁ : Σ A B} → π₀ p₀ ≡ π₀ p₁ → π₁ p₀ ≡ π₁ p₁ → p₀ ≡ p₁
cong-Σ refl refl = refl

infix 4 _≡_
postulate
  funext : ∀ {α β} {A : Set α} {B : A → Set β} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g


-- Functions

_∘_ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ} →
        (∀ {x} → (y : B x) → C y) → (g : (x : A) → B x) → (x : A) → C (g x)
f ∘ g = λ x → f (g x)

app : ∀ {α β} {A : Set α} {B : A → Set β} (x : A) (f : (a : A) → B a) → B x
app x f = f x


infixr 5 _⟶̇_
_⟶̇_ : ∀ {α β} {I : Set} → (I → Set α) → (I → Set β) → Set (α ⊔ β)
_⟶̇_ {I = I} X Y = (i : I) → X i → Y i
\end{code}
