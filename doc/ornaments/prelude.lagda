%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.prelude where

open import Agda.Primitive public
open import Agda.Builtin.Size hiding (↑_) public
\end{code}


%%% LIFTING %%%

%<*lift>
\begin{code}
record Lift {α} (β : Level) (A : Set α) : Set (α ⊔ β) where
  constructor lift
  field lower : A
\end{code}
%</lift>

\begin{code}
open Lift public
\end{code}


%%% SIGMA %%%

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
\end{code}

%<*prod>
\begin{code}
_×_ : {-<-}∀ {α β} → {->-}Set α → Set β → Set _
A × B = Σ A λ _ → B
\end{code}
%</prod>


%%% SIGMA %%%

%<*prop>
\begin{code}
data ⊥ {α} : Set α where
data ⊤ {α} : Set α where * : ⊤
\end{code}
%</prop>


%%% FUNCTION UTILITIES %%%

\begin{code}
infixl 20 _∘_
infixr 5 _⟶̇_
infixr 10 _$_

_∘_ : {-<-}∀ {α β γ} {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ} →{->-} (∀ {x} → (y : B x) → C y) → (g : (x : A) → B x) → (x : A) → C (g x)
f ∘ g = λ x → f (g x)

_$_ : {-<-}∀ {α β} {A : Set α} {B : A → Set β}{->-} (f : (a : A) → B a) → (x : A) → B x
f $ x = f x

--app : {-<-}∀ {α β} {A : Set α} {B : A → Set β}{->-} (x : A) (f : (a : A) → B a) → B x
--app x f = f x

S : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : (a : A) → B a → Set γ} (x : (a : A) → (b : B a) → C a b) (y : (a : A) → B a) → (a : A) → C a (y a)
S x y z = x z (y z)

_⟶̇_ : {-<-}∀ {α β γ} {I : Set α} →{->-} (I → Set β) → (I → Set γ) → Set (α ⊔ β ⊔ γ)
_⟶̇_ {-<-}{I = I}{->-} X Y = (i : I) → X i → Y i
\end{code}


%%% EQUALITY %%%

%<*equality>
\begin{code}
data _≡_ {-<-}{α} {A : Set α}{->-} (x : A) : {-<-}{B : Set α} →{->-} B → Set α where refl : x ≡ x
\end{code}
%</equality>

\begin{code}
postulate
\end{code}

%<*funext>
\begin{code}
  funext : {-<-}∀ {α β} {A : Set α} {B₀ B₁ : A → Set β} {f : (x : A) → B₀ x} {g : (x : A) → B₁ x} → {->-}((x : A) → f x ≡ g x) → f ≡ g
\end{code}
%</funext>

% utils for equality
\begin{code}
infix 4 _≡_
infix 4 _≡′_
_≡′_ : ∀ {α} {A : Set α} → A → A → Set α
x ≡′ y = x ≡ y

data _≡″_ {α} {A : Set α} (x : A) : A → Set α where
  refl : x ≡″ x
{-# BUILTIN EQUALITY _≡″_  #-}

to-beq : ∀ {α} {A : Set α} {x y : A} → x ≡ y → x ≡″ y
to-beq refl = refl

to-eq : ∀ {α} {A : Set α} {x y : A} → x ≡″ y → x ≡ y
to-eq refl = refl


subst : {-<-}∀ {α β} {A : Set α}{->-} (P : A → Set β) {-<-}{x y} {->-}→ x ≡ y → P x → P y
subst P refl p = p

subst-elim : {-<-}∀ {α β} {A : Set α}{->-} (P : A → Set β) {-<-}{x y}{->-}→ (p : x ≡ y) {-<-}{a : P x}{->-} → subst P p a ≡ a
subst-elim P refl = refl

cong : {-<-}∀ {α β} {A : Set α} {B : A → Set β}{->-} (f : (x : A) → B x) {-<-}{x y}{->-} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {-<-}∀ {α} {A B C : Set α} {x : A} {y : B} {z : C} →{->-} x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

uoip : ∀ {α} {A B : Set α} {x : A} {y : B} → (p₀ : x ≡ y) → (p₁ : x ≡ y) → p₀ ≡ p₁
uoip refl refl = refl

sym : {-<-}∀ {α} {A : Set α} {x y : A} →{->-} x ≡ y → y ≡ x
sym refl = refl

subst₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} (P : (a : A) → B a → Set γ)
           {x₀ x₁ y₀ y₁} → x₀ ≡ x₁ → y₀ ≡ y₁ → P x₀ y₀ → P x₁ y₁
subst₂ P refl refl p = p

cong₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : {a : A} → B a → Set γ} (f : (a : A) → (b : B a) → C b) {x₀ x₁ y₀ y₁} → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
cong₂ f refl refl = refl

cong-Σ : ∀ {α β} {A : Set α} {B : A → Set β} {p₀ p₁ : Σ A B} → π₀ p₀ ≡ π₀ p₁ → π₁ p₀ ≡ π₁ p₁ → p₀ ≡ p₁
cong-Σ refl refl = refl

subst-≡ : {A₀ A₁ : Set₁} → {B₀ B₁ : A₁ → Set₁} → (p : A₀ ≡ A₁) → (B₀ ≡ B₁) → B₀ ∘ subst (λ x → x) p ≡ B₁
subst-≡ refl refl = refl
\end{code}
