module prelude where

open import Agda.Primitive public
open import Agda.Builtin.Size renaming (↑_ to ssuc) public

record lift (α : Level) (A : Set) : Set α where
  constructor ↑
  field
    lower : A
open lift public

l₁ : Level
l₁ = lsuc lzero

infixl 15 _,_
record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀
open Σ public

syntax Σ A (λ a → B) = Σ[ a ∈ A ] B

_×_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
A × B = Σ A λ _ → B

data ⊥ : Set where
record ⊤ : Set where constructor *

infixl 20 _∘_
_∘_ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : ∀ {x} → B x → Set γ}
      (f : ∀ {x} (y : B x) → C y) (g : (x : A) → B x) (x : A) → C (g x)
f ∘ g = λ x → f (g x)

infixr 20 _$_
_$_ : ∀ {α β} {A : Set α} {B : A → Set β} (f : (a : A) → B a) → (a : A) → B a
f $ x = f x

--- Equality

infix 5 _≡_

data _≡_ {α} {A : Set α} (x : A) : {B : Set α} → B → Set where
  refl : x ≡ x

sym : ∀ {α} {A B : Set α} {x : A} {y : B} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {α} {A B C : Set α} {x : A} {y : B} {z : C} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

coerce : ∀ {α} {A B : Set α} → A ≡ B → A → B
coerce refl x = x

coerce-coh : ∀ {α} {A B : Set α} (e : A ≡ B) {x : A} → coerce e x ≡ x
coerce-coh refl = refl

cong : ∀ {α β} {A : Set α} {B : A → Set β} (f : (a : A) → B a) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {α β} {A : Set α} (P : A → Set β) {x y} → x ≡ y → P x → P y
subst P e = coerce (cong P e)

subst-coh : ∀ {α β} {A : Set α} (P : A → Set β) {x y} (e : x ≡ y) {p} → subst P e p ≡ p
subst-coh P e = coerce-coh (cong P e)

cong₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : (a : A) → B a → Set γ}
  (f : (a : A) (b : B a) → C a b) {x x' y y'} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

subst₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} (C : (a : A) → B a → Set γ)
  {x x' y y'} → x ≡ x' → y ≡ y' → C x y → C x' y'
subst₂ P e e' = coerce (cong₂ P e e')

Σ-ext : ∀ {α β} {A : Set α} {B : A → Set β} {x y : Σ A B} → π₀ x ≡ π₀ y → π₁ x ≡ π₁ y → x ≡ y
Σ-ext = cong₂ _,_

postulate
  Π-ext : ∀ {α β} {A : Set α} {B : A → Set β} {f g : (a : A) → B a} → ((a : A) → f a ≡ g a) → f ≡ g

uoip : ∀ {α} {A B : Set α} {x : A} {y : B} (e e' : x ≡ y) → e ≡ e'
uoip refl refl = refl

data _⁻¹_ {α β} {A : Set α} {B : Set β} (f : A → B) : B → Set α where
  ok : (a : A) → f ⁻¹ (f a)
