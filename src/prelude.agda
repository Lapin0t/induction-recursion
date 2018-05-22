module prelude where

open import Agda.Primitive public
open import Agda.Builtin.Size


-- Datatypes

record Lift {α β} (A : Set α) : Set (α ⊔ β) where
  constructor lift
  field lower : A

open Lift public


infixr 4 _,_
record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀

open Σ public


data ⊥ : Set where
data ⊤ : Set where tt : ⊤


-- Equality

infix 4 _≡_
data _≡_ {α} {A : Set α} (x : A) : {B : Set α} → B → Set α where
  refl : x ≡ x

cong : ∀ {α β} {A : Set α} {B : A → Set β} (f : (x : A) → B x) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : {a : A} → B a → Set γ}
          (f : (x : A) → (y : B x) → C y) {x₀ x₁ : A} {y₀ : B x₀} {y₁ : B x₁} →
          x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
cong₂ f refl refl = refl

sym : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

subst : ∀ {α β} {A : Set α} (P : A → Set β) {x y} → x ≡ y → P x → P y
subst P refl p = p

subst-elim : ∀ {α β} {A : Set α} {P : A → Set β} {x y} {p : x ≡ y} {y : P x} → subst P p y ≡ y
subst-elim {p = refl} = refl

postulate
  funext : ∀ {α β} {A : Set α} {B : A → Set β} {f g : (x : A) → B x} →
           ((x : A) → f x ≡ g x) → f ≡ g

--           (λ x a → decode (⟦ B a ⟧ᵢ .B) (π₀ ⟦ B a ⟧[ f ]ᵢ (x a))) ≡
--      (λ f₁ a → decode (⟦ B a ⟧ᵢ .A) (f₁ a))



-- Functions

_∘_ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ} →
        (∀ {x} → (y : B x) → C y) → (g : (x : A) → B x) → (x : A) → C (g x)
f ∘ g = λ x → f (g x)

infixr 5 _⟶̇_
_⟶̇_ : ∀ {α β} {I : Set} → (I → Set α) → (I → Set β) → Set (α ⊔ β)
_⟶̇_ {I = I} X Y = (i : I) → X i → Y i
