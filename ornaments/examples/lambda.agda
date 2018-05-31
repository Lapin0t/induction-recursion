module examples.lambda where

open import Data.Product hiding (_,_)
open import Relation.Binary.PropositionalEquality

data ⊥ : Set where
data ⊤ : Set where * : ⊤

infixl 30 _,_

data stack (X : Set) : Set where
  ε : stack X
  _,_ : stack X → X → stack X

module _ {X : Set} where
  data _⊆_ : stack X → stack X → Set where
    bot : ε ⊆ ε
    keep : ∀ {Γ Δ x} → Γ ⊆ Δ → Γ , x ⊆ Δ , x
    skip : ∀ {Γ Δ x} → Γ ⊆ Δ → Γ ⊆ Δ , x

  data _∈_ (x : X) : stack X → Set where
    here : ∀ {Γ} → x ∈ Γ , x
    there : ∀ {Γ y} → x ∈ Γ → x ∈ Γ , y

  id : ∀ {Γ} → Γ ⊆ Γ
  id {ε} = bot
  id {_ , _} = keep id

  triv : ∀ {Γ} → ε ⊆ Γ
  triv {ε} = bot
  triv {_ , _} = skip triv

  shift : ∀ {Γ Δ x} → Γ ⊆ Δ → x ∈ Γ → x ∈ Δ
  shift (keep x) here = here
  shift (keep x) (there y) = there (shift x y)
  shift (skip x) y = there (shift x y)


data type : Set where
  base : type
  _⇒_ : type → type → type

data dir : Set where chk syn : dir

IN OUT : dir → Set
IN chk = type
IN syn = ⊤
OUT chk = ⊤
OUT syn = type

data term (Γ : stack type) : (d : dir) → IN d → Set
out : ∀ {Γ d i} → term Γ d i → OUT d

ask-dom : (stack type) → type → Set
ask-dom _ base = ⊥
ask-dom Γ (a ⇒ b) = term Γ chk a

data term Γ where
  var : ∀ {a} → a ∈ Γ → term Γ syn *
  lam : ∀ {a} → (t : term (Γ , a) syn *) → term Γ chk (a ⇒ out t)
  app : (f : term Γ syn *) → (x : ask-dom Γ (out f)) → term Γ syn *

  vrf : (t : term Γ syn *) → term Γ chk (out t)
  ann : ∀ {a} → (t : term Γ chk a) → term Γ syn *

out (var {a} _) = a
out (ann {a} _) = a
out (app f x) with out f | x
...              | base  | ()
...              | a ⇒ b | _ = b
out (lam _) = *
out (vrf _) = *

rename : ∀ {Γ Δ} (_ : Γ ⊆ Δ) {d x} → term Γ d x → term Δ d x
rename-≡ : ∀ {Γ Δ} {p : Γ ⊆ Δ} {d x} (t : term Γ d x) → out t ≡ out (rename p t)

rename p x = ?
rename-≡ x = ?
