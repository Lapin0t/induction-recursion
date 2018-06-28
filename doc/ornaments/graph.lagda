%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.graph {α β} where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
--open import ornaments.pow
open import ornaments.iir
open import ornaments.induction
--open import ornaments.induction
--open import ornaments.trans hiding (foo)

--lft : ∀ {α} {A : Set (lsuc α)} → Fam A → Fam (Lift A)
--Code (lft F) = Lift (Code F)
--decode (lft F) (lift x) = lift (decode F x)


{-record Lift' {α β} (A : Set α) : Set (α ⊔ β) where
  constructor lift
  field
    lower' : A
open Lift' public-}


{-lft : ∀ {α} → ISet α → ISet (lsuc α)
Code (lft X) = Lift $ Code X
decode (lft X) (lift i) = Lift $ decode X i

LF-↓ : ∀ {α} {X : ISet α} → (LF X) ⊂ lft X
up   LF-↓ (lift (i , _)) = lift i
down LF-↓ i _ = *

-----------

_!>_ : ∀ {α} {X Y Z : ISet (lsuc α)} (f : Z ⊂ Y) → IIR X Y → IIR X Z
node (f !> α) j = node α (up f j)
emit (f !> α) j = down f j ∘ emit α (up f j)

sub₀ : ∀ {α} {X Y : ISet (lsuc α)} → X ⊂ Y → poly X → poly Y
inf₀ : ∀ {α} {X Y : ISet (lsuc α)} (f : X ⊂ Y) (γ : poly X) → info (sub₀ f γ) → info γ

sub₀ f (ι i) = ι (up f i)
sub₀ f (κ A) = κ A
sub₀ f (σ A B) = σ (sub₀ f A) λ a → sub₀ f (B (inf₀ f A a))
sub₀ f (π A B) = π A λ a → sub₀ f (B a)

inf₀ f (ι i) x = down f i x
inf₀ f (κ A) x = x
inf₀ f (σ A B) (a , b) = inf₀ f A a , inf₀ f (B _) b
inf₀ f (π A B) x = λ a → inf₀ f (B a) (x a)

_<!_ : ∀ {α} {X Y Z : ISet (lsuc α)} → IIR X Z → X ⊂ Y → IIR Y Z
node (γ <! f) j = sub₀ f (node γ j)
emit (γ <! f) j = emit γ j ∘ inf₀ f (node γ j)

bump₀ : ∀ {α} {X : ISet (lsuc α)} → poly X → poly (lft X)
bump₀-d : ∀ {α} {X : ISet (lsuc α)} (γ : poly X) → info (bump₀ γ) → info γ

bump₀ (ι i) = ι (lift i)
bump₀ (κ A) = κ (Lift A)
bump₀ (σ A B) = σ (bump₀ A) λ a → bump₀ (B (bump₀-d A a))
bump₀ (π A B) = π (Lift A) (λ a → bump₀ (B $ lower a))

bump₀-d (ι i) (lift x) = x
bump₀-d (κ A) (lift x) = x
bump₀-d (σ A B) (a , b) = bump₀-d A a , bump₀-d (B _) b
bump₀-d (π A B) x = λ a → bump₀-d (B a) (x $ lift a)

bump : ∀ {α} {X Y : ISet (lsuc α)} → IIR X Y → IIR (lft X) (lft Y)
node (bump γ) (lift j) = bump₀ (node γ j)
emit (bump γ) (lift j) x = lift (emit γ j (bump₀-d (node γ j) x))-}


-------------

LF : ISet α β → ISet (α ⊔ β) lzero
Code (LF X) = Σ (Code X) (decode X)
decode (LF X) _ = ⊤


G₀ : ∀ {X} → poly X → poly (LF X)
dg₀ : ∀ {X} (γ : poly X) → info (G₀ γ) → info γ

G₀ {X} (ι i) = σ (κ (Lift α (decode X i))) λ { (lift (lift j)) → ι (i , j) }
G₀ (κ A) = κ (Lift β A)
G₀ (σ A B) = σ (G₀ A) λ x → G₀ (B (dg₀ A x))
G₀ (π A B) = π (Lift β A) λ { (lift a) → G₀ (B a) }

dg₀ (ι i) (lift j , _) = j
dg₀ (κ A) (lift a) = a
dg₀ (σ A B) (a , b) = dg₀ A a , dg₀ (B _) b
dg₀ (π A B) x = λ a → dg₀ (B a) (x $ lift a)

ext : ∀ {X} (γ : poly X) (F : 𝔽 X) → Fam (α ⊔ β) (info γ)
ext γ F = dg₀ γ >> ⟦ G₀ γ ⟧ᵢ λ { (i , j) → (Σ (Lift β $ Code (F i)) (λ y → decode (F i) (lower y) ≡ j)) , λ _ → * }

η-G₀ : ∀ {X} (γ : poly X) (F : 𝔽 X) → ⟦ γ ⟧ᵢ F ⟶̃ ext γ F
η-G₀ (ι i) F x = (lift $ decode (F i) x , lift x , refl) , refl
η-G₀ (κ A) F x = lift x , refl
η-G₀ (σ A B) F (a , b) =
  let B' x = ⟦ G₀ (B x) ⟧ᵢ _ in
  let a' , p = η-G₀ A F a in
  let b' , q = η-G₀ (B _) F b in
  (a' , subst (Code ∘ B') (sym p) b') ,
  cong-Σ p (trans  (cong₂ (λ x → dg₀ (B x) ∘ decode (B' x)) p (subst-elim _ _)) q)
η-G₀ (π A B) F x =
  (λ { (lift a) → π₀ $ η-G₀ (B a) F (x a) }) ,
  funext (λ a → π₁ $ η-G₀ (B a) F (x a))

G : ∀ {X Y} (γ : IIR X Y) → IIR (LF X) (LF Y)
node (G γ) (i , j) = σ (G₀ (node γ i)) λ x → κ (Lift α (emit γ i (dg₀ (node γ i) x) ≡ j))
emit (G γ) (i , j) _ = *

to-G : ∀ {X Y} (γ : IIR X Y) (F : 𝔽 X) (j : Code Y) (x : Code (⟦ γ ⟧ F j)) → Code (⟦ G γ ⟧ _ (j , decode (⟦ γ ⟧ F j) x))
to-G γ F j x = π₀ $ η-G₀ (node γ j) F x , lift $ cong (emit γ j) (π₁ $ η-G₀ (node γ j) F x)

η-G₀⁻¹ : ∀ {X} (γ : poly X) (F : 𝔽 X) → ext γ F ⟶̃ ⟦ γ ⟧ᵢ F
η-G₀⁻¹ (ι i) F (lift j , lift x , p) = x , cong lift p
η-G₀⁻¹ (κ A) F (lift a) = a , refl
η-G₀⁻¹ (σ A B) F (a , b) = {!   !}
η-G₀⁻¹ (π A B) F x = (λ a → π₀ $ η-G₀⁻¹ (B a) F (x $ lift a)) , funext λ a → π₁ $ η-G₀⁻¹ (B a) F (x $ lift a)

from-G : ∀ {X Y} (γ : IIR X Y) (F : 𝔽 X) (j : Code Y) (a : decode Y j) (x : Code (⟦ G γ ⟧ _ (j , a))) → Σ (Code (⟦ γ ⟧ F j)) λ y → decode (⟦ γ ⟧ F j) y ≡ a
from-G γ F j y (x , lift p) = π₀ $ η-G₀⁻¹ (node γ j) F x , (trans (cong (emit γ j) (π₁ $ η-G₀⁻¹ (node γ j) F x)) p)

GF : ∀ {X : ISet α β} (γ : IIR X X) → Set (α ⊔ β)
GF {X} γ = Σ (Σ (Code X) λ i → Σ Size λ s → μ-c γ {s} i) λ { (i , _) → decode X i }

record g-iso {α β γ} {X : ISet α β} (f : el X) (g : sing X → Set γ) : Set (α ⊔ β ⊔ γ) where
  field
    to : (a : _) → g (a , f a)
    from : (s : sing X) → g s → π₁ s ≡ f (π₀ s)

uncurry : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : (a : A) → B a → Set γ}
          (f : (a : A) → (b : B a) → C a b) → (x : Σ A B) → C (π₀ x) (π₁ x)
uncurry f (x , y) = f x y

-- TODO: move this
IND : ∀ {α} (X Y : Set α) → Set (lsuc α)
IND X Y = Y → poly {β = lzero} (X , λ _ → ⊤)

μ-i : ∀ {α} {X : Set α} (γ : IND X X) {s : Size} (i : X) → Set α
μ-i γ = μ-c (γ , λ _ _ → *)

IIRg : {X : ISet α β} (γ : IIR X X) → Set (lsuc (α ⊔ β))
IIRg γ = Σ (IND (GF γ) (GF γ)) (λ δ → {s : Size} → g-iso (λ { (i , (_ , x)) → μ-d γ i x }) (μ-i δ {s}))
--Σ (IND (GF γ) (GF γ)) λ δ → {s : Size} → g-iso (uncurry $ emit γ) (μ-i δ {s})


--gr : {X Y : ISet α β} (γ : IIR X Y) → Set ?
--gr γ = {! IIR   !}

\end{code}
