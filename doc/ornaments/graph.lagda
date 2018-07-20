%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.graph where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.pow
open import ornaments.iir hiding (α; β; γ)
open import ornaments.orn hiding (α₀; α₁; β₀; β₁; γ₀; γ₁)


variable
  {α β γ} : Level

PLF : (X : ISet α β) → PRef (α ⊔ β) lzero X
Code (PLF X) = Σ (Code X) (decode X)
down (PLF X) (x , _) = x
decode (PLF X) j x = ⊤

G₀-orn : {X : ISet α β} (ρ : poly γ X) → orn₀ (β ⊔ γ) (PLF X) ρ
G₀-orn {γ = γ} {X = X} (ι i) = add₀ (κ (Lift γ (decode X i))) λ { (lift y) → ι (i , lower y) }
G₀-orn (κ A) = κ
G₀-orn (σ A B) = σ (G₀-orn A) (λ a → G₀-orn (B (info↓ a)))
G₀-orn (π A B) = π (λ a → G₀-orn (B a))

G-orn : {X Y : ISet α β} (ρ : IIR γ X Y) → orn (β ⊔ γ) (PLF X) (PLF Y) ρ
node (G-orn {γ = γ} ρ) (i , y) = add₁ (G₀-orn (node ρ i)) λ x → κ (Lift γ (emit ρ i (info↓ x) ≡ y))
emit (G-orn ρ) j x = *


{-G₀ : ∀ {γ X} → poly γ X → poly (β ⊔ γ) (LF X)
dg₀ : ∀ {γ X} (ρ : poly γ X) → info (G₀ ρ) → info ρ

G₀ {γ} {X} (ι i) = σ (κ (Lift γ (decode X i))) λ { (lift (lift j)) → ι (i , j) }
G₀ (κ A) = κ (Lift β A)
G₀ (σ A B) = σ (G₀ A) λ x → G₀ (B (dg₀ A x))
G₀ (π A B) = π (Lift β A) λ { (lift a) → G₀ (B a) }

dg₀ (ι i) (lift j , _) = j
dg₀ (κ A) (lift a) = a
dg₀ (σ A B) (a , b) = dg₀ A a , dg₀ (B _) b
dg₀ (π A B) x = λ a → dg₀ (B a) (x $ lift a)

F-g : ∀ {γ X} → 𝔽 γ X → 𝔽 (β ⊔ γ) (LF X)
Code (F-g F (i , j)) = Σ (Lift β $ Code (F i)) (λ { (lift k) → decode (F i) k ≡ j })
decode (F-g F (i , j)) _ = *

ext : ∀ {γ X} (ρ : poly γ X) (F : 𝔽 γ X) → Fam (β ⊔ γ) (info ρ)
ext γ F = dg₀ γ >> ⟦ G₀ γ ⟧ᵢ (F-g F)

η-G₀ : ∀ {γ X} (ρ : poly γ X) (F : 𝔽 γ X) → ⟦ ρ ⟧ᵢ F ⟶̃ ext ρ F
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

G : ∀ {γ X Y} (ρ : IIR γ X Y) → IIR (β ⊔ γ) (LF X) (LF Y)
node (G {γ} ρ) (i , j) = σ (G₀ (node ρ i)) λ x → κ (Lift γ (emit ρ i (dg₀ (node ρ i) x) ≡ j))
emit (G γ) (i , j) _ = *

to-G : ∀ {γ X Y} (ρ : IIR γ X Y) (F : 𝔽 γ X) (j : Code Y) (x : Code (⟦ ρ ⟧ F j)) → Code (⟦ G ρ ⟧ (F-g F) (j , decode (⟦ ρ ⟧ F j) x))
to-G γ F j x = π₀ $ η-G₀ (node γ j) F x , lift $ cong (emit γ j) (π₁ $ η-G₀ (node γ j) F x)

η-G₀⁻¹ : ∀ {γ X} (ρ : poly γ X) (F : 𝔽 γ X) → ext ρ F ⟶̃ ⟦ ρ ⟧ᵢ F
η-G₀⁻¹ (ι i) F (_ , lift x , p) = x , cong lift p
η-G₀⁻¹ (κ A) F (lift a) = a , refl
η-G₀⁻¹ (σ A B) F (a , b) =
  let B' x = ⟦ B x ⟧ᵢ F in
  let a' , p = η-G₀⁻¹ A F a in
  let b' , q = η-G₀⁻¹ (B _) F b in
  (a' , subst (Code ∘ B') (sym p) b') ,
  cong-Σ p (trans (cong₂ (decode ∘ B') p (subst-elim _ _)) q)
η-G₀⁻¹ (π A B) F x = (λ a → π₀ $ η-G₀⁻¹ (B a) F (x $ lift a)) , funext λ a → π₁ $ η-G₀⁻¹ (B a) F (x $ lift a)

from-G : ∀ {γ X Y} (ρ : IIR γ X Y) (F : 𝔽 γ X) (j : Code Y) (a : decode Y j) (x : Code (⟦ G ρ ⟧ (F-g F) (j , a))) → Σ (Code (⟦ ρ ⟧ F j)) λ y → decode (⟦ ρ ⟧ F j) y ≡ a
from-G γ F j y (x , lift p) = π₀ $ η-G₀⁻¹ (node γ j) F x , (trans (cong (emit γ j) (π₁ $ η-G₀⁻¹ (node γ j) F x)) p)-}

----


{-GF : ∀ {X : ISet α β} (γ : IIR X X) → Set (α ⊔ β)
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
IIRg γ = Σ (IND (GF γ) (GF γ)) (λ δ → {s : Size} → g-iso (λ { (i , (_ , x)) → μ-d γ i x }) (μ-i δ {s}))-}
--Σ (IND (GF γ) (GF γ)) λ δ → {s : Size} → g-iso (uncurry $ emit γ) (μ-i δ {s})


--gr : {X Y : ISet α β} (γ : IIR X Y) → Set ?
--gr γ = {! IIR   !}

\end{code}
