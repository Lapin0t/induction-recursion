module iir where

open import utils
open import fam using (Fam; Code; decode; _,_; 𝔽; _•_)


------------------------------------------------------------------------
-- Codes.


data poly (X : Fam Set₁) : Set₁
info : {X : Fam Set₁} → poly X → Set₁

data poly X where
  ι : Code X → poly X
  κ : (A : Set) → poly X
  σ : (A : poly X) → (B : info A → poly X) → poly X
  π : (A : Set) → (B : A → poly X) → poly X

info {X} (ι i) = decode X i
info (κ A) = Lift A
info (σ A B) = Σ (info A) λ x → info (B x)
info (π A B) = (a : A) → info (B a)



------------------------------------------------------------------------
-- Expression of FCT definitions as a functors.


record FCT (X Y : Fam Set₁) : Set₁ where
  constructor _,_
  field
    node : (y : Code Y) → poly X
    emit : (y : Code Y) → info (node y) → decode Y y
open FCT public

⟦_⟧ᵢ : ∀ {X} → (p : poly X) → 𝔽 X → Fam (info p)

⟦ ι i ⟧ᵢ F = F i
⟦ κ A ⟧ᵢ F = (A , lift)
⟦ σ A B ⟧ᵢ F = fam.σ (⟦ A ⟧ᵢ F) λ a → ⟦ B a ⟧ᵢ F
⟦ π A B ⟧ᵢ F = fam.π A λ a → ⟦ B a ⟧ᵢ F

⟦_⟧ : {X Y : Fam Set₁} → (α : FCT X Y) → 𝔽 X → 𝔽 Y
⟦ node , emit ⟧ F j = emit j • ⟦ node j ⟧ᵢ F

--⟦_⟧F : ∀ {X Y} (α : FCT X Y) {F G : 𝔽 X} → (F ⇒ G) → ⟦ α ⟧ F ⇒ ⟦ α ⟧ G
--⟦ α ⟧F f j = (λ x → {! π₀ (f ?)  !}) , {!   !}


------------------------------------------------------------------------
-- Composition of Codes

--pow : {X Y : Fam Set₁} → ((y : Code Y))
uncurry : (A : Fam Set₁) → (B : Code A → Fam Set₁) → Fam Set₁
Code (uncurry A B) = Σ (Code A) (Code ∘ B)
decode (uncurry A B) (a , b) = decode (B a) b

--pow : ∀ {X} (A : Fam Set₁) {B : Code A → Fam Set₁} → ((a : decode A) ⟶̊ FCT X (B a)) → FCT X (uncurry A B)
--node (pow A f) (a , b) = node (f a) b
--emit (pow A f) (a , b) x = emit (f a) b {!   !}

{-pow : ∀ {D} (A : Set) {E : A → Set₁} → ((a : A) → FCT* D (E a)) → FCT* D ((a : A) → E a)
pow A f = (π A (π₀ ∘ f) , λ z a → π₁ (f a) (z a))
`
η : ∀ {D E} → E → FCT* D E
η e = (k ⊤ , λ _ → e)

μ' : ∀ {D E} → FCT* D (FCT* D E) → FCT* D E
μ' (c , α) = (σ c (λ z → π₀ (α z))) , λ { (c' , α') → π₁ (α c') α' }

_<$>_ : ∀ {D E F} → (E → F) → FCT* D E → FCT* D F
f <$> c = (π₀ c , f ∘ (π₁ c))

_>>=_ : ∀ {C D E} → FCT* C D → ((x : D) → FCT* C (E x)) → FCT* C (Σ D E)
(c , α) >>= h = μ' (c , λ x → (π₀ (h (α x)) , λ y → (α x , π₁ (h (α x)) y)))

_/_ : ∀ {D E} → (c : poly E) → FCT D E → FCT* D (info c)
ι i / R = R i
k A / R = (k A , λ a → a)
σ S f / R = (S / R) >>= (λ s → f s / R)
π P f / R = pow P (λ p → f p / R)

_⊙_ : ∀ {J C D} {E : J → _} → FCT D E → FCT C D → FCT C E
(γ ⊙ R) i = π₁ (γ i) <$> (π₀ (γ i) / R)-}


------------------------------------------------------------------------
-- Initial algebra and Code interpretation

μ : ∀ {X} → FCT X X → 𝔽 X

{-# NO_POSITIVITY_CHECK #-}
data μ-Code {X} (α : FCT X X) (x : Code X) : Set

{-# TERMINATING #-}
μ-dec : ∀ {X} → (α : FCT X X) → (x : Code X) → μ-Code α x → decode X x

Code (μ α x) = μ-Code α x
decode (μ α x) = μ-dec α x

data μ-Code α x where
  ⟨_⟩ : Code (⟦ α ⟧ (μ α) x) → μ-Code α x

μ-dec α x ⟨ c ⟩ = emit α x (decode (⟦ node α x ⟧ᵢ (μ α)) c)


{-fmap : ∀ {D E} {X Y : obj D} (γ : FCT D E) → (X ⟶̃ Y) → ⟦ γ ⟧ X ⟶̃ ⟦ γ ⟧ Y
fmap γ f i with γ i
...        | ι i′ , α = π₀ (f i′) , cong (_∘_ α) (π₁ (f i′))
...        | k A , α = (λ a → a) , refl
...        | σ A B , α = (λ { (a , b) → {! π₀ (fmap ? f a) !} , {!   !} }) , {!   !}
...        | π A B , α = (λ f a → {! fmap (B a , ?)  !}) , {!   !}-}

--fmap-p : ∀ {D E} {X Y : obj D} (γ : poly D) → (X ⟶̃ Y) → ⟦ γ ⟧₀ X → ⟦ γ ⟧₀ Y
--fmap-p (ι i) f x = π₀ (f i) x
--fmap-p (k A) f x = x
--fmap-p (σ A B) f (a , b) = (fmap-p A f a , fmap-p (B _) f {!   !})
--fmap-p (π A B) f x = λ a → fmap-p (B a) f (x a)
