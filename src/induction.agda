module induction where

open import prelude
open import family
open import ir


μ : ∀ {X} (ρ : IR X) ..{s : Size} → ifam X

{-# NO_POSITIVITY_CHECK #-}
data μ-c {X} (ρ : IR X) ..{s : Size} (i : IN X) : Set where
  ⟨_⟩ : ..{t : Size< s} → code (⟦ ρ ⟧ (μ ρ {t}) i) → μ-c ρ {s} i

μ-d : ∀ {X} (ρ : IR X) ..{s} (i : IN X) → μ-c ρ {s} i → OUT X i
μ-d ρ i ⟨ x ⟩ = dec (⟦ ρ ⟧ (μ ρ) i) x

code (μ ρ {s} i) = μ-c ρ {s} i
dec (μ ρ {s} i) = μ-d ρ {s} i

μ-in : ∀ {X} {ρ : IR X} ..{s} ..{t : Size< s} → ⟦ ρ ⟧ (μ ρ {t}) ⇒ μ ρ {s}
μ-in i x = ⟨ x ⟩ , refl

--μ-out : ∀ {X} {ρ : IR X} ..{sI}

--constr₁ : ∀ {X} {ρ : IR X} {F} ..{s} (m : ..{t : Size< s} → F ⇒ ⟦ ρ ⟧ (μ ρ {t})) → F ⇒ μ ρ {s}
--π₀ (constr₁ m i x) = ? --⟨ π₀ $ m i x ⟩
--π₁ (constr₁ m i x) = ? --π₁ $ m i x

all : ∀ {α X} (ρ : poly X) {F : ifam X} (P : ∀ i → code (F i) → Set α) → code (⟦ ρ ⟧₀ F) → Set α
all (ι i)   P x       = P i x
all (κ A)   P _       = lift _ ⊤
all (σ A B) P (a , b) = all A P a × all (B _) P b
all (π A B) P f       = (a : A) → all (B a) P (f a)

every : ∀ {α X} (ρ : poly X) {F : ifam X} (P : ∀ i → code (F i) → Set α)
  (h : (i : _) (x : code (F i)) → P i x) (x : code (⟦ ρ ⟧₀ F)) → all ρ P x
every (ι i)   P h x       = h i x
every (κ A)   P h x       = ↑ *
every (σ A B) P h (a , b) = every A P h a , every (B _) P h b
every (π A B) P h f       = λ a → every (B a) P h (f a)

elim : ∀ {α X} (ρ : IR X) (P : ∀ ..{s} i → code (μ ρ {s} i) → Set α)
  (hyp : ∀ ..{s} ..{t : Size< s} i x → all (node ρ i) P x → P {s} i ⟨ x ⟩)
  ..{s} i x → P {s} i x
elim ρ P hyp i ⟨ x ⟩ = hyp i x $ every (node ρ i) P (elim ρ P hyp) x

record alg {X} (ρ : IR X) : Set₁ where
  constructor ⟨_⟩
  field
    {carrier} : ifam X
    app : ⟦ ρ ⟧ carrier ⇒ carrier
open alg public

cata : ∀ {X} (ρ : IR X) (φ : alg ρ) ..{s} → μ ρ {s} ⇒ carrier φ
cata ρ φ i ⟨ x ⟩ = (app φ ⊙ ⟦ ρ ⟧[ cata ρ φ ]) i x
  --where
   -- aux : μ ρ ⇒ ⟦ ρ ⟧ (carrier φ)
  --  aux i ⟨ x ⟩ = ⟦ ρ ⟧[ cata ρ φ ] i x

--record alg₁ {X₀ X₁} (ρ : IR X₀) (R : X₀ ⊇ X₁) : Set₁ where
--  constructor ⟨_⟩
--  field
--    {carrier₁} : ifam X₁
--    app₁ : ([ R ]⟦ ρ ⟧ carrier₁ ∘ ↓-in R) ⇒ (↓-out R <<ᵢ carrier₁)
--open alg₁ public

--cata₁ : ∀ {X₀ X₁} ..{s} {R : X₀ ⊇ X₁} {ρ : IR X₀} (φ : alg₁ ρ R) → (μ ρ {s} ∘ ↓-in R) ⇒ (↓-out R <<ᵢ carrier₁ φ)
--catam₁ : ∀ {X₀ X₁} ..{s} {R : X₀ ⊇ X₁} {ρ : IR X₀} (φ : alg₁ ρ R) → μ ρ {s} ⇒ [ R ]⟦ ρ ⟧ (carrier₁ φ)
--catam₁ : ∀ {X} ..{s} {} {ρ : IR X} (φ : alg ρ) → μ ρ {s} ⇒ ⟦ ρ ⟧ (carrier φ)

--cata₁ = ?
--catam₁ = ?

{-record alg' {X} (ρ : IR X) : Set₁ where
  constructor ⟨_⟩
  field
    {carrier} : ifam X
    app : ∀ {s} → ⟦ ρ ⟧ (μ ρ {s} ⊗ carrier) ⇒ carrier
open alg' public

para : ∀ {X s} {ρ : IR X} (φ : alg' ρ) → μ ρ {s} ⇒ carrier φ
param : ∀ {X s} {ρ : IR X} (φ : alg' ρ) → μ ρ {s} ⇒ ⟦ ρ ⟧ (μ ρ {s} ⊗ carrier φ)

para φ = app φ ⊙ param φ

param {ρ = ρ} φ i ⟨ x ⟩ = let y , p = ⟦ ρ ⟧[ para φ ] i x in {!   !} , {!   !}-}
