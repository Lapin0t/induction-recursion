open import Data.Product
open import Function


open Σ renaming (proj₁ to π₀; proj₂ to π₁)

data inv {I J : Set} (e : J → I) : I → Set where
  ok : (j : J) → inv e (e j)


-- a couple equivalences between categories

-- objects of (fam I) / X
[fam_]/_ : (I : Set) → (I → Set₁) → Set₁
[fam I ]/ X = Σ (I → Set) (λ A → (i : I) → A i → X i)

-- objects of I / (Σ I X)
type/Σ : (I : Set) → (I → Set₁) → Set₁
type/Σ I X = Σ Set (λ A → A → Σ I X)

-- objects of fam (I / X)
fam[_/_] : (I : Set) → (I → Set₁) → Set₁
fam[ I / X ] = (i : I) → Σ Set (λ A → A → X i)


T→F₂ : ∀ {I X} → type/Σ I X → [fam I ]/ X
T→F₂ (A , f) = inv (π₀ ∘ f) , λ { _ (ok a) → π₁ (f a) }

T→F₁ : ∀ {I X} → type/Σ I X → fam[ I / X ]
T→F₁ (A , f) i = (inv (π₀ ∘ f) i) , λ { (ok a) → π₁ (f a) }

F₂→T : ∀ {I X} → [fam I ]/ X → type/Σ I X
F₂→T {I} {X} (U , T) = (Σ I U) , (λ { (i , u) → i , T i u})

F₂→F₁ : ∀ {I X} → [fam I ]/ X → fam[ I / X ]
F₂→F₁ (U , T) i = U i , T i

F₁→T : ∀ {I X} → fam[ I / X ] → type/Σ I X
F₁→T {I} f = Σ I (π₀ ∘ f) , λ { (i , x) → i , π₁ (f i) x }

F₁→F₂ : ∀ {I X} → fam[ I / X ] → [fam I ]/ X
F₁→F₂ f = (π₀ ∘ f) , λ i x → π₁ (f i) x
