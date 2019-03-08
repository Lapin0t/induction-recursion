module ornament where

open import prelude
open import family
open import ir
open import induction


-- Pre-ornaments for node functors. Here `orn₀ ρ₀ ρ₁ := info ρ₁ → info ρ₀` could
-- have been a candidate, but it isn't precise enough to get the subnode (recursive)
-- case right. Indeed, `info (ι i)` should not be attainable out of the blue, we
-- really want to ensure that there is a matching subnode in the ornamented version,
-- not just that we can extract some `OUT Y j` from somewhere (possibly a constant!).
data orn₀ {X Y} (R : X ⊇ Y) : poly X → (ρ₁ : poly Y) → info ρ₁ → Set₁
info↓ : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁ x} → orn₀ R ρ₀ ρ₁ x → info ρ₀

data orn₀ {X} {Y} R where
  ι : ∀ {i j x} → i ≡ ↓-in R j                                            → orn₀ R (ι i)   (ι j)   x
  σ : ∀ {A B ρ₁ x} (f : orn₀ R A ρ₁ x) (g : orn₀ R (B $ info↓ f) ρ₁ x)    → orn₀ R (σ A B) ρ₁      x
  κ : ∀ {A ρ₁ x} → A                                                      → orn₀ R (κ A)   ρ₁      x
  π : ∀ {A B ρ₁ x} (f : (a : A) → orn₀ R (B a) ρ₁ x)                      → orn₀ R (π A B) ρ₁      x

  -- weakenings
  x-π : ∀ {ρ₀ A B x} (a : A) (f : orn₀ R ρ₀ (B a) (x a))                  → orn₀ R ρ₀      (π A B) x
  x-σ₀ : ∀ {ρ₀ A B x} (f : orn₀ R ρ₀ A (π₀ x))                            → orn₀ R ρ₀      (σ A B) x
  x-σ₁ : ∀ {ρ₀ A B x} (g : orn₀ R ρ₀ (B $ π₀ x) (π₁ x))                   → orn₀ R ρ₀      (σ A B) x

info↓ {R = R} {x = x} (ι refl)  = ↓-out R _ x
info↓ {x = x} (σ f g)   = info↓ f , info↓ g
info↓ {x = x} (κ a)     = ↑ a
info↓ {x = x} (π f)     = λ a → info↓ (f a)
info↓ {x = x} (x-π a f) = info↓ f
info↓ {x = x} (x-σ₀ f)  = info↓ f
info↓ {x = x} (x-σ₁ g)  = info↓ g

σ-ptw : ∀ {X Y} {R : X ⊇ Y} {A A' B B' x} (f : orn₀ R A A' (π₀ x)) (g : orn₀ R (B $ info↓ f) (B' (π₀ x)) (π₁ x)) → orn₀ R (σ A B) (σ A' B') x
σ-ptw f g = σ (x-σ₀ f) (x-σ₁ g)

π-ptw : ∀ {X Y} {R : X ⊇ Y} {A A' B B' x} (f : A → A') (g : (a : A) → orn₀ R (B a) (B' $ f a) (x $ f a)) → orn₀ R (π A B) (π A' B') x
π-ptw f g = π λ a → x-π (f a) (g a)

-- Compute a natural transformation between ⟦ ρ₁ ⟧₀ and ⟦ ρ₀ ⟧₀. More precisely, on the left
-- we postcompose with `info↓` and on the right we precompose with the action of the reindexing,
-- yielding two functors [ifam Y, fam (info ρ₀)].
erase₀ : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁} {y} (α : orn₀ R ρ₀ ρ₁ y) (F : ifam Y) → dec (⟦ ρ₁ ⟧₀ F) ⁻¹ y → Σ (code (⟦ ρ₀ ⟧₀ (F / R))) λ x → info↓ α ≡ dec (⟦ ρ₀ ⟧₀ (F / R)) x
erase₀ (ι refl)  F (ok x) = _ , x , refl
erase₀ (σ {B = B} f g)   F x =
  let a , m = erase₀ f F x in
  let b , p = erase₀ g F x in
  a , subst (λ x → code (⟦ B x ⟧₀ (F / _))) m b ,
  Σ-ext m (trans p (cong₂ (λ u v → dec (⟦ B u ⟧₀ (F / _)) v) m (sym $ coerce-coh _)))
erase₀ (κ a)     F (ok x) = a , refl
erase₀ (π f)     F x =
  let f a = erase₀ (f a) F x in
  π₀ ∘ f , Π-ext (π₁ ∘ f)
erase₀ (x-π a f) F (ok x) = erase₀ f F (ok $ x a)
erase₀ (x-σ₀ f)  F (ok x) = erase₀ f F (ok $ π₀ x)
erase₀ (x-σ₁ g)  F (ok x) = erase₀ g F (ok $ π₁ x)

-- Full ornaments: we pre-ornament the node at every index and give a coherence equation
-- for the decoding.
record orn {X Y} (R : X ⊇ Y) (ρ₀ : IR X) (ρ₁ : IR Y) : Set₁ where
  field
    node-o : (j : IN Y) (x : info (node ρ₁ j)) → orn₀ R (node ρ₀ (↓-in R j)) (node ρ₁ j) x
    emit-o : (j : IN Y) (x : info (node ρ₁ j)) → ↓-out R j (emit ρ₁ j x) ≡ emit ρ₀ (↓-in R j) (info↓ (node-o j x))
open orn public

-- Natural transformation between ⟦ ρ₁ ⟧ and ⟦ ρ₀ ⟧. Again, on the left we postcompose with the action
-- of the reindexing, and on the right we precompose by it, pre-erasure and the coherance fall nicely
-- into place.
erase : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁} (α : orn R ρ₀ ρ₁) (F : ifam Y) → (⟦ ρ₁ ⟧ F / R) ⇒ ⟦ ρ₀ ⟧ (F / R)
erase {R = R} {ρ₀ = ρ₀} α F _ (ok j , x) =
  let y , p = erase₀ (node-o α j _) F (ok x) in
  y , trans (emit-o α j _) (cong (emit ρ₀ (↓-in R j)) p)

-- With containers, now we would define the ornamental algebra, but it doesn't seem like there is a
-- way to make something similar for IR. Indeed `forget` isn't a fold. Notice how we use the action
-- `⟦ ρ₀ ⟧[ forget α ]`, which should hint at a fold on `⟦ ρ₀ ⟧`, but the source of the morphism is
-- a `μ ρ₁`. Indeed, the morphism works top down, not bottom up: given a `⟦ ρ₁ ⟧ (μ ρ₁) / R`, eg a
-- fancy family with stripped down output, we erase it's head, yielding a `⟦ ρ₀ ⟧ (μ ρ₁ / R)`, eg a
-- stripped down head where subnodes are fancy families with stripped down output. From there we can
-- recursively strip down subnodes and pack everything back up.
-- This expression could also work on containers, which seems to hint that `forget` being able to
-- work bottom-up is a specificity of containers that gets lost when generalizing to IR. Indeed
-- on containers the action of a reindexing just a precomposition, wherease on IR it is a
-- precomposition on the input index (right of the arrow) and a post-composition on the output (left
-- of the arrow). Being a post-composition, there is no way to fixup the input and feed a `μ ρ₀` to a
-- `⟦ ρ₁ ⟧`: we can only do it the other way around.
-- This may be an instance of a generic recursion scheme being the fusion of a catamorphism (on ρ₁)
-- followed by an anamorphism (on ρ₀), with the intermediary carrier being `μ ρ₁`. The catamorphism
-- is trivial here: it is simply a `μ-out` as expressed by the pattern matching.

forget : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁} (α : orn R ρ₀ ρ₁) ..{s : Size} → (μ ρ₁ {s} / R) ⇒ μ ρ₀ {s}
forget {ρ₀ = ρ₀} {ρ₁ = ρ₁} α _ (ok j , ⟨ x ⟩) = (μ-in ⊙ ⟦ ρ₀ ⟧[ forget α ] ⊙ erase α (μ ρ₁)) _ (ok j , x)
