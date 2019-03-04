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
data orn₀ {X Y} (R : X ⊇ Y) : poly X → poly Y → Set₁
info↓ : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁} → orn₀ R ρ₀ ρ₁ → info ρ₁ → info ρ₀

data orn₀ {X} {Y} R where
  -- a subnode must be matched in the fancy version
  ι : ∀ {i j} → i ≡ ↓-in R j                                            → orn₀ R (ι i)   (ι j)
  -- or it could be on the right of a function, at some particular input (a : A)
  ι-π : ∀ {i A B} (a : A) → orn₀ R (ι i) (B a)                          → orn₀ R (ι i)   (π A B)
  -- left of a sigma
  ι-σ₀ : ∀ {i A B} → orn₀ R (ι i) A                                     → orn₀ R (ι i)   (σ A B)
  -- right of a sigma
  ι-σ₁ : ∀ {i A B} → ((a : info A) → orn₀ R (ι i) (B a))                → orn₀ R (ι i)   (σ A B)

  -- ornamenting a constant is simply being able to extract it from the info
  κ : ∀ {A ρ₁} (f : info ρ₁ → A)                                        → orn₀ R (κ A)   ρ₁
  -- ornamenting a sigma is ornamenting both its components
  σ : ∀ {A B ρ₁} (f : orn₀ R A ρ₁) (g : (a : info A) → orn₀ R (B a) ρ₁) → orn₀ R (σ A B) ρ₁
  -- ornamenting a pi is ornamenting it pointwise
  π : ∀ {A B ρ₁} (f : (a : A) → orn₀ R (B a) ρ₁)                        → orn₀ R (π A B) ρ₁

info↓ {R = R} (ι refl) x = ↓-out R _ x
info↓ (ι-π a f) x = info↓ f (x a)
info↓ (ι-σ₀ f)  x = info↓ f (π₀ x)
info↓ (ι-σ₁ g)  x = info↓ (g $ π₀ x) (π₁ x)
info↓ (κ f)     x = ↑ (f x)
info↓ (σ f g)   x = info↓ f x , info↓ (g _) x
info↓ (π f)     x = λ a → info↓ (f a) x

-- Compute a natural transformation between ⟦ ρ₁ ⟧₀ and ⟦ ρ₀ ⟧₀. More precisely, on the left
-- we postcompose with `info↓` and on the right we precompose with the action of the reindexing,
-- yielding two functors [ifam Y, fam (info ρ₀)].
erase₀ : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁} (α : orn₀ R ρ₀ ρ₁) (F : ifam Y) → (info↓ α << ⟦ ρ₁ ⟧₀ F) ⟶ ⟦ ρ₀ ⟧₀ (F / R)
erase₀ (ι refl)  F x = _ , refl
erase₀ (ι-π a f) F x = erase₀ f F (x a)
erase₀ (ι-σ₀ f)  F x = erase₀ f F (π₀ x)
erase₀ (ι-σ₁ {A = A} g)  F x = erase₀ (g $ dec (⟦ A ⟧₀ F) (π₀ x)) F (π₁ x)
erase₀ (κ f)     F x = _ , refl
erase₀ (σ {B = B} {ρ₁ = ρ₁} f g)   F x =
  let nfo = dec (⟦ ρ₁ ⟧₀ F) x in
  let a , m = erase₀ f F x in
  let b , p = erase₀ (g (info↓ f nfo)) F x in
  a , subst (λ x → code (⟦ B x ⟧₀ (F / _))) m b ,
  Σ-ext m (trans p (cong₂ (λ u v → dec (⟦ B u ⟧₀ (F / _)) v) m (sym $ coerce-coh _)))
erase₀ (π f)     F x =
  let m = λ a → erase₀ (f a) F x in
  π₀ ∘ m , Π-ext (π₁ ∘ m)

-- Full ornaments: we pre-ornament the node at every index and give a coherence equation
-- for the decoding.
record orn {X Y} (R : X ⊇ Y) (ρ₀ : IR X) (ρ₁ : IR Y) : Set₁ where
  field
    node-o : (j : IN Y) → orn₀ R (node ρ₀ (↓-in R j)) (node ρ₁ j)
    emit-o : (j : IN Y) (x : info (node ρ₁ j)) → ↓-out R j (emit ρ₁ j x) ≡ emit ρ₀ (↓-in R j) (info↓ (node-o j) x)
open orn public

-- Natural transformation between ⟦ ρ₁ ⟧ and ⟦ ρ₀ ⟧. Again, on the left we postcompose with the action
-- of the reindexing, and on the right we precompose by it, pre-erasure and the coherance fall nicely
-- into place.
erase : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁} (α : orn R ρ₀ ρ₁) (F : ifam Y) → (⟦ ρ₁ ⟧ F / R) ⇒ ⟦ ρ₀ ⟧ (F / R)
erase {R = R} {ρ₀ = ρ₀} α F _ (ok j , x) =
  let y , p = erase₀ (node-o α j) F x in
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

-------

aux₀ : ∀ {X Y} {R : X ⊇ Y} {F G} → F ⇒ G [ R ] → (F / R) ⇒ G
aux₀ m _ (ok j , x) = m j x

aux₁ : ∀ {X Y} {R : X ⊇ Y} {F G} → (F / R) ⇒ G → F ⇒ G [ R ]
aux₁ {R = R} m i x = m (↓-in R i) (ok i , x)

  --erase : (F : ifam Y) → (⟦ ρ₁ ⟧ F / R) ⇒ ⟦ ρ₀ ⟧ (F / R)
  --π₀ (erase F _ (ok i , x)) = π₀ $ act (node-o α i) F x
  --π₁ (erase F _ (ok i , x)) = trans (emit-o α i _) (cong (emit ρ₀ _) (π₁ $ act (node-o α i) F x))

  --ornalg : ..{s : Size} ..{t : Size< s} → (⟦ ρ₁ ⟧ (μ ρ₁ {t}) / R) ⇒ μ ρ₀ {s}
  --forget : ..{s : Size} → (μ ρ₁ {s} / R) ⇒ μ ρ₀ {s}

  --ornalg = μ-in ⊙ ⟦ ρ₀ ⟧[ forget ] ⊙ erase (μ ρ₁)
  --forget _ (ok i , ⟨ x ⟩) = ornalg _ (ok i , x)

--cata₁ : ∀ {X Y} {R : X ⊇ Y} {ρ} {A : ifam X} {F : ifam Y} (inj : ⟦ ρ ⟧ F ⇒ A [ R ]) (φ : ⟦ ρ ⟧ F ⇒ A [ R ]) ..{s} → μ ρ {s} ⇒ A [ R ]
--cata₁-aux : ∀ {X Y} {R : X ⊇ Y} {ρ} {A : ifam X} {F : ifam Y} (inj : ⟦ ρ ⟧ F ⇒ A [ R ]) (φ : ⟦ ρ ⟧ F ⇒ A [ R ]) ..{s} → μ ρ {s} ⇒ ⟦ ρ ⟧ F

--π₀ (cata₁ inj φ i x) = π₀ $ inj i $ π₀ $ cata₁-aux inj φ i x --π₀ $ inj i $ π₀ $ cata₁-aux inj φ i x
--π₁ (cata₁ inj φ i x) = {!π₁ $ cata₁-aux inj φ i x !}

--cata₁-aux {ρ = ρ} inj φ {s} i ⟨ x ⟩ = ⟦ ρ ⟧[ cata₁ inj φ ] i x
--π₀ (cata' {ρ = ρ} inj φ i ⟨ x ⟩) = π₀ $ φ i $ π₀ $ ⟦ ρ ⟧[ cata-aux inj φ ] i x
--π₁ (cata' {ρ = ρ} inj φ i ⟨ x ⟩) = {!   !}

--π₀ (forget o {s} i ⟨ x ⟩) = ⟨ {!   !} ⟩
--π₁ (forget o {s} i ⟨ x ⟩) = {!   !}

--record orn {X Y} (R : X ⊇ Y) (ρ₀ : IR X) (ρ₁ : IR Y) : Set₁ where
--  field
--    ↓-nfo : (j : _) → info (node ρ₁ j) → info (node ρ₀ (↓-in R j))
--    coh : (j : _) (x : info (node ρ₁ j)) → ↓-out R j (emit ρ₁ j x) ≡ emit ρ₀ (↓-in R j) (↓-nfo j x)
--open orn public

--erase₀ : ∀ {X Y} {R : X ⊇ Y} {ρ₀ ρ₁} (dwn : info ρ₁ → info ρ₀) (coh : ?) (F : ifam Y) → (dwn << ⟦ ρ₁ ⟧₀ F) ⟶ ⟦ ρ₀ ⟧₀ (⌊ F ⌋ R)
--erase₀ {ρ₁ = ρ₁} dwn coh₁ F x = {!   !}


--module comb {X₀ X₁} {R : X₀ ⊇ X₁} where
--  ιι : ∀ {i j} → i ≡ ↓-in R j → orn₀ R (ι i) (ι j)
--  ιι refl x = ↓-out R _ x
--
--  ππ : ∀ {A₀ A₁ B₀ B₁} (f : A₀ → A₁) → ((x : _) → orn₀ R (B₀ x) (B₁ (f x))) → orn₀ R (π A₀ B₀) (π A₁ B₁)
--  ππ f g x = λ a → g a (x $ f a)
--
--  σσ : ∀ {A₀ A₁ B₀ B₁} (f : orn₀ R A₀ A₁) → ((x : _) → orn₀ R (B₀ (f x)) (B₁ x)) → orn₀ R (σ A₀ B₀) (σ A₁ B₁)
--  σσ f g (x , y) = f x , g x y
--
--  xσ₀ : ∀ {ρ₀ A₁ B₁} → orn₀ R ρ₀ A₁ → orn₀ R ρ₀ (σ A₁ B₁)
--  xσ₀ f (x , _) = f x
--
--  xσ₁ : ∀ {ρ₀ A₁ B₁} → ((x : _) → orn₀ R ρ₀ (B₁ x)) → orn₀ R ρ₀ (σ A₁ B₁)
--  xσ₁ g (x , y) = g x y
--
--  σx : ∀ {A₀ B₀ ρ₁} (f : orn₀ R A₀ ρ₁) → ((x : _) → info (B₀ (f x))) → orn₀ R (σ A₀ B₀) ρ₁
--  σx f g x = f x , g x
