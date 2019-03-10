module algorn where

open import prelude
open import family
open import ir
open import induction
open import ornament


Ref : ∀ {X} (F : ifam X) → idx
IN  (Ref {X} F) = Σ (IN X) (code ∘ F)
OUT (Ref {X} F) (i , c) = lift _ ⊤

RR : ∀ {X} (F : ifam X) → X ⊇ Ref F
↓-in  (RR F) (i , c) = i
↓-out (RR F) (i , c) = λ _ → dec (F i) c


algorn₀ : ∀ {X} (ρ : poly X) {F : ifam X} (x : code (⟦ ρ ⟧₀ F)) → poly (Ref F)
algorn₀-o : ∀ {X} (ρ : poly X) {F : ifam X} (x : code (⟦ ρ ⟧₀ F)) (y : info (algorn₀ ρ x)) → Σ (orn₀ (RR F) ρ (algorn₀ ρ x) y) λ α → dec (⟦ ρ ⟧₀ F) x ≡ info↓ α

algorn₀ (ι i)   c = ι (i , c)
algorn₀ (κ A)   c = κ ⊤
algorn₀ (σ A B) c =
  let α a = algorn₀-o A (π₀ c) a in
  σ (algorn₀ A (π₀ c)) (λ a → algorn₀ (B (info↓ $ π₀ (α a))) (subst (λ x → code (⟦ B x ⟧₀ _)) (π₁ $ α a) (π₁ c)))
algorn₀ (π A B) c = π A (λ a → algorn₀ (B a) (c a))

algorn₀-o (ι i)   c y = ι refl , refl
algorn₀-o (κ A)   c y = κ c , refl
algorn₀-o (σ A B) c y =
  let f , p = algorn₀-o A (π₀ c) (π₀ y) in
  let g , q = algorn₀-o (B _) (subst (λ x → code (⟦ B x ⟧₀ _)) p (π₁ c)) (π₁ y) in
  (σ-ptw f g) , Σ-ext p (trans (cong₂ (λ u v → dec (⟦ B u ⟧₀ _) v) p (sym $ coerce-coh _)) q)
algorn₀-o (π A B) c y =
  let f a = algorn₀-o (B a) (c a) (y a) in
  (π-ptw (λ a → a) (π₀ ∘ f)) , Π-ext (π₁ ∘ f)

algorn : ∀ {X} (ρ : IR X) (φ : alg ρ) → IR (Ref $ carrier φ)
algorn-o : ∀ {X} (ρ : IR X) (φ : alg ρ) → orn (RR $ carrier φ) ρ (algorn ρ φ)

node (algorn ρ φ) (i , c) = σ (κ ((π₀ ∘ app φ i) ⁻¹ c)) (λ { (↑ (ok x)) → algorn₀ (node ρ i) x })
emit (algorn ρ φ) (i , c) = λ _ → ↑ *

node-o (algorn-o ρ φ) (i , c) (↑ (ok x) , y) = x-σ₁ (π₀ $ algorn₀-o (node ρ i) x y)
emit-o (algorn-o ρ φ) (i , c) (↑ (ok x) , y) = trans (sym $ π₁ $ app φ i x) (cong (emit ρ i) (π₁ $ algorn₀-o (node ρ i) x y))


Remem : ∀ {X} {ρ : IR X} (φ : alg ρ) ..{s} (i : IN X) → μ-c ρ {s} i → Set
Remem φ {s} i x = μ-c (algorn _ φ) {s} (i , π₀ $ cata _ φ i x)

remember : ∀ {X} {ρ : IR X} (φ : alg ρ) ..{s} i x → Remem φ {s} i x
remember {ρ = ρ} φ = elim ρ (Remem φ) λ { i x h → ⟨ ok (π₀ $ ⟦ node ρ i ⟧[ cata ρ φ ]₀ x) , aux (node ρ i) x h ⟩ }
  where
    aux : ∀ ..{s} ..{t : Size< s} ρ' (x : code (⟦ ρ' ⟧₀ (μ ρ {t}))) → all ρ' (Remem φ) x → code (⟦ algorn₀ ρ' (π₀ $ ⟦ ρ' ⟧[ cata ρ φ ]₀ x) ⟧₀ (μ (algorn ρ φ) {t}))
    aux (ι i)   x h = h
    aux (κ A)   x h = *
    aux (σ A B) x h =
      let a = aux A (π₀ x) (π₀ h) in
      let b = aux (B (dec (⟦ A ⟧₀ _) _)) (π₁ x) (π₁ h) in
      a ,
      subst₂ (λ a b → code (⟦ algorn₀ (B a) b ⟧₀ _))
        (trans (π₁ (⟦ A ⟧[ _ ]₀ _)) (π₁ $ algorn₀-o A _ _))
        (sym $ trans (subst-coh _ (π₁ $ algorn₀-o A _ _)) (coerce-coh _))
        b
    aux (π A B) x h = λ a → aux (B a) (x a) (h a)

Recomp : ∀ {X} {ρ : IR X} (φ : alg ρ) ..{s} (j : IN (Ref $ carrier φ)) → μ-c (algorn ρ φ) {s} j → Set
Recomp {ρ = ρ} φ {s} j x =
    π₀ $ cata ρ φ (π₀ j) $
    π₀ $ forget (algorn-o ρ φ) (π₀ j) (ok j , x)
  ≡ π₁ j

recompute : ∀ {X} {ρ : IR X} (φ : alg ρ) ..{s} j x → Recomp φ {s} j x
recompute {ρ = ρ} φ = elim (algorn ρ φ) (Recomp φ)
  λ { (i , _) (ok c , x) (_ , h) → cong (π₀ ∘ app φ i) (aux (node ρ i) c x h) }
  where
    aux : ∀ ..{s} ..{t : Size< s} ρ'
      (c : code (⟦ ρ' ⟧₀ (carrier φ)))
      (x : code (⟦ algorn₀ ρ' c ⟧₀ (μ (algorn ρ φ) {t})))
      (h : all (algorn₀ ρ' c) (Recomp φ) x) →
        π₀ $ ⟦ ρ' ⟧[ cata ρ φ ]₀ $
        π₀ $ ⟦ ρ' ⟧[ forget (algorn-o ρ φ) ]₀ $
        π₀ $ erase₀ (π₀ $ algorn₀-o ρ' c (dec (⟦ algorn₀ ρ' c ⟧₀ _) x))
                    (μ (algorn ρ φ))
                    (ok x)
        ≡ c
    aux (ι i) c x h = h
    aux (κ A) c x h = refl
    aux (σ A B) c x h =
      let a-o , o-eq = algorn₀-o A (π₀ c) $ dec (⟦ algorn₀ A (π₀ c) ⟧₀ _) (π₀ x) in
      let e-c , e-eq = erase₀ a-o (μ (algorn ρ φ)) (ok (π₀ x)) in
      Σ-ext (aux A (π₀ c) (π₀ x) (π₀ h))
        (trans (coerce-coh _)
        $ trans (cong₂ (λ u v → π₀ $ ⟦ B u ⟧[ cata ρ φ ]₀ v)
            (sym $ trans e-eq $ π₁ $ ⟦ A ⟧[ forget (algorn-o ρ φ) ]₀ e-c)
            (trans
              (coerce-coh _)
              (cong₂ (λ u v → π₀ $ ⟦ B u ⟧[ forget (algorn-o ρ φ) ]₀ v)
                (sym e-eq)
                (coerce-coh _))))
        $ trans (aux (B $ info↓ a-o) (subst (λ u → code (⟦ B u ⟧₀ _)) o-eq (π₁ c)) (π₁ x) (π₁ h))
        $ coerce-coh _)
    aux (π A B) c x h = Π-ext (λ a → aux (B a) (c a) (x a) (h a))
