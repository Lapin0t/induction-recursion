\begin{code}
module ornaments.examples.lambda where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.pow
open import ornaments.iir
open import ornaments.induction
open import ornaments.graph


data two : Set where tt ff : two
data stack-tag : Set where ‵nil ‵snoc : stack-tag


stack-c : Set → IIR {lzero} {lzero} (⊤ , λ _ → ⊤) (⊤ , λ _ → ⊤)
node (stack-c X) _ = σ (κ stack-tag) λ { (lift ‵nil) → κ ⊤;
                                         (lift ‵snoc) → σ (ι *) λ _ → κ X }
emit (stack-c X) _ _ = *

stack : Set → Set
stack X = Σ Size λ s → μ-c (stack-c X) {s} *

infix 25 !_
pattern !_ x = _ , x

pattern ε = ⟨ ‵nil , * ⟩
infixl 26 _,,_
pattern _,,_ Γ x = ⟨ ‵snoc , Γ , x ⟩


module _ {X : Set} where
  idx-c : IIR (stack X , λ _ → X) (stack X , λ _ → X)
  node idx-c (! ε) = κ ⊥
  node idx-c (! Γ ,, x) = σ (κ two) (λ { (lift tt) → κ ⊤;
                                         (lift ff) → ι (! Γ) })
  emit idx-c (! ε)      (lift ())
  emit idx-c (! Γ ,, x) (lift tt , _) = x
  emit idx-c (! Γ ,, x) (lift ff , lift y) = y

  pattern ze = ⟨ tt , * ⟩
  pattern su i = ⟨ ff , i ⟩

  foo : IIRg idx-c
  π₀ foo ((! ε , _ , ⟨ () ⟩) , y)
  π₀ foo ((! Γ ,, x , ! ze) , y) = κ (y ≡ x)
  π₀ foo ((! Γ ,, x , ! su i) , y) = ι ((! Γ , ! i) , y)
  g-iso.to (π₁ foo) = ?
    where
      aux : (a : Σ (Σ Size (λ s → μ-c (stack-c X) *)) (λ i → Σ Size (λ s → μ-c idx-c i))) → μ-c (π₀ foo , (λ _ _ → *)) (a , μ-d idx-c (π₀ a) (π₁ (π₁ a)))
      aux (! ε ,      ! ⟨ () ⟩)
      aux (! Γ ,, x , ! ze)     = ⟨ refl ⟩
      aux (! Γ ,, x , ! su i)   = aux (! Γ , ! i)
  g-iso.from (π₁ foo) = ?
  {-π₀ foo ((! ε ,      lift ()) , y)
  π₀ foo ((! Γ ,, x , lift tt , _) , y) = κ (y ≡ x)
  π₀ foo ((! Γ ,, _ , lift ff , lift x) , y) = κ (y ≡ x)
  g-iso.to (π₁ foo) (! ε , lift ())
  g-iso.to (π₁ foo) (! Γ ,, x , lift tt , _) = ⟨ refl ⟩
  g-iso.to (π₁ foo) (! Γ ,, x , lift ff , _) = ⟨ refl ⟩
  g-iso.from (π₁ foo) ((! ε , lift ()) , y) a
  g-iso.from (π₁ foo) ((! Γ ,, x , lift tt , _) , y) ⟨ p ⟩ = p
  g-iso.from (π₁ foo) ((! Γ ,, x , lift ff , _) , y) ⟨ p ⟩ = p-}

  -- Not constructing the Fam with μ directly to hide the size and unlift the
  -- decoding
  idx : stack X → Set
  idx Γ = Σ Size λ s → μ-c idx-c {s} Γ

  get : (Γ : stack X) → idx Γ → X
  get Γ (! i) = μ-d idx-c Γ i

  idx-F : stack X → Fam _ X
  idx-F Γ = (idx Γ , get Γ)

  --Ren : stack X → stack X → Set
  --Ren Γ Δ = idx-F Γ ⟶̃ idx-F Δ

  --skip : ∀ {Γ Δ a} → Ren Γ Δ → Ren Γ (π₁ Δ ,, a)
  --skip r i = su (π₁ $ π₀ $ r i) , π₁ (r i)

  --keep : ∀ {Γ Δ a} → Ren Γ Δ → Ren (π₁ Γ ,, a) (π₁ Δ ,, a)
  --keep r ze = ze , refl
  --keep r (su i) = su (π₁ $ π₀ $ r $ ! i) , π₁ $ r $ ! i

  data ren-tag : Set where `wkn `lft : ren-tag

  ren-c : IIR (stack X × stack X , λ { (Γ , Δ) → (idx-F Γ ⟶̃ idx-F Δ) }) (stack X × stack X , λ { (Γ , Δ) → (idx-F Γ ⟶̃ idx-F Δ) })
  node ren-c (! ε ,      ! Δ)      = κ ⊤
  node ren-c (! Γ ,      ! ε)      = κ ⊥
  node ren-c (! Γ ,, a , ! Δ ,, b) = σ (κ ren-tag) (λ { (lift `wkn) → ι (! Γ ,, a , ! Δ);
                                                        (lift `lft) → σ (ι (! Γ , ! Δ)) λ _ → κ (a ≡ b) })

  --emit ren-c = ?
  emit ren-c (! ε ,      ! Δ)       r                                (! ⟨ () ⟩)
  emit ren-c (! Γ ,, a , ! ε)       (lift ())                        (! i)
  emit ren-c (! Γ ,, a , ! Δ ,, b)  (lift `wkn , lift r)             (! ze)   = let ! j , p = r (! ze) in ! su j , p
  emit ren-c (! Γ ,, a , ! Δ ,, b)  (lift `wkn , lift r)             (! su i) = let ! j , p = r (! su i) in ! su j , p
  emit ren-c (! Γ ,, a , ! Δ ,, .a) (lift `lft , lift r , lift refl) (! ze)   = ! ze , refl
  emit ren-c (! Γ ,, a , ! Δ ,, .a) (lift `lft , lift r , lift refl) (! su i) = let ! j , p = r (! i) in ! su j , p

  ren : stack X → stack X → Set
  ren Γ Δ = Σ Size λ s → μ-c ren-c {s} (Γ , Δ)

  pattern wkn r = ⟨ `wkn , r ⟩
  pattern lft r p = ⟨ `lft , r , p ⟩


data type : Set where
  `base : type
  _`⇒_ : type → type → type

data dir : Set where chk syn : dir

IN : Set
IN = Σ dir λ { chk → type; syn → ⊤ }

OUT : IN → Set
OUT (chk , _) = ⊤
OUT (syn , _) = type

data syn-tag : Set where `var `app `ann : syn-tag
data chk-tag : Set where `lam `vrf : chk-tag

term-c : IIR (stack type × IN , OUT ∘ π₁) (stack type × IN , OUT ∘ π₁)

node term-c (! Γ , chk , `base)  = σ (ι (! Γ ,      syn , *)) λ { (lift s) → κ (s ≡ `base) }
node term-c (! Γ , chk , a `⇒ b) = σ (ι (! Γ ,, a , syn , *)) λ { (lift s) → κ (s ≡ b) }
--node term-c (Γ , chk , o) = σ (κ chk-tag)
--  λ { (lift `lam) → σ (κ type) λ { (lift a) →
--                    σ (ι (! π₁ Γ ,, a , syn , *)) λ { (lift b) →
--                    κ (o ≡ (a `⇒ b)) } };
--      (lift `vrf) → σ (ι (Γ , syn , *)) λ { (lift a) → κ (o ≡ a) } }
node term-c (Γ , syn , *) = σ (κ syn-tag)
  λ { (lift `var) → κ (idx Γ);
      (lift `app) → σ (ι (Γ , syn , *)) λ { (lift `base) → κ ⊥;
                                            (lift (a `⇒ b)) → ι (Γ , chk , a) };
      (lift `ann) → σ (κ type) (λ { (lift a) → ι (Γ , chk , a) }) }

emit term-c (Γ , chk , _) _                                = *
emit term-c (Γ , syn , *) (lift `var , lift i)             = get Γ i
emit term-c (Γ , syn , *) (lift `app , lift `base , lift ())
emit term-c (Γ , syn , *) (lift `app , lift (a `⇒ b) , _)  = b
emit term-c (Γ , syn , *) (lift `ann , lift a , _)         = a

--term-g : IIRg term-c
--π₀ term-g (((Γ , chk , _) , x) , o) = κ ⊤
--π₀ term-g (((Γ , syn , *) , lift `var , lift i) , o) = κ (μ-i (π₀ foo) ((Γ , {!   !}) , o))
--π₀ term-g (((Γ , syn , *) , lift `app , lift `base , lift ()) , o)
--π₀ term-g (((Γ , syn , *) , lift `app , lift (a `⇒ b) , _) , o) = κ (o ≡ b)
--π₀ term-g (((Γ , syn , *) , lift `ann , lift a , _) , o) = κ (o ≡ a)
--π₁ term-g = {!   !}


{-term : stack type → _ → Set
term Γ i = Σ Size λ s → μ-C term-c {s} (Γ , i)

out : ∀ {Γ i} → term Γ i → OUT i
out x = lower $ μ-d term-c _ (π₁ x)

term-F : (Γ : stack type) → (i : IN) → Fam (Lift $ OUT i)
term-F Γ i = term Γ i , lift ∘ out

term-P : (Γ : stack type) → (i : IN) → Pow (Lift $ OUT i)
term-P Γ i = (term Γ i) , λ { x o → o ≡ lift $ out x }

pattern lam {a} x p = ⟨ `lam , a , x , p ⟩
pattern vrf x p = ⟨ `vrf , x , p ⟩
pattern var i = ⟨ `var , i ⟩
pattern app x y = ⟨ `app , x , y ⟩
pattern ann s x = ⟨ `ann , s , x ⟩-}



--rename : ∀ {Γ Δ} → ren Γ Δ → 

\end{code}
