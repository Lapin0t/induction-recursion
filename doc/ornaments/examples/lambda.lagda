\begin{code}
module ornaments.examples.lambda where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.pow
open import ornaments.iir


data two : Set where tt ff : two
data stack-tag : Set where ‵nil ‵snoc : stack-tag


stack-c : Set → IIR (⊤ , λ _ → Lift ⊤) (⊤ , λ _ → Lift ⊤)
node (stack-c X) _ = σ (κ stack-tag) λ { (lift ‵nil) → κ ⊤;
                                         (lift ‵snoc) → σ (ι *) λ _ → κ X }
emit (stack-c X) _ _ = lift *

stack : Set → Set
stack X = Σ Size λ s → μ-C (stack-c X) {s} *

pattern !_ x = _ , x
pattern ε = ! ⟨ ‵nil , * ⟩
pattern _,,_ Γ x = ! ⟨ ‵snoc , Γ , x ⟩


module _ {X : Set} where
  idx-c : IIR (stack X , λ _ → Lift X) (stack X , λ _ → Lift X)
  node idx-c ε = κ ⊥
  node idx-c (Γ ,, x) = σ (κ two) (λ { (lift tt) → κ ⊤;
                                       (lift ff) → ι (! Γ) })
  emit idx-c ε (lift ())
  emit idx-c (Γ ,, x) (lift tt , _) = lift x
  emit idx-c (Γ ,, x) (lift ff , y) = y

  -- Not constructing the Fam with μ directly to hide the size and unlift the
  -- decoding
  idx : stack X → Set
  idx Γ = Σ Size λ s → μ-C idx-c {s} Γ

  get : (Γ : stack X) → idx Γ → X
  get Γ i = lower $ μ-d idx-c Γ (π₁ i)

  idx-F : stack X → Fam X
  idx-F Γ = (idx Γ , get Γ)

  pattern ze = ! ⟨ tt , * ⟩
  pattern su i = ! ⟨ ff , i ⟩

  Ren : stack X → stack X → Set
  Ren Γ Δ = idx-F Γ ⟶̃ idx-F Δ

  skip : ∀ {Γ Δ a} → Ren Γ Δ → Ren Γ (π₁ Δ ,, a)
  skip r i = su (π₁ $ π₀ $ r i) , π₁ (r i)

  keep : ∀ {Γ Δ a} → Ren Γ Δ → Ren (π₁ Γ ,, a) (π₁ Δ ,, a)
  keep r ze = ze , refl
  keep r (su i) = su (π₁ $ π₀ $ r $ ! i) , π₁ $ r $ ! i


data type : Set where
  ‵base : type
  _‵⇒_ : type → type → type

data dir : Set where chk syn : dir

IN : Set
IN = Σ dir λ { chk → type; syn → ⊤ }

OUT : IN → Set
OUT (chk , _) = ⊤
OUT (syn , _) = type

data syn-tag : Set where `var `app `ann : syn-tag
data chk-tag : Set where `lam `vrf : chk-tag

term-c : IIR (stack type × IN , Lift ∘ OUT ∘ π₁) (stack type × IN , Lift ∘ OUT ∘ π₁)

node term-c (Γ , chk , o) = σ (κ chk-tag)
  λ { (lift `lam) → σ (κ type) λ { (lift a) →
                    σ (ι (π₁ Γ ,, a , syn , *)) λ { (lift b) →
                    κ (o ≡ (a ‵⇒ b)) } };
      (lift `vrf) → σ (ι (Γ , syn , *)) λ { (lift a) → κ (o ≡ a) } }
node term-c (Γ , syn , _) = σ (κ syn-tag)
  λ { (lift `var) → κ (idx Γ);
      (lift `app) → σ (ι (Γ , syn , *)) λ { (lift ‵base) → κ ⊥;
                                            (lift (a ‵⇒ b)) → ι (Γ , chk , a) };
      (lift `ann) → σ (κ type) (λ { (lift a) → ι (Γ , chk , a) }) }

emit term-c (Γ , chk , _) _                                = lift *
emit term-c (Γ , syn , _) (lift `var , lift i)             = lift (get Γ i)
emit term-c (Γ , syn , _) (lift `app , lift ‵base , lift ())
emit term-c (Γ , syn , _) (lift `app , lift (a ‵⇒ b) , _)  = lift b
emit term-c (Γ , syn , _) (lift `ann , lift a , _)         = lift a


term : stack type → _ → Set
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
pattern ann s x = ⟨ `ann , s , x ⟩
\end{code}
