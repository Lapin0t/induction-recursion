%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.orn where

open import ornaments.prelude
open import ornaments.fam using (Fam; _,_; Code; decode; _⇒_; _>>_; _⟶̃_)
open import ornaments.iir


pow : (X : Fam Set₁) → Set₂
pow (I , X) = Σ (I → Set) (λ J → (ij : Σ I J) → X (π₀ ij) → Set₁)

pow→fam : ∀ {X} → (P : pow X) → Fam Set₁
Code (pow→fam {I , _} (J , _)) = Σ I J
decode (pow→fam {_ , X} (_ , Y)) (i , j) = Σ (X i) (Y (i , j))



data poly-orn {X : Fam Set₁} (Y : pow X) : poly X → Set₁
info+ : ∀ {X Y γ} → poly-orn {X} Y γ → Set₁
info↓ : ∀ {X Y γ} (o : poly-orn {X} Y γ) → info+ o → info γ

data poly-orn {X} Y where
  -- structure preserving
  ι : {i : Code X} → (π₀ Y i) → poly-orn Y (ι i)
  κ : (A : Set) → poly-orn Y (κ A)
  σ : ∀ {P Q} → (A : poly-orn Y P) → (B : (a : info+ A) → poly-orn Y (Q (info↓ A a))) → poly-orn Y (σ P Q)
  π : (A : Set) → ∀ {P} → (B : (a : A) → poly-orn Y (P a)) → poly-orn Y (π A P)

  -- insertions/deletions
  -- OPTION 1
  add : (A : poly (pow→fam Y)) → ∀ {P} → (B : info A → poly-orn Y P) → poly-orn Y P
  del : ∀ {A : poly X} → (x : info A) → poly-orn Y A
  -- OPTION 2
  add-κ : (A : Set) → ∀ {P} → (Lift A → poly-orn Y P) → poly-orn Y P
  del-κ : ∀ {A} → (a : A) → poly-orn Y (κ A)

info+ {_ , X} {_ , Y} (ι {i} j) = Σ (X i) (Y (i , j))
info+ (κ A) = Lift A
info+ (σ A B) = Σ (info+ A) (λ a → info+ (B a))
info+ (π A B) = (a : A) → info+ (B a)
info+ (add A B) = Σ (info A) (λ a → info+ (B a))
info+ (del _) = Lift ⊤
info+ (add-κ A B) = Σ (Lift A) (λ a → info+ (B a))
info+ (del-κ _) = Lift ⊤

info↓ (ι i) (x , _) = x
info↓ (κ A) a = a
info↓ (σ A B) (a , b) = info↓ A a , info↓ (B a) b
info↓ (π A B) f = λ a → info↓ (B a) (f a)
info↓ (add A B) (a , b) = info↓ (B a) b
info↓ (del x) _ = x
info↓ (add-κ A B) (a , b) = info↓ (B a) b
info↓ (del-κ a) _ = lift a


-- interpret back to plain poly
⌊_⌋₀ : ∀ {X Y} {γ : poly X} → poly-orn Y γ → poly (pow→fam Y)
info↑ : ∀ {X Y} {γ : poly X} (o : poly-orn Y γ) → info ⌊ o ⌋₀ ≡ info+ o

⌊ ι {i} j ⌋₀ = ι (i , j)
⌊ κ A ⌋₀ = κ A
⌊ σ A B ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B (subst (λ x → x) (info↑ A) a) ⌋₀
⌊ π A B ⌋₀ = π A λ a → ⌊ B a ⌋₀
⌊ add A B ⌋₀ = σ A λ a → ⌊ B a ⌋₀
⌊ del _ ⌋₀ = κ ⊤
⌊ add-κ A B ⌋₀ = σ (κ A) λ { a → ⌊ B a ⌋₀ }
⌊ del-κ _ ⌋₀ = κ ⊤

info↑ (ι j) = refl
info↑ (κ A) = refl
info↑ (σ A B) = cong₂ Σ (info↑ A) (lem' (info↑ A) (funext λ x → info↑ (B x)))
  where lem' : {A₀ A₁ : Set₁} → {B₀ B₁ : A₁ → Set₁} → (p : A₀ ≡ A₁) → (B₀ ≡ B₁) → B₀ ∘ subst (λ x → x) p ≡ B₁
        lem' refl refl = refl
info↑ (π A B) = cong (λ f → (a : A) → f a) (funext λ a → info↑ (B a))
info↑ (add A B) = cong (Σ (info A)) (funext λ x → info↑ (B x))
info↑ (del _) = refl
info↑ (add-κ A B) = cong (Σ (Lift A)) (funext λ a → info↑ (B a))
info↑ (del-κ _) = refl


record orn {X Y : Fam Set₁} (P : pow X) (Q : pow Y) (γ : IIR X Y) : Set₁ where
  field
    node : (j : Code Y) → poly-orn P (node γ j)
    emit : (jk : Σ (Code Y) (π₀ Q)) → info+ (node (π₀ jk)) → Σ (decode Y (π₀ jk)) (π₁ Q jk)

open orn public


⌊_⌋ : ∀ {X Y P Q} {γ : IIR X Y} (o : orn P Q γ) → IIR (pow→fam P) (pow→fam Q)
node ⌊ o ⌋ (j , y) = ⌊ node o j ⌋₀
emit ⌊ o ⌋ (j , y) x = emit o (j , y) (subst (λ x → x) (info↑ (node o j)) x)

forget : ∀ {X} {γ : IIR X X} {P} (o : orn P P γ) → (ij : _) → (π₀ >> (μ ⌊ o ⌋ ij)) ⟶̃ μ γ (π₀ ij)
forget o = {!⌊ o ⌋!}


module catholic where

  data inv {α β} {A : Set α} {B : Set β} (f : A → B) : B → Set α where
    ok : (x : A) → inv f (f x)

  to-pow : ∀ {X Y} → (E : Code Y → Code X) → (e : (y : Code Y) → decode Y y → decode X (E y)) → pow X
  π₀ (to-pow E e) x = inv E x
  π₁ (to-pow E e) (x , ok y) a = inv (e y) a
\end{code}
