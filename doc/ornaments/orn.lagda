%include agda.fmt
  {-<-}-- insertions/deletions{->-}
%include ornaments.fmt

\begin{code}
module ornaments.orn where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.pow
open import ornaments.iir
\end{code}


%<*code-def>
\begin{code}
data orn₀ {-<-}{X : Fam Set₁}{->-} (P : ℙ X) : poly X → Set₁
⌊_⌋₀ : {-<-}∀ {X P} {γ : poly X} →{->-} orn₀ P γ → poly (PFam P)
info↓ : {-<-}∀ {X P γ}{->-} (o : orn₀ {-<-}{X}{->-} P γ) → info ⌊ o ⌋₀ → info γ
\end{code}
%</code-def>

%<*code-impl>
\begin{code}
data orn₀ {-<-}{X} {->-}P where
  ι :      (i : Code (PFam P)) → orn₀ P (ι (π₀ i))
  κ :      (A : Set) → orn₀ P (κ A)
  σ :      {-<-}∀ {A′ B′} → {->-}(A : orn₀ P A′) → (B : (a : info ⌊ A ⌋₀) → orn₀ P (B′ (info↓ A a))) → orn₀ P (σ A′ B′)
  π :      (A : Set) → {-<-}∀ {B′} →{->-} (B : (a : A) → orn₀ P (B′ a)) → orn₀ P (π A B′)

  add :    (A : poly (PFam P)) → {-<-}∀ {A′} → {->-}(B : info A → orn₀ P A′) → orn₀ P A′
  del :    {-<-}∀ {A : poly X} → {->-} {!  !} → orn₀ P A
  add-κ :  (A : Set) → {-<-}∀ {A′} →{->-} (A → orn₀ P A′) → orn₀ P A′
  del-κ :  {-<-}∀ {A} → {->-}(a : A) → orn₀ P (κ A)
\end{code}
%</code-impl>

%<*p-interp>
\begin{code}
⌊ ι i        ⌋₀ = ι i
⌊ κ A        ⌋₀ = κ A
⌊ σ A B      ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B a ⌋₀
⌊ π A B      ⌋₀ = π A λ a → ⌊ B a ⌋₀
⌊ add A B    ⌋₀ = σ A λ a → ⌊ B a ⌋₀
⌊ del _      ⌋₀ = κ ⊤
⌊ add-κ A B  ⌋₀ = σ (κ A) λ a → ⌊ B (lower a) ⌋₀
⌊ del-κ _    ⌋₀ = κ ⊤
\end{code}
%</p-interp>

%<*infodown-impl>
\begin{code}
info↓ (ι i)        (x , _)  = x
info↓ (κ A)        a        = a
info↓ (σ A B)      (a , b)  = info↓ A a , info↓ (B a) b
info↓ (π A B)      f        = λ a → info↓ (B a) (f a)
info↓ (add A B)    (a , b)  = info↓ (B a) b
info↓ (del x)      _        = ?
info↓ (add-κ A B)  (a , b)  = info↓ (B (lower a)) b
info↓ (del-κ a)    _        = lift a
\end{code}
%</infodown-impl>



%<*orn>
\begin{code}
record orn {-<-}{X Y : Fam Set₁} {->-}(P : ℙ X) (Q : ℙ Y) (γ : IIR X Y) : Set₁ where
  field
    node :  (j : Code (PFam Q)) → orn₀ P (node γ (π₀ j))
    emit :  (j : Code (PFam Q)) → (x : info ⌊ node j ⌋₀) → Rel (Q (π₀ j)) (π₁ j) (emit γ (π₀ j) (info↓ (node j) x))
\end{code}
%</orn>

\begin{code}
open orn public
\end{code}


%<*interp>
\begin{code}
⌊_⌋ : {-<-}∀ {X Y P Q} {γ : IIR X Y} {->-}(o : orn P Q γ) → IIR (PFam P) (PFam Q)
node  ⌊ o ⌋ j    = ⌊ node o j ⌋₀
emit  ⌊ o ⌋ j x  = _ , emit o j x
\end{code}
%</interp>

%<*erase>
\begin{code}
erase₀ : ∀ {X} {α : poly X} {P} (o : orn₀ P α) {F : 𝔽 X} {R : 𝔽 (PFam P)} → (π₀> R) ⇒ (F ∘ π₀) → info↓ o >> ⟦ ⌊ o ⌋₀ ⟧ᵢ R ⟶̃ ⟦ α ⟧ᵢ F
erase₀ (ι i) F x = F i x
erase₀ (κ A) F a = a , refl
erase₀ (σ {B′ = B′} A B) F (a , b) =
  let (a' , eqa) = erase₀ A F a in
  let (b' , eqb) = erase₀ (B _) F b in
  (a' , subst (λ x → Code (⟦ B′ x ⟧ᵢ _)) (sym eqa) b') ,
  (cong-Σ eqa (trans  (cong₂ (λ x → decode (⟦ B′ x ⟧ᵢ _)) eqa (subst-elim _ $ sym eqa))  eqb))
erase₀ (π A B) F f = (λ a → π₀ $ erase₀ (B a) F (f a)) , funext (λ a → π₁ $ erase₀ (B a) F (f a))
erase₀ (add A B) F (a , x) = erase₀ (B (decode (⟦ A ⟧ᵢ _) a)) F x
erase₀ (del x) F _ = {!   !} , {!   !}
erase₀ (add-κ A B) F (a , x) = erase₀ (B a) F x
erase₀ (del-κ a) F _ = a , refl

erase : ∀ {X Y} {α : IIR X Y} {P Q} (o : orn P Q α) {F : 𝔽 X} {R : 𝔽 (PFam P)} → (π₀> R) ⇒ (F ∘ π₀) → (π₀> ⟦ ⌊ o ⌋ ⟧ R) ⇒ (⟦ α ⟧ F ∘ π₀)
erase {α = α} o F i = emit α (π₀ i) <$>> erase₀ (node o i) F

\end{code}
%</erase>

%<*algorn>
\begin{code}
--algorn₀ : ∀ {X} {α : IIR X X} (φ : alg α) (γ : poly X) (i : Σ _ (Code ∘ (obj φ))) → orn₀ (F→P $ obj φ) γ
--algorn₀ φ (ι x) i ac = {!   !}
--algorn₀ φ (κ A) i ac = {!   !}
--algorn₀ φ (σ γ B) i ac = {!   !}
--algorn₀ φ (π A B) i ac = π A (λ a → algorn₀ φ (B a) i (λ x → {!   !}))
--algorn₀ (ι i)   F j φ = add-κ (Code (F i)) (λ x → ι {!   !})
--algorn₀ (κ A)   F j φ = κ A
--algorn₀ (σ A B) F j φ = σ (algorn₀ A F j φ) (λ x → {!   !})
--algorn₀ (π A B) F j φ = π A (λ a → algorn₀ (B a) F j {!   !})

alg-orn : ∀ {X} (α : IIR X X) → (φ : alg α) → orn (F→P $ obj φ) (F→P $ obj φ) α
node (alg-orn α φ) j = ?
emit (alg-orn α φ) j x = {! mor φ (π₀ j)  !}

\end{code}
%</algorn>


%<*forget>
\begin{code}
{-forget : {-<-}∀ {X} {γ : IIR X X} {P} {->-}(o : orn P P γ) → μ {!(node ⌊ o ⌋) , ? !} ⇒ (μ γ ∘ π₀)
forget o = {!fold!}-}
\end{code}
%</forget>



\begin{code}
module catholic where
\end{code}

%<*catholic>
\begin{code}
  {-data inv {-<-}{α β} {A : Set α} {B : Set β} {->-}(f : A → B) : B → Set α where
    ok : (x : A) → inv f (f x)

  to-pow : {-<-}∀ {X Y} → {->-}(E : Code Y → Code X) → (e : (y : Code Y) → decode Y y → decode X (E y)) → pow X
  π₀ (to-pow E e)             = inv E
  π₁ (to-pow E e) (_ , ok y)  = inv (e y)

  --from-pow : ∀ {X} → (P : pow X) → Σ (Code (pow⁻¹ P) → Code X) (λ E → (j : Code (pow⁻¹ P)) → decode (pow⁻¹ P) j → decode )-}
\end{code}
%</catholic>
