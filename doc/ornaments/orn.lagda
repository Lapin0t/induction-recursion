%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.orn where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π; el)
open import ornaments.pow hiding (α₀; α₁; β₀; β₁)
open import ornaments.iir hiding (α; β; γ; X; Y)
open import ornaments.induction hiding (α; β; γ; δ; X; s; t)

variable
  {α₀ α₁} : Level  -- old/new index lvl
  {β₀ β₁} : Level  -- old/new output lvl (actually new is `β₀ ⊔ β₁`)
  {γ₀ γ₁} : Level  -- old/new code lvl (actually new is `γ₀ ⊔ γ₁`)
  {X Y} : ISet α₀ β₀
  --{R S} : PRef α₁ β₁ X
\end{code}


%<*code-def>
\begin{code}
data orn₀ {-<-}{α₀ α₁ β₀ β₁ γ₀ : _}{X : ISet α₀ β₀}{->-}(γ₁ : Level) (R : PRef α₁ β₁ X) : poly γ₀ X → Set (α₀ ⊔ β₀ ⊔ β₁ ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁))
⌊_⌋₀  : {-<-}{X : ISet α₀ β₀}{R : PRef α₁ β₁ X}{ρ : poly γ₀ X}{->-}(o : orn₀ γ₁ R ρ) → poly (γ₀ ⊔ γ₁) (PFam R)
info↓ : {-<-}{X : ISet α₀ β₀}{R : PRef α₁ β₁ X}{ρ : poly γ₀ X}{->-}(o : orn₀ γ₁ R ρ) → info ⌊ o ⌋₀ → info ρ
\end{code}
%</code-def>

%<*code-impl>
\begin{code}
data orn₀ {-<-}{α₀}{α₁}{β₀}{β₁}{γ₀}{X}{->-}γ₁ R where
  ι      : (j : Code R)                                                                           → orn₀ γ₁ R (ι (down R j))
  κ      : (A : Set γ₀)                                                                           → orn₀ γ₁ R (κ A)
  σ      : {-<-}∀ {U V}{->-}(A : orn₀ γ₁ R U) (B : (a : info ⌊ A ⌋₀) → orn₀ γ₁ R (V (info↓ A a))) → orn₀ γ₁ R (σ U V)
  π      : (A : Set γ₀){-<-}{V : _}{->-} (B : (a : A) → orn₀ γ₁ R (V a))                          → orn₀ γ₁ R (π A V)

  add₀   : (A : poly (γ₀ ⊔ γ₁) (PFam R)) {-<-}{U : _}{->-}(B : info A → orn₀ γ₁ R U)              → orn₀ γ₁ R U
  add₁   : {-<-}∀ {U}{->-}(A : orn₀ γ₁ R U) (B : info ⌊ A ⌋₀ → poly (γ₀ ⊔ γ₁) (PFam R))           → orn₀ γ₁ R U
--  del :    {-<-}∀ {A : poly X} → {->-} {!  !} → orn₀ P A
  add-κ  : (A : Set (γ₀ ⊔ γ₁)){-<-}{U : _}{->-} (B : A → orn₀ γ₁ R U)                             → orn₀ γ₁ R U
  del-κ  : {-<-}∀ {A}{->-}(a : A) → orn₀ γ₁ R (κ A)
\end{code}
%</code-impl>

%<*p-interp>
\begin{code}
⌊ ι i        ⌋₀ = ι i
⌊_⌋₀ {γ₁ = γ₁} (κ A) = κ (Lift γ₁ A)
⌊ σ A B      ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B a ⌋₀
⌊_⌋₀ {γ₁ = γ₁} (π A B) = π (Lift γ₁ A) λ { (lift a) → ⌊ B a ⌋₀ }
⌊ add₀ A B   ⌋₀ = σ A λ a → ⌊ B a ⌋₀
⌊ add₁ A B   ⌋₀ = σ ⌊ A ⌋₀ B
--⌊ del _      ⌋₀ = κ ⊤
⌊ add-κ A B  ⌋₀ = σ (κ A) λ { (lift a) → ⌊ B a ⌋₀ }
⌊ del-κ _    ⌋₀ = κ ⊤
\end{code}
%</p-interp>

%<*infodown-impl>
\begin{code}
info↓ (ι i)        (lift (x , _))  = lift x
info↓ (κ A)        (lift (lift a)) = lift a
info↓ (σ A B)      (a , b)  = info↓ A a , info↓ (B a) b
info↓ (π A B)      f        = λ a → info↓ (B a) (f (lift a))
info↓ (add₀ A B)   (a , b)  = info↓ (B a) b
info↓ (add₁ A B)   (a , _)  = info↓ A a
--info↓ (del x)      _        = ?
info↓ (add-κ A B)  (lift a , b)  = info↓ (B a) b
info↓ (del-κ a)    _        = lift a
\end{code}
%</infodown-impl>



%<*orn>
\begin{code}
record orn {-<-}{α₀ α₁ β₀ β₁ γ₀}{X Y : ISet α₀ β₀}{->-}(γ₁ : Level) (R : PRef α₁ β₁ X) (S : PRef α₁ β₁ Y) (ρ : IIR γ₀ X Y) : Set (α₀ ⊔ β₀ ⊔ β₁ ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁)) where
  field
    node :  (j : Code (PFam S)) → orn₀ γ₁ R (node ρ (down S j))
    emit :  (j : Code (PFam S)) → (x : info ⌊ node j ⌋₀) → decode S j (emit ρ (down S j) (info↓ (node j) x))
\end{code}
%</orn>

\begin{code}
open orn public
\end{code}


%<*interp>
\begin{code}
⌊_⌋ : {-<-}{R : PRef α₁ β₁ X}{S : PRef α₁ β₁ Y}{ρ : IIR γ₀ X Y}{->-}(o : orn γ₁ R S ρ) → IIR (γ₀ ⊔ γ₁) (PFam R) (PFam S)
node  ⌊ o ⌋ j    = ⌊ node o j ⌋₀
emit  ⌊ o ⌋ j x  = _ , emit o j x
\end{code}
%</interp>

%<*erase>
\begin{code}
erase₀ : {-<-}{ρ : poly γ₀ X}{R : PRef α₁ β₁ X}{->-}(o : orn₀ γ₁ R ρ) (F : PObj γ₀ γ₁ R) → info↓ o >> ⟦ ⌊ o ⌋₀ ⟧ᵢ (pfam F) ⟶̃ ⟦ ρ ⟧ᵢ (ifam F)
erase₀ (ι j)       F (x , _)  = x , refl
erase₀ (κ A)       F (lift x) = x , refl
erase₀ (σ {-<-}{V = V}{->-}A B)     F (a , b)  =
  let (a' , eqa) = erase₀ A F a in
  let (b' , eqb) = erase₀ (B _) F b in
  (a' , subst (λ x → Code (⟦ V x ⟧ᵢ _)) (sym eqa) b') ,
  (cong-Σ eqa (trans  (cong₂ (λ x → decode (⟦ V x ⟧ᵢ _)) eqa (subst-elim _ $ sym eqa))  eqb))
erase₀ (π A B)     F x        =
  let aux a = erase₀ (B a) F (x $ lift a) in
  (λ a → π₀ $ aux a) , funext (λ a → π₁ $ aux a)
erase₀ (add₀ A B)  F (a , x)  = erase₀ (B $ decode (⟦ A ⟧ᵢ _) a) F x
erase₀ (add₁ A _)  F (x , _)  = erase₀ A F x
erase₀ (add-κ A B) F (a , x)  = erase₀ (B a) F x
erase₀ (del-κ a)   F _        = a , refl

erase : {-<-}{ρ : IIR γ₀ X Y}{R : PRef α₁ β₁ X}{S : PRef α₁ β₁ Y}{->-}(o : orn γ₁ R S ρ) (F : PObj γ₀ γ₁ R) → (π₀> ⟦ ⌊ o ⌋ ⟧ (pfam F)) ⇒ (⟦ ρ ⟧ (ifam F) ∘ down S)
erase {ρ = ρ} {S = S} o F i = emit ρ (down S i) <$>> erase₀ (node o i) F
\end{code}
%</erase>

%<*forget>
\begin{code}
--forget : {-<-}∀ {X} {γ : IIR X X} {P} {->-}(o : orn P P γ) → (π₀> μ ⌊ o ⌋) ⇒ (μ γ ∘ π₀)
--forget o = {! fold  !}

\end{code}
%</forget>

%<*algorn>
\begin{code}
algorn₀ : {X : ISet α₀ β₀} (ρ : poly γ₀ X) (F : 𝔽 γ₁ X) → orn₀ γ₁ (Ref F) ρ
algorn₀ = ?

--lem : ∀ {α₀ β₀ γ₀}{X : ISet α₀ β₀} (ρ : IIR γ₀ X X) (φ : alg ρ) (i : _) → info ⌊ algorn₀ (node ρ i) (obj φ) ⌋₀ → Code (obj φ i)
--lem ρ φ i x = {!   !}

algorn : {X : ISet α₀ β₀} (ρ : IIR γ₀ X X) (φ : alg ρ) → orn γ₀ (Ref (obj φ)) (Ref (obj φ)) ρ
node (algorn ρ φ) (i , j) = add₁ (algorn₀ (node ρ i) (obj φ)) λ x → κ ({!   !})
emit (algorn ρ φ) (i , j) (x , lift p) = {!   !}

remember : ∀ {α₀ β₀ γ₀ s} {X : ISet α₀ β₀} (ρ : IIR γ₀ X X) (φ : alg ρ) {i : Code X} (x : μ-c ρ {↑ s} i) → μ-c ⌊ algorn ρ φ ⌋ {↑ s} (i , π₀ $ fold φ i x)
remember ρ φ = induction ρ (λ {s} {i} x → μ-c ⌊ algorn ρ φ ⌋ {s} (i , π₀ $ fold φ i x)) {!   !}

--algorn₀ : ∀ {X} {α : IIR X X} (φ : alg α) (γ : poly X) (i : Σ _ (Code ∘ (obj φ))) → orn₀ (F→P $ obj φ) γ
--algorn₀ φ (ι x) i ac = {!   !}
--algorn₀ φ (κ A) i ac = {!   !}
--algorn₀ φ (σ γ B) i ac = {!   !}
--algorn₀ φ (π A B) i ac = π A (λ a → algorn₀ φ (B a) i (λ x → {!   !}))
--algorn₀ (ι i)   F j φ = add-κ (Code (F i)) (λ x → ι {!   !})
--algorn₀ (κ A)   F j φ = κ A
--algorn₀ (σ A B) F j φ = σ (algorn₀ A F j φ) (λ x → {!   !})
--algorn₀ (π A B) F j φ = π A (λ a → algorn₀ (B a) F j {!   !})

--alg-orn : ∀ {X} (α : IIR X X) → (φ : alg α) → orn (F→P $ obj φ) (F→P $ obj φ) α
--node (alg-orn α φ) j = ?
--emit (alg-orn α φ) j x = {! mor φ (π₀ j)  !}

\end{code}
%</algorn>


\begin{code}
--module catholic where
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
