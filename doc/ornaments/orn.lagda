%include agda.fmt
  {-<-}-- insertions/deletions{->-}
%include ornaments.fmt

\begin{code}
module ornaments.orn where

open import ornaments.prelude
open import ornaments.fam using (Fam; _,_; Code; decode; _⇒_; _>>_; _⟶̃_)
open import ornaments.iir
\end{code}


%<*pow>
\begin{code}
pow : Fam Set₁ → Set₂
pow (I , X) = Σ (I → Set) (λ J → (ix : Σ I J) → X (π₀ ix) → Set₁)

pow⁻¹ : {-<-}∀ {X} →{->-} (P : pow X) → Fam Set₁
Code (pow⁻¹ {-<-}{I , _}{->-} (J , _)) = Σ I J
decode (pow⁻¹ {-<-}{_ , X}{->-} (_ , Y)) (i , j) = Σ (X i) (Y (i , j))
\end{code}
%</pow>


%<*code-def>
\begin{code}
data orn₀ {-<-}{X : Fam Set₁}{->-} (Y : pow X) : poly X → Set₁
info+ : {-<-}∀ {X Y γ} →{->-} orn₀ {-<-}{X}{->-} Y γ → Set₁
info↓ : {-<-}∀ {X Y γ}{->-} (o : orn₀ {-<-}{X}{->-} Y γ) → info+ o → info γ
\end{code}
%</code-def>

%<*code-impl>
\begin{code}
data orn₀ {-<-}{X} {->-}Y where
  ι :      {-<-}{i : Code X} → {->-}(π₀ Y i) → orn₀ Y (ι i)
  κ :      (A : Set) → orn₀ Y (κ A)
  σ :      {-<-}∀ {P Q} → {->-}(A : orn₀ Y P) → (B : (a : info+ A) → orn₀ Y (Q (info↓ A a))) → orn₀ Y (σ P Q)
  π :      (A : Set) → {-<-}∀ {P} →{->-} (B : (a : A) → orn₀ Y (P a)) → orn₀ Y (π A P)

  {-<-}-- OPTION 1{->-}
  add :    (A : poly (pow⁻¹ Y)) → {-<-}∀ {P} → {->-}(B : info A → orn₀ Y P) → orn₀ Y P
  del :    {-<-}∀ {A : poly X} → {->-}(x : info A) → orn₀ Y A
  {-<-}-- OPTION 2{->-}
  add-κ :  (A : Set) → {-<-}∀ {P} →{->-} (A → orn₀ Y P) → orn₀ Y P
  del-κ :  {-<-}∀ {A} → {->-}(a : A) → orn₀ Y (κ A)
\end{code}
%</code-impl>

%<*info+-impl>
\begin{code}
info+ {-<-}{_ , X} {_ , Y} {->-}(ι {-<-}{i} {->-}j)        = Σ (X i) (Y (i , j))
info+ (κ A)        = Lift A
info+ (σ A B)      = Σ (info+ A) (λ a → info+ (B a))
info+ (π A B)      = (a : A) → info+ (B a)
info+ (add A B)    = Σ (info A) (λ a → info+ (B a))
info+ (del _)      = Lift ⊤
info+ (add-κ A B)  = Σ (Lift A) λ a → info+ (B (lower a))
info+ (del-κ _)    = Lift ⊤
\end{code}
%</info+-impl>

%<*infodown-impl>
\begin{code}
info↓ (ι i)        (x , _)  = x
info↓ (κ A)        a        = a
info↓ (σ A B)      (a , b)  = info↓ A a , info↓ (B a) b
info↓ (π A B)      f        = λ a → info↓ (B a) (f a)
info↓ (add A B)    (a , b)  = info↓ (B a) b
info↓ (del x)      _        = x
info↓ (add-κ A B)  (a , b)  = info↓ (B (lower a)) b
info↓ (del-κ a)    _        = lift a
\end{code}
%</infodown-impl>


%<*orn>
\begin{code}
record orn {-<-}{X Y : Fam Set₁} {->-}(P : pow X) (Q : pow Y) (γ : IIR X Y) : Set₁ where
  field
    node :  (j : Code (pow⁻¹ Q)) → orn₀ P (node γ (π₀ j))
    emit :  (j : Code (pow⁻¹ Q)) → info+ (node j) → decode (pow⁻¹ Q) j
\end{code}
%</orn>

\begin{code}
open orn public
\end{code}


%<*p-interp>
\begin{code}
⌊_⌋₀ : {-<-}∀ {X Y} {γ : poly X} →{->-} orn₀ Y γ → poly (pow⁻¹ Y)
info↑ : {-<-}∀ {X Y} {γ : poly X} {->-}(o : orn₀ Y γ) → info ⌊ o ⌋₀ ≡ info+ o

⌊ ι {-<-}{i} {->-}j        ⌋₀ = ι (_ , j)
⌊ κ A        ⌋₀ = κ A
⌊ σ A B      ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B (subst (λ x → x) (info↑ A) a) ⌋₀
⌊ π A B      ⌋₀ = π A λ a → ⌊ B a ⌋₀
⌊ add A B    ⌋₀ = σ A λ a → ⌊ B a ⌋₀
⌊ del _      ⌋₀ = κ ⊤
⌊ add-κ A B  ⌋₀ = σ (κ A) λ a → ⌊ B (lower a) ⌋₀
⌊ del-κ _    ⌋₀ = κ ⊤

info↑ (ι j)        = refl
info↑ (κ A)        = refl
info↑ (σ A B)      = cong₂ Σ (info↑ A) (subst-≡ (info↑ A) (funext (λ a → info↑ (B a))))
info↑ (π A B)      = cong (λ f → (a : A) → f a) (funext (λ a → info↑ (B a)))
info↑ (add A B)    = cong (Σ (info A)) (funext (λ a → info↑ (B a)))
info↑ (del _)      = refl
info↑ (add-κ A B)  = cong (Σ (Lift A)) (funext (λ a → info↑ (B (lower a))))
info↑ (del-κ _)    = refl
\end{code}
%</p-interp>


%<*interp>
\begin{code}
⌊_⌋ : {-<-}∀ {X Y P Q} {γ : IIR X Y} {->-}(o : orn P Q γ) → IIR (pow⁻¹ P) (pow⁻¹ Q)
node  ⌊ o ⌋ j    = ⌊ node o j ⌋₀
emit  ⌊ o ⌋ j x  = emit o j (subst (λ x → x) (info↑ (node o j)) x)
\end{code}
%</interp>

%<*erase>
\begin{code}

\end{code}
%</erase>

%<*algorn>
\begin{code}
algorn₀ : ∀ {X} {γ : poly X} → orn₀ ? γ
algorn₀ {γ = ι i} = {!   !}
algorn₀ {γ = κ A} = {!   !}
algorn₀ {γ = σ A B} = {!   !}
algorn₀ {γ = π A B} = {!   !}

algorn-p : ∀ {X} {α : IIR X X} (φ : alg α) → pow X
π₀ (algorn-p φ) i = Code (obj φ i)
π₁ (algorn-p φ) (i , i′) x = Lift ⊤

algorn : ∀ {X} {α : IIR X X} (φ : alg α) → orn (algorn-p φ) (algorn-p φ) α
node (algorn {α = α} φ) j with node α (π₀ j)
node (algorn {α = α} φ) j | ι i = {!   !}
node (algorn {α = α} φ) j | κ A = κ A
node (algorn {α = α} φ) j | σ A B = {!   !}
node (algorn {α = α} φ) j | π A B = {!   !}
emit (algorn {α = α} φ) (i , i′) x = emit α i (info↓ ? x) , lift *
\end{code}
%</algorn>


%<*forget>
\begin{code}
forget : {-<-}∀ {X} {γ : IIR X X} {P} {->-}(o : orn P P γ) → μ {!(node ⌊ o ⌋) , ? !} ⇒ (μ γ ∘ π₀)
forget o = {!fold!}
\end{code}
%</forget>



\begin{code}
module catholic where
\end{code}

%<*catholic>
\begin{code}
  data inv {-<-}{α β} {A : Set α} {B : Set β} {->-}(f : A → B) : B → Set α where
    ok : (x : A) → inv f (f x)

  to-pow : {-<-}∀ {X Y} → {->-}(E : Code Y → Code X) → (e : (y : Code Y) → decode Y y →
    decode X (E y)) → pow X
  π₀ (to-pow E e) x             = inv E x
  π₁ (to-pow E e) (x , ok y) a  = inv (e y) a
\end{code}
%</catholic>
