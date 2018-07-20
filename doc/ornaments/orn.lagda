%include agda.fmt
%include ornaments.fmt

\begin{code}
{-# OPTIONS --experimental-irrelevance #-}
module ornaments.orn where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π; el)
open import ornaments.pow hiding (α₀; α₁; β₀; β₁)
open import ornaments.iir hiding (α; β; γ; δ; X; Y)
open import ornaments.induction hiding (α; β; γ; δ; X; s)

variable
  {α₀ α₁} : Level  -- old/new index lvl
  {β₀ β₁} : Level  -- output lvl
  {γ₀ γ₁} : Level  -- old/new code lvl (actually new is `γ₀ ⊔ γ₁`)
  {δ} : Level
  {X Y} : ISet α₀ β₀
  {R} : PRef α₁ β₁ X
  {S} : PRef α₁ β₁ Y
\end{code}


%<*code-def>
\begin{code}
data orn₀ {-<-}{α₀ α₁ β₀ β₁ γ₀ : Level}{X : ISet α₀ β₀}{->-}(γ₁ : Level)(R : PRef α₁ β₁ X) : poly γ₀ X → Set (α₀ ⊔ β₀ ⊔ β₁ ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁))
⌊_⌋₀  : {-<-}{R : PRef α₁ β₁ X}{ρ : poly γ₀ X}{->-}(o : orn₀ γ₁ R ρ) → poly (γ₀ ⊔ γ₁) (PFam R)
info↓ : {-<-}{R : PRef α₁ β₁ X}{ρ : poly γ₀ X}{o : orn₀ γ₁ R ρ}{->-} → info ⌊ o ⌋₀ → info ρ
\end{code}
%</code-def>

%<*code-impl>
\begin{code}
data orn₀ {-<-}{α₀}{α₁}{β₀}{β₁}{γ₀}{X}{->-}γ₁ R where
  ι      : (j : Code R)                                                                         → orn₀ γ₁ R (ι (down R j))
  κ      : {A : Set γ₀}                                                                         → orn₀ γ₁ R (κ A)
  σ      : {-<-}∀ {U V}{->-}(A : orn₀ γ₁ R U)(B : (a : info ⌊ A ⌋₀) → orn₀ γ₁ R (V (info↓ a)))  → orn₀ γ₁ R (σ U V)
  π      : {-<-}∀ {A V}{->-}(B : (a : A) → orn₀ γ₁ R (V a))                                     → orn₀ γ₁ R (π A V)

  add₀   : (A : poly (γ₀ ⊔ γ₁) (PFam R)){-<-}{U : _}{->-}(B : info A → orn₀ γ₁ R U)             → orn₀ γ₁ R U
  add₁   : {-<-}∀ {U}{->-}(A : orn₀ γ₁ R U)(B : info ⌊ A ⌋₀ → poly (γ₀ ⊔ γ₁) (PFam R))          → orn₀ γ₁ R U
  del-κ  : {-<-}∀ {A}{->-}(a : A)                                                               → orn₀ γ₁ R (κ A)
\end{code}
%</code-impl>

%<*p-interp>
\begin{code}
⌊ ι j        ⌋₀ = ι j
⌊_⌋₀ {γ₁ = γ₁} (κ {A}) = κ (Lift γ₁ A)
⌊ σ A B      ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B a ⌋₀
⌊_⌋₀ {γ₁ = γ₁} (π {A} B) = π (Lift γ₁ A) λ { (lift a) → ⌊ B a ⌋₀ }
⌊ add₀ A B   ⌋₀ = σ A λ a → ⌊ B a ⌋₀
⌊ add₁ A B   ⌋₀ = σ ⌊ A ⌋₀ B
⌊ del-κ _    ⌋₀ = κ ⊤
\end{code}
%</p-interp>

%<*infodown-impl>
\begin{code}
info↓ {o = ι i}        (lift (x , _))  = lift x
info↓ {o = κ}          (lift a)        = lift $ lower a
info↓ {o = σ A B}      (a , b)         = info↓ a , info↓ b
info↓ {o = π B}        f               = λ a → info↓ (f $ lift a)
info↓ {o = add₀ A B}   (a , b)         = info↓ b
info↓ {o = add₁ A B}   (a , _)         = info↓ a
info↓ {o = del-κ a}    _               = lift a
\end{code}
%</infodown-impl>



%<*orn>
\begin{code}
record orn {α₀ α₁ β₀ β₁ γ₀}{X Y : ISet α₀ β₀}(γ₁ : Level)(R : PRef α₁ β₁ X)(S : PRef α₁ β₁ Y)(ρ : IIR γ₀ X Y) : Set (α₀ ⊔ β₀ ⊔ β₁ ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁)) where
  field
    node :  (j : Code S) → orn₀ γ₁ R (node ρ (down S j))
    emit :  (j : Code S) → (x : info ⌊ node j ⌋₀) → decode S j (emit ρ (down S j) (info↓ x))
\end{code}
%</orn>

\begin{code}
open orn public
\end{code}


%<*interp>
\begin{code}
⌊_⌋ : {X Y : ISet α₀ β₀}{R : PRef α₁ β₁ X}{S : PRef α₁ β₁ Y}{ρ : IIR γ₀ X Y}(o : orn γ₁ R S ρ) → IIR (γ₀ ⊔ γ₁) (PFam R) (PFam S)
node ⌊ o ⌋ j = ⌊ node o j ⌋₀
emit ⌊ o ⌋ j = λ x → _ , emit o j x
\end{code}
%</interp>

%<*erase>
\begin{code}
{-erase₀ : {-<-}{X : ISet α₀ β}{ρ : poly γ₀ X}{R : Set α₁}{f : R → Code X}{->-}(o : orn₀ γ₁ f ρ) (F : 𝔽 γ₀ X) → info↓ o >> ⟦ ⌊ o ⌋₀ ⟧ᵢ (F ∘ f) ⟶̃ ⟦ ρ ⟧ᵢ F
erase₀ {f = f} (ι j) F (lift x) = lift x , refl
erase₀ (κ A) F (lift x) = lift $ lower x , refl
erase₀ (σ {V = V} A B) F (a , b) =
  let (a' , eqa) = erase₀ A F a in
  let (b' , eqb) = erase₀ (B _) F b in
  (a' , subst (λ x → Code (⟦ V x ⟧ᵢ _)) (sym eqa) b') ,
  (cong-Σ eqa (trans  (cong₂ (λ x → decode (⟦ V x ⟧ᵢ _)) eqa (subst-elim _ $ sym eqa))  eqb))
erase₀ (π A B) F x =
  let aux a = erase₀ (B a) F (x $ lift a) in
  π₀ ∘ aux , funext (π₁ ∘ aux)
erase₀ (add₀ A B) F (a , x) = erase₀ (B $ decode (⟦ A ⟧ᵢ _) a) F x
erase₀ (add₁ A B) F (x , _) = erase₀ A F x
erase₀ (add-κ A B) F (lift a , x) = erase₀ (B a) F x
erase₀ (del-κ a) F _ = lift a , refl

erase : {-<-}{X Y : ISet α₀ β}{R S : Set α₁}{f : R → Code X}{g : S → Code Y}{ρ : IIR γ₀ X Y}{->-}(o : orn γ₁ f g ρ) (F : 𝔽 γ₀ X) → ⟦ ⌊ o ⌋ ⟧ (F ∘ f) ⇒ (⟦ ρ ⟧ F ∘ g)
erase {g = g}{ρ} o F j = emit ρ (g j) <$>> erase₀ (node o j) F-}
\end{code}
%</erase>

%<*ornalg>
\begin{code}
--ornalg : {X : ISet α₀ β}{R : Set α₁}{f : R → Code X}{ρ : IIR γ₀ X X}(o : orn γ₁ f f ρ) ..{s : Size} ..{t : Size< s} → (⟦ ⌊ o ⌋ ⟧ (μ ρ {t} ∘ f)) ⇒ (μ ρ {s} ∘ f)
--ornalg o i x = ⟨ π₀ $ erase o _ i x ⟩ , π₁ $ erase o _ i x
\end{code}
%</ornalg>

%<*forget>
\begin{code}
--forget : {-<-}{X : ISet α₀ β}{R : Set α₁}{f : R → Code X}{ρ : IIR γ₀ X X}{->-}(o : orn γ₁ f f ρ){-<-}{->-} → μ ⌊ o ⌋ {∞} ⇒ (μ ρ {∞} ∘ f)
--forget {f = f}{ρ = ρ} o = fold (μ ρ ∘ f , ornalg o)

\end{code}
%</forget>

%<*foldout>
\begin{code}
POut : {X : ISet α₀ β₀}(f : (i : Code X) → decode X i → Set β₁) → PRef α₀ β₁ X
Code (POut f) = _
down (POut f) = λ x → x
decode (POut f) = f

PFold : {X : ISet α₀ β₀}(F : 𝔽 β₁ X) → PRef α₀ (β₀ ⊔ β₁) X
PFold F = POut λ i x → Σ (Code (F i)) λ c → decode (F i) c ≡ x

lem : ∀ {α₀ β₀ β₁ γ₀ γ₁}{X : ISet α₀ β₀}{F : 𝔽 β₁ X}{ρ : poly γ₀ X}(o : orn₀ γ₁ (PFold F) ρ) → (info ⌊ o ⌋₀ , info↓) ⟶̃ ⟦ ρ ⟧ᵢ F
lem (ι j)      (lift (_ , (c , p))) = lift c , cong lift p
lem κ          x                    = _ , refl
lem (σ {V = V} A B)    (a , b)      =
  let a' , p = lem A a in
  let b' , q = lem (B _) b in
  (a' , subst (λ x → Code (⟦ V x ⟧ᵢ _)) (sym p) b') ,
  cong-Σ p (trans (cong₂ (λ x → decode (⟦ V x ⟧ᵢ _)) p (subst-elim _ $ sym p)) q)
lem (π B)      x                    = π→ (λ a → lem (B a)) (x ∘ lift)
lem (add₀ A B) (a , x)              = lem (B a) x
lem (add₁ A B) (x , _)              = lem A x
lem (del-κ a)  x                    = _ , refl

o-fold₀ : ∀ {α₀ β₀ β₁ γ₀}{X : ISet α₀ β₀}(F : 𝔽 β₁ X)(ρ : poly γ₀ X) → orn₀ γ₀ (PFold F) ρ
o-fold₀ F (ι i) = ι i
o-fold₀ F (κ A) = κ
o-fold₀ F (σ A B) = σ (o-fold₀ F _) (o-fold₀ F ∘ _)
o-fold₀ F (π A B) = π (o-fold₀ F ∘ _)

o-fold : ∀ {α₀ β₀ β₁ γ₀}{X : ISet α₀ β₀}(ρ : IIR γ₀ X X)(φ : alg β₁ ρ) → orn γ₀ (PFold (obj φ)) (PFold (obj φ)) ρ
node (o-fold ρ φ) i = o-fold₀ (obj φ) (node ρ i)
emit (o-fold ρ φ) i x =
  let a , p = lem (o-fold₀ (obj φ) (node ρ i)) x in
  let b , q = mor φ i a in
  b , (trans q (cong (emit ρ i) p))

\end{code}
%</foldout>

%<*algorn>
\begin{code}
--algorn₀ : ∀ {α₀ β γ₀ δ} {X : ISet α₀ β} (ρ : poly γ₀ X) (F : 𝔽 δ X) → orn₀ δ {R = Σ (Code X) (λ i → Code (F i))} π₀ ρ
--algorn₀ {γ₀ = γ₀} (ι i) F = add₀ (κ (Lift γ₀ (Code (F i)))) (λ { (lift j) → ι (i , lower j) })
--algorn₀ (κ A) F = κ A
--algorn₀ (σ A B) F = σ (algorn₀ A F) (λ a → algorn₀ (B $ info↓ _ a) F)
--algorn₀ (π A B) F = π A (λ a → algorn₀ (B a) F) --π A (λ a → algorn₀ (B a) ((Code G) , (λ x → decode G x a)) λ x → (π₀ $ f {! λ a →   !}) , {!   !}) --π A (λ a → algorn₀ (B a) f)

--algorn : ∀ {α β γ δ} {X : ISet α β} (ρ : IIR γ X X) (φ : alg δ ρ) → orn δ {R = Σ (Code X) (λ i → Code (obj φ i))} {S = Σ (Code X) (λ i → Code (obj φ i))} π₀ π₀ ρ
--node (algorn {α} {β} {γ} {δ} {X} ρ φ) (i , j) = add₁ (algorn₀ (node ρ i) (obj φ)) λ x → κ {! mor φ i  !}
--emit (algorn {α} {β} {γ} {δ} {X} ρ φ) = {!   !}

{-algorn₀ : {X : ISet α₀ β} (ρ : poly γ₀ X) (F : 𝔽 γ₁ X) → orn₀ γ₁ (Ref F) ρ
algorn₀ {γ₀ = γ₀} (ι i) F = add₀ (κ (Lift γ₀ $ Code (F i))) λ { (lift x) → ι (i , lower x) }
algorn₀ (κ A) F = κ A
algorn₀ (σ A B) F = σ (algorn₀ A F) (λ a → algorn₀ (B $ info↓ _ a) F)
algorn₀ (π A B) F = π A (λ a → algorn₀ (B a) F)

foo : ∀ {α₀ β γ₀ γ₁} {X : ISet α₀ β} (ρ : poly γ₀ X) (F : 𝔽 γ₁ X) (P : PObj γ₀ γ₁ (Ref F)) (xs : Code (⟦ ρ ⟧ᵢ (ifam P))) → all ρ ? xs → Code (⟦ ⌊ algorn₀ ρ F ⌋₀ ⟧ᵢ (pfam P))
foo (ι i) F P x p = {!   !}
foo (κ A) F P x p = lift x
foo (σ A B) F P x p = ? --foo A F P (π₀ x) (π₀ p) , {! foo (B _) F P (π₁ x) (π₁ p)  !}
foo (π A B) F P x p = λ { (lift a) → foo (B a) F P (x a) (p a) }-}

--lem : ∀ {α₀ β γ₀}{X : ISet α₀ β} (ρ : IIR γ₀ X X) (φ : alg ρ) (i : _) → info ⌊ algorn₀ (node ρ i) (obj φ) ⌋₀ → Code (obj φ i)
--lem ρ φ i x = {!   !}

--algorn : {X : ISet α₀ β} (ρ : IIR γ₀ X X) (φ : alg ρ) → orn γ₀ (Ref (obj φ)) (Ref (obj φ)) ρ
--node (algorn ρ φ) (i , j) = add₁ (algorn₀ (node ρ i) (obj φ)) λ x → κ ({!   !})
--emit (algorn ρ φ) (i , j) (x , lift p) = {!   !}

--remember : ∀ {α₀ β γ₀ s} {X : ISet α₀ β} (ρ : IIR γ₀ X X) (φ : alg ρ) {i : Code X} (x : μ-c ρ {s} i) → μ-c ⌊ algorn ρ φ ⌋ {s} (i , π₀ $ fold φ i x)
--remember ρ φ = induction ρ (λ {s} {i} x → μ-c ⌊ algorn ρ φ ⌋ {s} (i , π₀ $ fold φ i x)) aux
--  where
--    aux : ∀ {s t i} → (xs : Code (⟦ node ρ i ⟧ᵢ (μ ρ {t}))) → all (node ρ i) _ xs → μ-c ⌊ algorn ρ φ ⌋ {s} (i , _)
--    aux xs x = {!   !}

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
