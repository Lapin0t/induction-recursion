%include agda.fmt
%include ornaments.fmt

\begin{code}
{-# OPTIONS --experimental-irrelevance --allow-unsolved-metas #-}
module ornaments.orn where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π; el; α₀; α₁; β₀; β₁; γ₀; γ₁)
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
data orn₀ {-<-}{α₀ α₁ β₀ β₁ γ₀ : Level}{X : ISet α₀ β₀}{->-}(γ₁ : Level)(R : PRef α₁ β₁ X) : poly γ₀ X → Set {-<-}(α₀ ⊔ β₀ ⊔ β₁ ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁)){->-}
⌊_⌋₀  : {-<-}{R : PRef α₁ β₁ X}{ρ : poly γ₀ X}{->-}(o : orn₀ γ₁ R ρ) → poly (γ₀ ⊔ γ₁) (PFam R)
info↓ : {-<-}{R : PRef α₁ β₁ X}{ρ : poly γ₀ X}{o : orn₀ γ₁ R ρ} →{->-}info ⌊ o ⌋₀ → info ρ
\end{code}
%</code-def>

%<*code-impl>
\begin{code}
data orn₀ {-<-}{α₀}{α₁}{β₀}{β₁}{γ₀}{X}{->-}γ₁ R where
  ι      : (j : Code R)                                       → orn₀ γ₁ R (ι (down R j))
  κ      : {A : Set γ₀}                                       → orn₀ γ₁ R (κ A)
  σ      : {-<-}∀{U V}{->-}(A : orn₀ γ₁ R U)
           (B : (a : info ⌊ A ⌋₀) → orn₀ γ₁ R (V (info↓ a)))
                           → orn₀ γ₁ R (σ U V)
  π      : {-<-}∀{A V}{->-}(B : (a : A) → orn₀ γ₁ R (V a))→ orn₀ γ₁ R (π A V)

  add₀   : (A : poly (γ₀ ⊔ γ₁) (PFam R)){-<-}{U : _}{->-}
           (B : info A → orn₀ γ₁ R U)                         → orn₀ γ₁ R U
  add₁   : {-<-}∀{U}{->-}(A : orn₀ γ₁ R U)
           (B : info ⌊ A ⌋₀ → poly (γ₀ ⊔ γ₁) (PFam R))        → orn₀ γ₁ R U
  del-κ  : {-<-}∀{A}{->-}(a : A)                              → orn₀ γ₁ R (κ A)
\end{code}
%</code-impl>

%<*p-interp>
\begin{code}
⌊ ι j        ⌋₀ = ι j
⌊_⌋₀ {-<-}{γ₁ = γ₁}{->-} (κ {A}) = κ (Lift γ₁ A)
⌊ σ A B      ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B a ⌋₀
⌊_⌋₀ {-<-}{γ₁ = γ₁}{->-} (π {A} B) = π (Lift γ₁ A) λ { (lift a) → ⌊ B a ⌋₀ }
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
record orn {-<-}{α₀ α₁ β₀ β₁ γ₀}{X Y : ISet α₀ β₀}{->-}(γ₁ : Level)(R : PRef α₁ β₁ X)(S : PRef α₁ β₁ Y)(ρ : IIR γ₀ X Y) : Set {-<-}(α₀ ⊔ β₀ ⊔ β₁ ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁)){->-} where
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
⌊_⌋ : {-<-}{X Y : ISet α₀ β₀}{R : PRef α₁ β₁ X}{S : PRef α₁ β₁ Y}{ρ : IIR γ₀ X Y}{->-}(o : orn γ₁ R S ρ) → IIR (γ₀ ⊔ γ₁) (PFam R) (PFam S)
node ⌊ o ⌋ j = ⌊ node o j ⌋₀
emit ⌊ o ⌋ j = λ x → _ , emit o j x
\end{code}
%</interp>

%<*foldout>
\begin{code}
POut : {-<-}{X : ISet α₀ β₀}{->-}(f : (i : Code X) → decode X i → Set β₁) → PRef α₀ β₁ X
Code (POut f) = _
down (POut f) = λ x → x
decode (POut f) = f

PFold : {X : ISet α₀ β₀}(F : 𝔽 β₁ X) → PRef α₀ (β₀ ⊔ β₁) X
PFold F = POut λ i x → Σ (Code (F i)) λ c → decode (F i) c ≡ x

lem : ∀ {α₀ β₀ β₁ γ₀ γ₁}{X : ISet α₀ β₀}{F : 𝔽 β₁ X}{ρ : poly γ₀ X}(o : orn₀ γ₁ (PFold F) ρ) → (info ⌊ o ⌋₀ , info↓) ⟶̃ ⟦ ρ ⟧₀ F
lem (ι j)      (lift (_ , (c , p))) = lift c , cong lift p
lem κ          x                    = _ , refl
lem (σ {V = V} A B)    (a , b)      =
  let a' , p = lem A a in
  let b' , q = lem (B _) b in
  (a' , subst (λ x → Code (⟦ V x ⟧₀ _)) (sym p) b') ,
  cong-Σ p (trans (cong₂ (λ x → decode (⟦ V x ⟧₀ _)) p (subst-elim _ $ sym p)) q)
lem (π B)      x                    = π→ (λ a → lem (B a)) (x ∘ lift)
lem (add₀ A B) (a , x)              = lem (B a) x
lem (add₁ A B) (x , _)              = lem A x
lem (del-κ a)  x                    = _ , refl

o-fold₀ : ∀ {α₀ β₀ β₁ γ₀}{X : ISet α₀ β₀}(F : 𝔽 β₁ X)(ρ : poly γ₀ X) → orn₀ γ₀ (PFold F) ρ
o-fold₀ F (ι i) = ι i
o-fold₀ F (κ A) = κ
o-fold₀ F (σ A B) = σ (o-fold₀ F A) (o-fold₀ F ∘ B ∘ info↓)
o-fold₀ F (π A B) = π (o-fold₀ F ∘ B)

o-fold : ∀ {α₀ β₀ β₁ γ₀}{X : ISet α₀ β₀}(ρ : IIR γ₀ X X)(φ : alg β₁ ρ) → orn γ₀ (PFold (obj φ)) (PFold (obj φ)) ρ
node (o-fold ρ φ) i = o-fold₀ (obj φ) (node ρ i)
emit (o-fold ρ φ) i x =
  let a , p = lem (o-fold₀ (obj φ) (node ρ i)) x in
  let b , q = mor φ i a in
  b , trans q (cong (emit ρ i) p)

\end{code}
%</foldout>

%<*algR>
\begin{code}
AlgR : {-<-}{X : ISet α₀ β₀}{->-}(F : 𝔽 α₁ X) → PRef (α₀ ⊔ α₁) β₀ X
Code (AlgR {-<-}{X = X}{->-}F) = Σ (Code X) λ i → Code (F i)
down (AlgR F) (i , _) = i
decode (AlgR F) (i , c) x = decode (F i) c ≡ x
\end{code}
%</algR>

%<*algorn0>
\begin{code}
algorn₀ : {-<-}∀ {α₀ α₁ β₀ γ₀} {X : ISet α₀ β₀}{->-}(ρ : poly γ₀ X) (F : 𝔽 α₁ X) (x : Code (⟦ ρ ⟧₀ F)) →
  Σ (orn₀ (γ₀ ⊔ α₁) (AlgR F) ρ) λ o → (y : info ⌊ o ⌋₀) → decode (⟦ ρ ⟧₀ F) x ≡ info↓ y
algorn₀ (ι i) F (lift x) = ι (i , x) , λ { (lift (a , b)) → cong lift b }
algorn₀ (κ A) F (lift x) = del-κ x , λ _ → refl
algorn₀ (σ A B) F (a , b) =
  let (oa , p) = algorn₀ A F a in
  let aux x = algorn₀ (B _) F (subst (λ x → Code (⟦ B x ⟧₀ F)) (p x) b) in
  (σ oa (π₀ ∘ aux)) ,
  λ { (x , y) → cong-Σ (p x) (trans  (cong₂  (λ x₁ → decode (⟦ B x₁ ⟧₀ F)) (p x)
                                             (sym $ subst-elim _ _))
                                     (π₁ (aux x) y)) }
algorn₀ (π A B) F x =
  let aux a = algorn₀ (B a) F (x a) in
  π (π₀ ∘ aux) , (λ f → funext λ a → π₁ (aux a) (f $ lift a))
\end{code}
%</algorn0>

%<*algorn>
\begin{code}
algorn : {-<-}∀ {α₀ α₁ β₀ γ₀}{X : ISet α₀ β₀}{->-}(ρ : IIR γ₀ X X)(φ : alg α₁ ρ) → orn (γ₀ ⊔ α₁) (AlgR (obj φ)) (AlgR (obj φ)) ρ
node (algorn ρ φ) (i , c) =
  add₀  (κ ((π₀ ∘ mor φ i) ⁻¹ c))
        λ { (lift (ok x)) → π₀ $ algorn₀ (node ρ i) (obj φ) x }
emit (algorn ρ φ) (i , c) (lift (ok x) , y) =
  trans  (π₁ $ mor φ i x)
         (cong (emit ρ i) $ π₁ (algorn₀ (node ρ i) (obj φ) x) y)
\end{code}
%</algorn>

%<*algorn-inj>
%{
%format P = "\DATA{P}"
%format aux = "\FCT{aux}"
%format rec = "\FCT{rec}"
\begin{code}
algorn-inj : {-<-}∀ {α₀ α₁ β₀ γ₀}{X : ISet α₀ β₀}{ρ : IIR γ₀ X X}{φ : alg α₁ ρ} ..{s : Size}{->-}(i : Code X) (x : μ-c ρ {s} i) → μ-c ⌊ algorn ρ φ ⌋ {-<-}{s}{->-}(i , π₀ $ fold φ i x)
algorn-inj {-<-}{γ₀ = γ₀} {X = X} {ρ = ρ} {φ}{->-} = induction ρ P rec
  where
    P : {-<-}..{s : Size}{->-}(i : Code X) (x : μ-c ρ {s} i) → Set _
    P {-<-}{s}{->-}i x = μ-c ⌊ algorn ρ φ ⌋ {-<-}{s}{->-}(i , π₀ $ fold φ i x)

    aux : {-<-}..{s : Size} ..{t : Size< s}{->-}(ρ₀ : poly γ₀ X) (x : Code (⟦ ρ₀ ⟧₀ (μ ρ{-<-}{t}{->-}))) (p : all ρ₀ P x) →
          Σ (Code (⟦ ⌊ π₀ $ algorn₀ ρ₀ (obj φ) (π₀ $ ⟦ ρ₀ ⟧[ fold φ ]₀ x) ⌋₀ ⟧₀ (μ ⌊ algorn ρ φ ⌋{-<-}{t}{->-})))
            λ y →  decode (⟦ ρ₀ ⟧₀ (μ ρ{-<-}{t}{->-})) x
                   ≡ info↓ (decode (  ⟦ ⌊ π₀ $ algorn₀ ρ₀ (obj φ) (π₀ $ ⟦ ρ₀ ⟧[ fold φ ]₀ x) ⌋₀ ⟧₀
                                      (μ ⌊ algorn ρ φ ⌋{-<-}{t}{->-})) y)

    aux (ι i) (lift x) (lift p) = lift p , cong lift ?
    aux (κ A) x p = lift * , refl
    aux (σ A B) (x , y) (p , q) = ?
    aux (π A B) x p =
      let aux a = aux (B a) (x a) (p a) in
      π₀ ∘ aux ∘ lower , funext (π₁ ∘ aux)

    rec : {-<-}..{s : Size} ..{t : Size< s}{->-}(i : Code X) (x : Code (⟦ ρ ⟧ (μ ρ{-<-}{t}{->-}) i)) → all (node ρ i) P x → P i (⟨_⟩ {-<-}{s = s}{->-}x)
    rec i x p =
      let c = ⟦ ρ ⟧[ fold φ ] i x in
      ⟨ lift (ok $ π₀ c) , π₀ $ aux (node ρ i) x p ⟩

\end{code}
%}
%</algorn-inj>

%<*erase>
\begin{code}

{-erase₀ : {-<-}{X : ISet α₀ β₀}{ρ : poly γ₀ X}{R : PRef α₁ β₁ X}{->-}(o : orn₀ γ₁ R ρ)
         (F : 𝔽 γ₀ X) (G : (j : Code $ PFam R) → (x : Code (F $ down R j)) → Fam (γ₀ ⊔ γ₁) (decode R j (decode (F $ down R j) x))) → info↓ {o = o} << ⟦ ⌊ o ⌋₀ ⟧₀ (foo {γ₁ = γ₁} F G) ⟶̃ ⟦ ρ ⟧₀ F
erase₀ (ι j) F G _ = _ , refl
erase₀ κ F G _ = _ , refl
erase₀ (σ A B) F G i = σ→ _ _ (erase₀ A F G) (λ a → erase₀ (B (decode (⟦ ⌊ A ⌋₀ ⟧₀ (foo F G)) a)) F G) i
erase₀ (π B) F G f = π→ (λ a → erase₀ (B a) F G) (f ∘ lift)
erase₀ (add₀ A B) F G (a , b) = erase₀ (B _) F G b
erase₀ (add₁ A B) F G (a , b) = erase₀ A F G a
erase₀ (del-κ a) F G i = _ , refl

erase : {-<-}{X : ISet α₀ β₀}{R : PRef α₁ β₁ X}{ρ : IIR γ₀ X X}{->-}(o : orn γ₁ R R ρ)
        (F : 𝔽 γ₀ X) ..{s : Size} → π₀< ⟦ ⌊ o ⌋ ⟧ (μ ⌊ o ⌋ {s} & (F ∘ down R)) ⇒ (⟦ ρ ⟧ F ∘ down R)
erase {R = R} {ρ} o F i = emit ρ (down R i) <<$> {!   !}
--emit ρ (down S j) <<$> erase₀ (node o j) F G-}


{-erase₀ (ι i) F G (lift (x , y)) = _ , refl
erase₀ κ F G (lift x) = _ , refl
erase₀ (σ {V = V} A B) F G (a , b) =
  let (a' , p) = erase₀ A F G a in
  let (b' , q) = erase₀ (B _) F G b in
  (a' , subst (λ x → Code (⟦ V x ⟧₀ _)) (sym p) b') ,
  (cong-Σ p (trans  (cong₂ (λ x → decode (⟦ V x ⟧₀ _)) p (subst-elim _ $ sym p)) q))
erase₀ (π B) F G x = π→ (λ a → erase₀ (B a) F G) (x ∘ lift)
erase₀ (add₀ A B) F G (a , x) = erase₀ (B _) F G x
erase₀ (add₁ A B) F G (a , _) = erase₀ A F G a
erase₀ (del-κ a) F G x = _ , refl

erase : {-<-}{X Y : ISet α₀ β₀}{R : PRef α₁ β₁ X}{S : PRef α₁ β₁ Y}{ρ : IIR γ₀ X Y}{->-}(o : orn γ₁ R S ρ)
        (F : 𝔽 γ₀ X)(G : PObj γ₁ R F) → π₀< ⟦ ⌊ o ⌋ ⟧ (pfam G) ⇒ (⟦ ρ ⟧ F ∘ down S)
erase {S = S} {ρ} o F G j = emit ρ (down S j) <<$> erase₀ (node o j) F G-}

--Bla : ∀ {α₀ α₁ β₀ β₁ γ₀ γ₁}{X : ISet α₀ β₀}{R : PRef α₁ β₁ X}{ρ : IIR γ₀ X X}(o : orn γ₁ R R ρ)(F : 𝔽 γ₀ X) → PObj γ₁ R F
--Code (addon (Bla o F) j x) = μ-c ⌊ o ⌋ j
--decode (addon (Bla o F) j x) y = {! π₁ $ μ-d ⌊ o ⌋ j y !}

{-forget : {-<-}∀ {α₀ β₀ α₁ β₁ γ₀ γ₁}{X : ISet α₀ β₀}{R : PRef α₁ β₁ X}{ρ : IIR γ₀ X X}{->-}(o : orn γ₁ R R ρ){s} → π₀< (μ ⌊ o ⌋ {s}) ⇒ (μ ρ {s} ∘ down R)
forget {X = X} {R = R} {ρ = ρ} o {s = s} = para {!   !} φ
  where
    φ : ..{t : Size} → p-alg _ (decode X ∘ down R) ⌊ o ⌋
    obj (φ {t}) = μ ρ {t} ∘ down R
    down φ _ = π₀
    mor φ i x =
      let y , p = erase o (μ ρ) {!   !} i ?
      in {!   !} , trans p ?-}

\end{code}
%</erase>
