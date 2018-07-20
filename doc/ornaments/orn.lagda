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
erase₀ : {-<-}{X : ISet α₀ β₀}{ρ : poly γ₀ X}{R : PRef α₁ β₁ X}{->-}(o : orn₀ γ₁ R ρ)
         {F : 𝔽 γ₀ X} {G : 𝔽 (γ₀ ⊔ γ₁) (PFam R)} (m : π₀> G ⇒ (F ∘ down R)) →
         info↓ {o = o} >> ⟦ ⌊ o ⌋₀ ⟧ᵢ G ⟶̃ ⟦ ρ ⟧ᵢ F
erase₀ (ι i) m (lift x) = _ , cong lift $ π₁ $ m i x
erase₀ κ m (lift x) = _ , refl
erase₀ (σ {V = V} A B) m (a , b) =
  let (a' , p) = erase₀ A m a in
  let (b' , q) = erase₀ (B _) m b in
  (a' , subst (λ x → Code (⟦ V x ⟧ᵢ _)) (sym p) b') ,
  (cong-Σ p (trans  (cong₂ (λ x → decode (⟦ V x ⟧ᵢ _)) p (subst-elim _ $ sym p)) q))
erase₀ (π B) m x = π→ (λ a → erase₀ (B a) m) (x ∘ lift)
erase₀ (add₀ A B) m (a , x) = erase₀ (B _) m x
erase₀ (add₁ A B) m (a , _) = erase₀ A m a
erase₀ (del-κ a) m x = _ , refl

erase : {-<-}{X Y : ISet α₀ β₀}{R : PRef α₁ β₁ X}{S : PRef α₁ β₁ Y}{ρ : IIR γ₀ X Y}{->-}(o : orn γ₁ R S ρ)
        {-<-}{F : 𝔽 γ₀ X}{G : 𝔽 (γ₀ ⊔ γ₁) (PFam R)}{->-}(m : π₀> G ⇒ (F ∘ down R)) → π₀> ⟦ ⌊ o ⌋ ⟧ G ⇒ (⟦ ρ ⟧ F ∘ down S)
erase {S = S} {ρ} o m j = emit ρ (down S j) <$>> erase₀ (node o j) m

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
Foo : {X : ISet α₀ β₀}(F : 𝔽 α₁ X) → PRef (α₀ ⊔ α₁) β₀ X
Code (Foo {X = X} F) = Σ (Code X) λ i → Code (F i)
down (Foo F) (i , _) = i
decode (Foo F) (i , c) x = decode (F i) c ≡ x

algorn₀ : ∀ {α₀ α₁ β₀ γ₀} {X : ISet α₀ β₀} (ρ : poly γ₀ X) (F : 𝔽 α₁ X) (x : Code (⟦ ρ ⟧ᵢ F)) → Σ (orn₀ (γ₀ ⊔ α₁) (Foo F) ρ) λ o → (y : info ⌊ o ⌋₀) → decode (⟦ ρ ⟧ᵢ F) x ≡ info↓ y
algorn₀ (ι i) F (lift x) = ι (i , x) , λ { (lift (a , b)) → cong lift b }
algorn₀ (κ A) F (lift x) = del-κ x , λ _ → refl
algorn₀ (σ A B) F (a , b) =
  let (oa , p) = algorn₀ A F a in
  let aux x = algorn₀ (B _) F (subst (λ x → Code (⟦ B x ⟧ᵢ F)) (p x) b) in
  (σ oa (π₀ ∘ aux)) ,
  λ { (x , y) → cong-Σ (p x) (trans (cong₂ (λ x₁ → decode (⟦ B x₁ ⟧ᵢ F)) (p x) (sym $ subst-elim _ _)) (π₁ (aux x) y)) }
algorn₀ (π A B) F x =
  let aux a = algorn₀ (B a) F (x a) in
  π (π₀ ∘ aux) , (λ f → funext λ a → π₁ (aux a) (f $ lift a))

algorn : ∀ {α₀ α₁ β₀ γ₀}{X : ISet α₀ β₀}(ρ : IIR γ₀ X X)(φ : alg α₁ ρ) → orn (γ₀ ⊔ α₁) (Foo (obj φ)) (Foo (obj φ)) ρ
node (algorn ρ φ) (i , c) = add₀ (κ ((π₀ ∘ mor φ i) ⁻¹ c)) λ { (lift (ok x)) → π₀ $ algorn₀ (node ρ i) (obj φ) x }
emit (algorn ρ φ) (i , c) (lift (ok x) , y) = trans (π₁ $ mor φ i x) (cong (emit ρ i) $ π₁ (algorn₀ (node ρ i) (obj φ) x) y)

to-algorn : ∀ {α₀ α₁ β₀ γ₀}{X : ISet α₀ β₀}{ρ : IIR γ₀ X X}{φ : alg α₁ ρ} {s : Size} {i : Code X} → (x : μ-c ρ {s} i) → μ-c ⌊ algorn ρ φ ⌋ {s} (i , π₀ $ fold φ i x)
to-algorn {γ₀ = γ₀} {X = X} {ρ = ρ} {φ} = induction ρ P rec
  where
    P : ..{s : Size} {i : Code X} → (x : μ-c ρ {s} i) → Set _
    P {s} {i} x = μ-c ⌊ algorn ρ φ ⌋ {s} (i , π₀ $ fold φ i x)

    aux : ..{s : Size} ..{t : Size< s} (ρ₀ : poly γ₀ X) (x : Code (⟦ ρ₀ ⟧ᵢ (μ ρ {t}))) (p : all ρ₀ P x) →
          Σ (Code (⟦ ⌊ π₀ $ algorn₀ ρ₀ (obj φ) (π₀ $ ⟦ ρ₀ ⟧[ fold φ ]ᵢ x) ⌋₀ ⟧ᵢ (μ ⌊ algorn ρ φ ⌋ {t})))
            λ y → decode (⟦ ρ₀ ⟧ᵢ (μ ρ {t})) x ≡ info↓ (decode (⟦ ⌊ π₀ $ algorn₀ ρ₀ (obj φ) (π₀ $ ⟦ ρ₀ ⟧[ fold φ ]ᵢ x) ⌋₀ ⟧ᵢ (μ ⌊ algorn ρ φ ⌋ {t})) y)

    aux (ι i) (lift x) (lift p) = lift p , cong lift {!   !}
    aux (κ A) x p = lift * , refl
    aux (σ A B) (x , y) (p , q) = ?
      --let a , p' = aux A x p in
      --let b , q' = aux (B _) y q in
      --(a , ?) ,
      --cong-Σ p' (trans q' {!cong₂ (λ x y → info↓ (decode (⟦ ⌊ π₀ $ algorn₀ (B x) (obj φ) (π₀ $ ⟦ B x ⟧[ fold φ ]ᵢ y) ⌋₀ ⟧ᵢ (μ ⌊ algorn ρ φ ⌋)) y)) ? ? !})
    aux (π A B) x p =
      let aux a = aux (B a) (x a) (p a) in
      π₀ ∘ aux ∘ lower , funext (π₁ ∘ aux)

    rec : ..{s : Size} ..{t : Size< s} {i : Code X} (x : Code (⟦ ρ ⟧ (μ ρ {t}) i)) → all (node ρ i) P x → P (⟨_⟩ {s = s} x)
    rec {i = i} x p =
      let c = ⟦ ρ ⟧[ fold φ ] i x in
      ⟨ lift (ok $ π₀ c) , π₀ $ aux (node ρ i) x p ⟩

\end{code}
%</algorn>
