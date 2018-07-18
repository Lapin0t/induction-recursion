%include agda.fmt
%include ornaments.fmt

\begin{code}
{--# OPTIONS --experimental-irrelevance --show-implicit --show-irrelevant #-}
module ornaments.orn where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π; el)
open import ornaments.pow hiding (α₀; α₁; β₀; β₁)
open import ornaments.iir hiding (α; β; γ; δ; X; Y)
open import ornaments.induction hiding (α; β; γ; δ; X; s)

variable
  {α₀ α₁} : Level  -- old/new index lvl
  {β} : Level  -- output lvl
  {γ₀ γ₁} : Level  -- old/new code lvl (actually new is `γ₀ ⊔ γ₁`)
  {δ} : Level
  {X Y} : ISet α₀ β
  {R} : ISet α₁ β
  --{R S} : PRef α₁ β₁ X
\end{code}


%<*code-def>
\begin{code}
mk : (X : ISet α₀ β) {R : Set α₁} (f : R → Code X) → ISet α₁ β
Code (mk X {R} f) = R
decode (mk X f) j = decode X (f j)

mk₂ : {X : ISet α₀ β} {R : Set α₁} (γ₁ : Level) (f : R → Code X) → 𝔽 γ₀ X → 𝔽 (γ₀ ⊔ γ₁) (mk X f)
Code (mk₂ γ₁ f F j) = Lift γ₁ (Code $ F $ f j)
decode (mk₂ γ₁ f F j) (lift x) = decode (F $ f j) x

data orn₀ {-<-}{α₀ α₁ β γ₀ : _}{X : ISet α₀ β}{->-}(γ₁ : Level) {R : Set α₁} (f : R → Code X) : poly γ₀ X → Set (α₀ ⊔ β ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁))
⌊_⌋₀  : {-<-}{X : ISet α₀ β}{R : Set α₁}{f : R → Code X}{ρ : poly γ₀ X}{->-}(o : orn₀ γ₁ f ρ) → poly (γ₀ ⊔ γ₁) (mk X f)
info↓ : {-<-}{X : ISet α₀ β}{R : Set α₁}{f : R → Code X}{ρ : poly γ₀ X}{->-}(o : orn₀ γ₁ f ρ) → info ⌊ o ⌋₀ → info ρ
\end{code}
%</code-def>

%<*code-impl>
\begin{code}
data orn₀ {-<-}{α₀}{α₁}{β}{γ₀}{X}{->-}γ₁ {R} f where
  ι      : (j : R)                                                                                → orn₀ γ₁ f (ι (f j))
  κ      : (A : Set γ₀)                                                                           → orn₀ γ₁ f (κ A)
  σ      : {-<-}∀ {U V}{->-}(A : orn₀ γ₁ f U) (B : (a : info ⌊ A ⌋₀) → orn₀ γ₁ f (V (info↓ A a))) → orn₀ γ₁ f (σ U V)
  π      : (A : Set γ₀){-<-}{V : _}{->-} (B : (a : A) → orn₀ γ₁ f (V a))                          → orn₀ γ₁ f (π A V)

  add₀   : (A : poly (γ₀ ⊔ γ₁) (mk X f)) {-<-}{U : _}{->-}(B : info A → orn₀ γ₁ f U)              → orn₀ γ₁ f U
  add₁   : {-<-}∀ {U}{->-}(A : orn₀ γ₁ f U) (B : info ⌊ A ⌋₀ → poly (γ₀ ⊔ γ₁) (mk X f))           → orn₀ γ₁ f U
--  del :    {-<-}∀ {A : poly X} → {->-} {!  !} → orn₀ P A
  add-κ  : (A : Set (γ₀ ⊔ γ₁)){-<-}{U : _}{->-} (B : A → orn₀ γ₁ f U)                             → orn₀ γ₁ f U
  del-κ  : {-<-}∀ {A}{->-}(a : A)                                                                 → orn₀ γ₁ f (κ A)
\end{code}
%</code-impl>

%<*p-interp>
\begin{code}
⌊ ι j        ⌋₀ = ι j
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
info↓ {f = f} (ι i)        (lift x) = lift x
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
record orn {-<-}{α₀ α₁ β γ₀}{X Y : ISet α₀ β}{->-}(γ₁ : Level) {R S : Set α₁} (f : R → Code X) (g : S → Code Y) (ρ : IIR γ₀ X Y) : Set (α₀ ⊔ β ⊔ lsuc (α₁ ⊔ γ₀ ⊔ γ₁)) where
  field
    node :  (j : S) → orn₀ γ₁ f (node ρ (g j))
    emit :  (j : S) → (x : info ⌊ node j ⌋₀) → decode Y (g j)
\end{code}
%</orn>

\begin{code}
open orn public
\end{code}


%<*interp>
\begin{code}
⌊_⌋ : {-<-}{X Y : ISet α₀ β}{R S : Set α₁}{f : R → Code X}{g : S → Code Y}{ρ : IIR γ₀ X Y}{->-}(o : orn γ₁ f g ρ) → IIR (γ₀ ⊔ γ₁) (mk X f) (mk Y g)
node ⌊ o ⌋ j = ⌊ node o j ⌋₀
emit (⌊_⌋ {g = g} {ρ = ρ} o) j x = emit ρ (g j) (info↓ (node o j) x)
\end{code}
%</interp>

%<*erase>
\begin{code}
--dwn : {ρ : }

erase₀ : {-<-}{X : ISet α₀ β}{ρ : poly γ₀ X}{R : Set α₁}{f : R → Code X}{->-}(o : orn₀ γ₁ f ρ) (F : 𝔽 γ₀ X) → info↓ o >> ⟦ ⌊ o ⌋₀ ⟧ᵢ (F ∘ f) ⟶̃ ⟦ ρ ⟧ᵢ F
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

erase : {-<-}{X Y : ISet α₀ β}{ρ : IIR γ₀ X Y}{R S : Set α₁}{f : R → Code X}{g : S → Code Y}{->-}(o : orn γ₁ f g ρ) (F : 𝔽 γ₀ X) → ⟦ ⌊ o ⌋ ⟧ (F ∘ f) ⇒ (⟦ ρ ⟧ F ∘ g)
erase {ρ = ρ} {g = g} o F j = emit ρ (g j) <$>> erase₀ (node o j) F
\end{code}
%</erase>

%<*ornalg>
\begin{code}
ornalg : {X : ISet α₀ β}{ρ : IIR γ₀ X X}{R : Set α₁}{f : R → Code X} (o : orn γ₁ f f ρ) ..{s : Size} ..{t : Size< s} → (⟦ ⌊ o ⌋ ⟧ (μ ρ {t} ∘ f)) ⇒ (μ ρ {s} ∘ f)
ornalg o i x = ⟨ π₀ $ erase o _ i x ⟩ , π₁ $ erase o _ i x
\end{code}
%</ornalg>

%<*forget>
\begin{code}
forget : {-<-}{X : ISet α₀ β}{ρ : IIR γ₀ X X}{R : Set α₁}{f : R → Code X}{->-}(o : orn γ₁ f f ρ){-<-}..{s : Size}{->-} → (μ ⌊ o ⌋ {s}) ⇒ (μ ρ {s} ∘ f)
forget o {s} = {!fold (_ , ornalg o {↑ s})!}

\end{code}
%</forget>

%<*algorn>
\begin{code}
--algorn₀ : ∀ {α₀ β γ₀ δ} {X : ISet α₀ β} (ρ : poly γ₀ X) {F : 𝔽 δ X} (G : Set δ) (f : Code (⟦ ρ ⟧ᵢ F) → G) → orn₀ δ {R = Σ (Code X) (λ i → Code (F i))} π₀ ρ
--algorn₀ {γ₀ = γ₀} (ι i) G f = ?
--algorn₀ (κ A) G f = κ A
--algorn₀ (σ A B) G f = ? --σ (algorn₀ A F) (λ a → algorn₀ (B $ info↓ _ a) f)
--algorn₀ (π A B) G f = π A (λ a → algorn₀ (B a) {!   !} λ x → {!   !}) --π A (λ a → algorn₀ (B a) ((Code G) , (λ x → decode G x a)) λ x → (π₀ $ f {! λ a →   !}) , {!   !}) --π A (λ a → algorn₀ (B a) f)

--algorn : ∀ {α β γ δ} {X : ISet α β} (ρ : IIR γ X X) (φ : alg δ ρ) → orn δ {R = Σ (Code X) (λ i → Code (obj φ i))} {S = Σ (Code X) (λ i → Code (obj φ i))} π₀ π₀ ρ
--algorn ρ φ = {! mor φ  !}

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
