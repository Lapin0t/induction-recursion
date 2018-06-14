%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.pow where
open import ornaments.prelude
open import ornaments.fam using (Fam; Code; decode; 𝔽; _⇒_; ISet)

record Pow (X : Set₁) : Set₂ where
  constructor _,_
  field
    PCode : Set
    Rel : PCode → X → Set₁

--  field
--    func : ∀ {a x y} → Rel a x → Rel a y → x ≡ y
--    tot : (a : PCode) → Σ X (λ x → Rel a x)

open Pow public

el : ∀ {X} → Pow X → X → Set₁
el P x = Σ (PCode P) (λ i → Rel P i x)

_⟶̊_ : ∀ {X} → Pow X → Pow X → Set₁
P ⟶̊ Q = (x : _) → el P x → el Q x

ℙ : (X : Fam Set₁) → Set₂
ℙ X = (i : _) → Pow (decode X i)

_⇒̊_ : ∀ {X} → ℙ X → ℙ X → Set₁
P ⇒̊ Q = (i : _) → P i ⟶̊ Q i


{-σ : {-<-}{X : Set₁} {Y : X → Set₁} → {->-}(A : Pow X) → (B : (x : X) → Pow (Y x)) → Pow (Σ X Y)
PCode  (σ A B)                  = Σ (PCode A) λ a → PCode (B (π₀ (tot A a)))
Rel    (σ A B) (a , b) (x , y)  = Σ (Rel A a x) aux
  where aux : Rel A a x → Set₁
        aux p with func A p (π₁ $ tot A a)
        ...   | refl = {!Rel (B x) b y!}
func   (σ A B) r₁ r₂            = ?
tot    (σ A B) (a , b)          = (π₀ aux₀ , π₀ aux₁) , (π₁ aux₀ , {!  π₁ aux₁ !})
  where aux₀ : _
        aux₀ = tot A a
        aux₁ : _
        aux₁ = tot (B _) b-}

{-π : (A : Set) {-<-}{X : A → Set₁} {->-}(B : (a : A) → Pow (X a)) → Pow ((a : A) → X a)
PCode  (π A B)      = (a : A) → PCode (B a)
Rel    (π A B) f p  = (a : A) → Rel (B a) (f a) (p a)
func   (π A B) r₁ r₂ = funext λ a → func (B a) (r₁ a) (r₂ a)
tot    (π A B) f    = let aux = λ a → tot (B a) (f a) in (π₀ ∘ aux , π₁ ∘ aux)-}

record iso {X} (F : 𝔽 X) (R : (i : _) → Code (F i) → decode X i → Set₁) : Set₁ where
  field
    to : ∀ {i x} → R i x (decode (F i) x)
    from : ∀ {i x y} → R i x y → decode (F i) x ≡′ y

  i-pow : ℙ X
  PCode  (i-pow i)        = Code (F i)
  Rel    (i-pow i)        = R i
  --func   (i-pow i) r₁ r₂  = trans (sym (from r₁)) (from r₂)
  --tot    (i-pow i) a      = decode (F i) a , to

open iso public


trans-arr : ∀ {X} {F G : 𝔽 X} {P Q} (A : iso F P) (B : iso G Q) → i-pow A ⇒̊ i-pow B → F ⇒ G
trans-arr A B f i x with f i _ (x , to A)
...                 | x′ , q = x′ , from B q

PFam : ∀ {X} → ℙ X → ISet
Code (PFam P) = Σ _ (PCode ∘ P)
decode (PFam P) (i , j) = Σ _ (Rel (P i) j)

--orn-ℙ : ∀ {X} (P : ℙ X) (F : 𝔽 X) → Set₁
--orn-ℙ P F = (i : Code (PFam P)) → (x : Code (F $ π₀ i)) → Σ Set λ A → A → Rel (P $ π₀ i) (π₁ i) (decode (F $ π₀ i) x)

--P→F : ∀ {X} {P : ℙ X} {F : 𝔽 X} → orn-ℙ P F → 𝔽 (PFam P)
--Code (P→F A i) = Σ _ (π₀ ∘ A i)
--decode (P→F A i) (x , y) = _ , π₁ (A i x) y

--F→P : ∀ {X} → 𝔽 X → ℙ X
--PCode (F→P F i) = Code (F i)
--Rel (F→P F i) x y = decode (F i) x ≡ y
--func (F→P F i) r₁ r₂ = trans (sym r₁) r₂
--tot (F→P F i) a = _ , refl

--P→F : ∀ {X} → ℙ X → 𝔽 X
--Code (P→F P i) = PCode (P i)
--decode (P→F P i) x = π₀ (tot (P i) x)

{-PF-iso : ∀ {X} {F : 𝔽 X} → iso F (λ i x y → decode (F i) x ≡ y)
to PF-iso = refl
from PF-iso = λ x → x-}
\end{code}
