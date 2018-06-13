%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.pow where
open import ornaments.prelude
open import ornaments.fam

--pow : Set₁ → Set₂
--pow X = Σ Set (λ A → A → X → Set₁)

record Pow (X : Set₁) : Set₂ where
  constructor _,_
  field
    PCode : Set
    Rel : PCode → X → Set₁
open Pow public

el : ∀ {X} → Pow X → X → Set₁
--Code (el P x) = PCode P
--decode (el P x) i = Rel P i x
el P x = Σ (PCode P) (λ i → Rel P i x)

_⟶̊_ : ∀ {X} → Pow X → Pow X → Set₁
P ⟶̊ Q = (x : _) → el P x → el Q x

ℙ : (X : Fam Set₁) → Set₂
ℙ X = (i : _) → Pow (decode X i)

_⇒̊_ : ∀ {X} → ℙ X → ℙ X → Set₁
P ⇒̊ Q = (i : _) → P i ⟶̊ Q i

record iso {X} (F : 𝔽 X) (R : (i : _) → Code (F i) → decode X i → Set₁) : Set₁ where
  pow : ℙ X
  pow i = Code (F i) , R i
  field
    to : ∀ {i x} → R i x (decode (F i) x)
    from : ∀ {i x y} → R i x y → decode (F i) x ≡ y
open iso public

trans-arr : ∀ {X} {F G : 𝔽 X} {P Q} (A : iso F P) (B : iso G Q) → pow A ⇒̊ pow B → F ⇒ G
trans-arr A B f i x with f i _ (x , to A)
...                 | x′ , q = x′ , from B q

PFam : ∀ {X} → ℙ X → ISet
Code (PFam P) = Σ _ (PCode ∘ P)
decode (PFam P) (i , j) = Σ _ (Rel (P i) j)

--P→F : ∀ {X} → 𝔽 X → (P : ℙ X) → 𝔽 (PFam P)
--Code (P→F F P (i , j)) = Code (F i)
--decode (P→F F P (i , j)) x = {!   !} , {!   !}

--P→F : ∀ {X} → (P : ℙ X) → 𝔽 X --(Σ (Code X) (λ i → PCode (P i)) , λ { (i , j) → Σ (decode X i) (Rel (P i) j) })
--Code (P→F P i) = PCode (P i)
--decode (P→F P i) x = {!   !}

\end{code}
