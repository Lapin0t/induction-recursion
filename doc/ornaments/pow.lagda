%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.pow where
open import ornaments.prelude
open import ornaments.fam hiding (el)

--record Pow (α : Level) {β} (X : Set β) : Set (lsuc (α ⊔ β)) where
--  constructor _,_
--  field
--    PCode : Set α
--    Rel : PCode → X → Set β
--    func : ∀ {a x y} → Rel a x → Rel a y → x ≡ y
--    tot : (a : PCode) → Σ X (λ x → Rel a x)
--open Pow public

record PRef {α₀ β₀} (α₁ β₁ : Level) (X : ISet α₀ β₀) : Set (α₀ ⊔ β₀ ⊔ lsuc α₁ ⊔ lsuc β₁) where
  field
    Code : Set α₁
    down : Code → Fam.Code X
    decode : (j : Code) → decode X (down j) → Set β₁
open PRef public

variable
  {α₀ α₁} : Level
  {β₀ β₁} : Level

PFam : {X : ISet α₀ β₀} → PRef α₁ β₁ X → ISet α₁ (β₀ ⊔ β₁)
Code (PFam P) = Code P
decode (PFam P) j = Σ _ (decode P j)

Ref : ∀ {α β γ} {X : ISet α β} (F : 𝔽 γ X) → PRef (α ⊔ γ) β X
Code (Ref F) = Σ _ (Code ∘ F)
down (Ref F) (i , _) = i
decode (Ref F) (i , j) x = decode (F i) j ≡ x


record PObj {α₀ α₁ β₀ β₁} {X : ISet α₀ β₀} (γ₀ γ₁ : Level) (R : PRef α₁ β₁ X) : Set (α₀ ⊔ β₀ ⊔ α₁ ⊔ β₁ ⊔ lsuc γ₀ ⊔ lsuc γ₁) where
  field
    ifam : 𝔽 γ₀ X
    addon : (j : Code $ PFam R) → (x : decode X $ down R j) → Fam γ₁ $ decode R j x

  pfam : 𝔽 (γ₀ ⊔ γ₁) (PFam R)
  Code (pfam j) = Σ (Code ∘ ifam $ down R j) λ x → Code ∘ addon j $ decode (ifam $ down R j) x
  decode (pfam j) (x , y) = _ , decode (addon j $ decode (ifam $ down R j) x) y
open PObj public

{-el : ∀ {α β} {X : Set β} → Pow α X → X → Set (α ⊔ β)
el P x = Σ (PCode P) (λ i → Rel P i x)

_⟶̊_ : ∀ {α β} {X : Set β} → Pow α X → Pow α X → Set (α ⊔ β)
P ⟶̊ Q = (x : _) → el P x → el Q x

ℙ : ∀ {α β} (X : ISet α β) → Set (lsuc (α ⊔ β))
ℙ {α} X = (i : _) → Pow α (decode X i)

_⇒̊_ : ∀ {α β} {X : ISet α β} → ℙ X → ℙ X → Set (α ⊔ β)
P ⇒̊ Q = (i : _) → P i ⟶̊ Q i-}


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

{-record iso {α β} {X : ISet α β} (F : 𝔽 X) (R : (i : _) → Code (F i) → decode X i → Set β) : Set (α ⊔ β) where
  field
    to : ∀ {i x} → R i x (decode (F i) x)
    from : ∀ {i x y} → R i x y → decode (F i) x ≡′ y

  i-pow : ℙ X
  PCode  (i-pow i)        = Code (F i)
  Rel    (i-pow i)        = R i
open iso public


trans-arr : ∀ {α β} {X : ISet α β} {F G : 𝔽 X} {P Q} (A : iso F P) (B : iso G Q) → i-pow A ⇒̊ i-pow B → F ⇒ G
trans-arr A B f i x with f i _ (x , to A)
...                 | x′ , q = x′ , from B q-}

--PFam : ∀ {α β} {X : ISet α β} → ℙ X → ISet α β
--Code (PFam P) = Σ _ (PCode ∘ P)
--decode (PFam P) (i , j) = Σ _ (Rel (P i) j)

--open PObj public

--PFObj {α} {_} {X} P = Σ (𝔽 X) λ F → (i : Code (PFam P)) (x : Code (F $ π₀ i)) → Fam α (Rel (P $ π₀ i) (π₁ i) (decode (F $ π₀ i) x))
--(i : Code X) → Σ (Fam α (decode X i)) λ F → (j : PCode (P i)) → (x : Code F) → Fam α (Rel (P i) j (decode F x))

--to-fam : ∀ {α β} {X : ISet α β} {P : ℙ X} → PFObj P → 𝔽 X
--to-fam P = π₀ P

--to-pfam : ∀ {α β} {X : ISet α β} {P : ℙ X} → PFObj P → 𝔽 (PFam P)
--Code (to-pfam P i) = Σ _ (Code ∘ π₁ P i)
--decode (to-pfam P i) (x , y) = _ , decode (π₁ P i x) y

--orn-ℙ : ∀ {α β} {X : ISet α β} (P : ℙ X) (F : 𝔽 X) → Set (lsuc α ⊔ β)
--orn-ℙ {α} P F = (i : Code (PFam P)) → (x : Code (F $ π₀ i)) → Fam α (Rel (P $ π₀ i) (π₁ i) (decode (F $ π₀ i) x))

--P→F : ∀ {α β} {X : ISet α β} {P : ℙ X} {F : 𝔽 X} → orn-ℙ P F → 𝔽 (PFam P)
--Code (P→F A i) = Σ _ (Code ∘ A i)
--decode (P→F A i) (x , y) = _ , decode (A i x) y

--F→P : ∀ {α β} {X : ISet α β} → 𝔽 X → ℙ X
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
