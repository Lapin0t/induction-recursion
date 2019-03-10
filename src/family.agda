module family where

open import prelude

record fam (X : Set₁) : Set₁ where
  constructor _,_
  field
    code : Set
    dec : code → X
open fam public

--_&_ : ∀ {X Y} → fam X → fam Y → fam (X × Y)
--code (F & G) = code F × code G
--dec (F & G) (x , y) = dec F x , dec G y

_⟶_ : ∀ {X} → fam X → fam X → Set
F ⟶ G = (x : code F) → Σ[ y ∈ code G ] (dec F x ≡ dec G y)

_∘₀_ : ∀ {X} {F G H : fam X} → G ⟶ H → F ⟶ G → F ⟶ H
(m ∘₀ n) x = π₀ $ m $ π₀ $ n x , trans (π₁ $ n x) (π₁ $ m _)

_<<_ : ∀ {X Y} (f : X → Y) → fam X → fam Y
code (f << F) = code F
dec (f << F) x = f (dec F x)

_<<$_ : ∀ {X Y} (f : X → Y) {A B : fam X} → A ⟶ B → (f << A) ⟶ (f << B)
f <<$ m = λ x → let y , e = m x in y , cong f e

FΣ : ∀ {X} (A : fam X) {Y} (B : (x : X) → fam (Y x)) → fam (Σ X Y)
code (FΣ A B) = Σ (code A) λ a → code (B (dec A a))
dec (FΣ A B) (a , b) = dec A a , dec (B _) b

FΣ⟶ : ∀ {X} {A A' : fam X} {Y : X → Set₁} {B B' : (x : X) → fam (Y x)} → A ⟶ A' → ((x : X) → B x ⟶ B' x) → FΣ A B ⟶ FΣ A' B'
FΣ⟶ {A = A} {A'} {B' = B'} mA mB (a , b) =
  let (a' , ea) = mA a in
  let (b' , eb) = mB _ b in
  (a' , (subst (code ∘ B') ea b')) ,
  Σ-ext ea (trans eb (cong₂ (dec ∘ B') ea (sym (subst-coh _ ea))))

FΠ : (A : Set) {Y : A → Set₁} (B : (x : A) → fam (Y x)) → fam ((x : A) → Y x)
code (FΠ A B) = (x : A) → code (B x)
dec (FΠ A B) f = λ x → dec (B x) (f x)

FΠ⟶ : ∀ {A : Set} {Y : A → Set₁} {B B' : (x : A) → fam (Y x)} → ((x : A) → B x ⟶ B' x) → FΠ A B ⟶ FΠ A B'
FΠ⟶ mB f = (π₀ ∘ mB _ ∘ f) , Π-ext (π₁ ∘ mB _ ∘ f)

record idx : Set₂ where
  constructor _,_
  field
    IN : Set
    OUT : IN → Set₁
open idx public

ifam : (X : idx) → Set₁
ifam X = (i : IN X) → fam (OUT X i)

_⇒_ : ∀ {X} → ifam X → ifam X → Set
F ⇒ G = ∀ i → F i ⟶ G i

infixl 20 _⊙_

_⊙_ : ∀ {X} {F G H : ifam X} → G ⇒ H → F ⇒ G → F ⇒ H
(m ⊙ n) i = (m i) ∘₀ (n i)

_<<ᵢ_ : ∀ {I X Y} (f : (i : I) → X i → Y i) → ifam (I , X) → ifam (I , Y)
(f <<ᵢ F) i = f i << F i

_<<ᵢ$_ : ∀ {I} {X Y : I → Set₁} (f : (i : I) → X i → Y i) {A B : ifam (I , X)} → A ⇒ B → (f <<ᵢ A) ⇒ (f <<ᵢ B)
π₀ ((f <<ᵢ$ m) i x) = π₀ $ m i x
π₁ ((f <<ᵢ$ m) i x) = cong (f i) (π₁ $ m i x)

record _⊇_ (X₀ X₁ : idx) : Set₁ where
  field
    ↓-in : IN X₁ → IN X₀
    ↓-out : (j : IN X₁) → OUT X₁ j → OUT X₀ (↓-in j)
open _⊇_ public

--id⊇ : ∀ {X} → X ⊇ X
--↓-in id⊇ = λ i → i
--↓-out id⊇ _ = λ o → o

_/_ : ∀ {X₀ X₁} → ifam X₁ → X₀ ⊇ X₁ → ifam X₀
code ((F / R) i) = Σ (↓-in R ⁻¹ i) (λ { (ok j) → code (F j) })
dec ((F / R) .(↓-in R j)) (ok j , c) = ↓-out R j (dec (F j) c)

_⇒_[_] : ∀ {X₀ X₁} → ifam X₁ → ifam X₀ → X₀ ⊇ X₁ → Set
F ⇒ G [ R ] = (↓-out R <<ᵢ F) ⇒ (G ∘ ↓-in R)

--aux₀ : ∀ {X Y} {R : X ⊇ Y} {F G} → F ⇒ G [ R ] → (F / R) ⇒ G
--aux₀ m _ (ok j , x) = m j x

aux₁ : ∀ {X Y} {R : X ⊇ Y} {F G} → (F / R) ⇒ G → F ⇒ G [ R ]
aux₁ {R = R} m i x = m (↓-in R i) (ok i , x)
