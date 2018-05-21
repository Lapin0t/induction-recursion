module orn where

open import utils
open import fam using (Fam; Code; decode)
open import iir


pow : (X : Fam Set₁) → Set₂
pow X = Σ (Code X → Set) (λ J → (ij : Σ (Code X) J) → decode X (π₀ ij) → Set₁)

pow→fam : ∀ {X} → (P : pow X) → Fam Set₁
Code (pow→fam {X} (J , Y)) = Σ (Code X) J
decode (pow→fam {X} (J , Y)) (i , j) = Σ (decode X i) (Y (i , j))



data poly-orn {X : Fam Set₁} (Y : pow X) : poly X → Set₁
info+ : ∀ {X Y γ} → poly-orn {X} Y γ → Set₁
info↓ : ∀ {X Y γ} (o : poly-orn {X} Y γ) → info+ o → info γ

data poly-orn {X} Y where
  -- structure preserving
  ι : {x : Code X} → (π₀ Y x) → poly-orn Y (ι x)
  κ : (A : Set) → poly-orn Y (κ A)
  σ : ∀ {P Q} → (A : poly-orn Y P) → (B : (a : info+ A) → poly-orn Y (Q (info↓ A a))) → poly-orn Y (σ P Q)
  π : (A : Set) → ∀ {P} → ((a : A) → poly-orn Y (P a)) → poly-orn Y (π A P)

  -- insertions/deletions
  add-σ : (A : poly (pow→fam Y)) → ∀ {P} → (info A → poly-orn Y P) → poly-orn Y P  -- OPTION 1
  add-κ : (A : Set) → ∀ {P} → (A → poly-orn Y P) → poly-orn Y P          -- OPTION 2, no new recursive positions
  del-κ : ∀ {A B} → (a : A) → poly-orn Y (B (lift a)) → poly-orn Y (σ (κ A) B)

info+ {X} {Y} (ι {i} j) = Σ (decode X i) (π₁ Y (i , j))
info+ (κ A) = Lift A
info+ (σ A B) = Σ (info+ A) (λ a → info+ (B a))
info+ (π A B) = (a : A) → info+ (B a)
info+ (add-σ A B) = Σ (info A) (λ a → info+ (B a))
info+ (add-κ A B) = Σ A (λ a → info+ (B a))
info+ (del-κ _ o) = info+ o

info↓ {X} {Y} (ι i) (x , _) = x
info↓ (κ A) a = a
info↓ (σ A B) (a , b) = info↓ A a , info↓ (B a) b
info↓ (π A B) f = λ a → info↓ (B a) (f a)
info↓ (add-σ A B) (a , b) = info↓ (B a) b
info↓ (add-κ A B) (a , b) = info↓ (B a) b
info↓ (del-κ a o) x = lift a , info↓ o x


-- interpret back to plain poly
⌊_⌋₀ : ∀ {X Y γ} → poly-orn {X} Y γ → poly (pow→fam Y)
info↑ : ∀ {X Y γ} → (o : poly-orn {X} Y γ) → info ⌊ o ⌋₀ → info+ o

⌊ ι {i} j ⌋₀ = ι (i , j)
⌊ κ A ⌋₀ = κ A
⌊ σ A B ⌋₀ = σ ⌊ A ⌋₀ λ a → ⌊ B (info↑ A a) ⌋₀
⌊ π A B ⌋₀ = π A λ a → ⌊ B a ⌋₀
⌊ add-σ A B ⌋₀ = σ A λ a → ⌊ B a ⌋₀
⌊ add-κ A B ⌋₀ = σ (κ A) λ { (lift a) → ⌊ B a ⌋₀ }
⌊ del-κ _ o ⌋₀ = ⌊ o ⌋₀

info↑ (ι j) (x , y) = x , y
info↑ (κ A) x = x
info↑ (σ A B) (a , b) = info↑ A a , info↑ (B _) b
info↑ (π A B) f = λ a → info↑ (B a) (f a)
info↑ (add-σ A B) (a , b) = a , info↑ (B a) b
info↑ (add-κ A B) (lift a , b) = a , info↑ (B a) b
info↑ (del-κ a o) x = info↑ o x


record orn {A B : Fam Set₁} (Y : pow A) (Z : pow B) (γ : FCT A B) : Set₁ where
  field
    node : (b : Code B) → poly-orn Y (node γ b)
    emit : (b : Σ (Code B) (π₀ Z)) → info+ (node (π₀ b)) → Σ (decode B (π₀ b)) (π₁ Z b)

⌊_⌋ : ∀ {A B Y Z γ} → (o : orn {A} {B} Y Z γ) → FCT (pow→fam Y) (pow→fam Z)
node ⌊ o ⌋ (b , z) = ⌊ orn.node o b ⌋₀
emit ⌊ o ⌋ (b , z) x = π₀ (orn.emit o (b , z) (info↑ (orn.node o b) x)) , π₁ (orn.emit o (b , z) (info↑ (orn.node o b) x))


data inv {α β} {A : Set α} {B : Set β} (f : A → B) : B → Set α where
  ok : (x : A) → inv f (f x)

to-pow : ∀ {X Y : Fam Set₁} → (e : Code Y → Code X) → (E : (y : Code Y) → decode Y y → decode X (e y)) → pow X
π₀ (to-pow e E) x = inv e x
π₁ (to-pow e E) (x , ok y) a = inv (E y) a
