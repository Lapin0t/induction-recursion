module ir where

open import prelude
open import family

data poly (X : idx) : Set₁
info : ∀ {X} → poly X → Set₁

data poly X where
  ι : (i : IN X)                         → poly X
  κ : (A : Set)                          → poly X
  σ : (A : poly X) (B : info A → poly X) → poly X
  π : (A : Set)    (B : A      → poly X) → poly X

info {X} (ι i) = OUT X i
info (κ A)     = lift _ A
info (σ A B)   = Σ (info A) λ a → info (B a)
info (π A B)   = (a : A) → info (B a)

record IR (X : idx) : Set₁ where
  field
    node : (i : IN X) → poly X
    emit : (i : IN X) → info (node i) → OUT X i
open IR public

⟦_⟧₀ : ∀ {X} (ρ : poly X) → ifam X → fam (info ρ)
⟦ ι i   ⟧₀ F = F i
⟦ κ A   ⟧₀ F = A , ↑
⟦ σ A B ⟧₀ F = FΣ (⟦ A ⟧₀ F) λ a → ⟦ B a ⟧₀ F
⟦ π A B ⟧₀ F = FΠ A λ a → ⟦ B a ⟧₀ F

⟦_⟧ : ∀ {X} (ρ : IR X) → ifam X → ifam X
⟦ ρ ⟧ F i = emit ρ i << ⟦ node ρ i ⟧₀ F

⟦_⟧[_]₀ : ∀ {X} (ρ : poly X) {F G : ifam X} → F ⇒ G → ⟦ ρ ⟧₀ F ⟶ ⟦ ρ ⟧₀ G
⟦ ι i   ⟧[ φ ]₀ = φ i
⟦ κ A   ⟧[ φ ]₀ = λ a → a , refl
⟦ σ A B ⟧[ φ ]₀ = FΣ⟶ ⟦ A ⟧[ φ ]₀ λ a → ⟦ B a ⟧[ φ ]₀
⟦ π A B ⟧[ φ ]₀ = FΠ⟶ λ a → ⟦ B a ⟧[ φ ]₀

⟦_⟧[_] : ∀ {X} (ρ : IR X) {F G : ifam X} → F ⇒ G → ⟦ ρ ⟧ F ⇒ ⟦ ρ ⟧ G
⟦ ρ ⟧[ φ ] i = emit ρ i <<$ ⟦ node ρ i ⟧[ φ ]₀

--info' : ∀ {X} {Y : IN X → Set₁} (R : (i : IN X) → Y i → OUT X i) → poly X → Set₁
--info↓ : ∀ {X} {Y : IN X → Set₁} {R : (i : IN X) → Y i → OUT X i} (ρ : poly X) → info' R ρ → info ρ
{-info' : ∀ {X Y} (R : X ⊇ Y) → poly X → Set₁
info↓ : ∀ {X Y} {R : X ⊇ Y} (ρ : poly X) → info' R ρ → info ρ

info' R (ι i)   = Σ (↓-in R ⁻¹ i) (comp (OUT _))
info' R (κ A)   = lift _ A
info' R (σ A B) = Σ (info' R A) λ a → info' R (B (info↓ A a))
info' R (π A B) = (a : A) → info' R (B a)

info↓ {R = R} (ι _) (ok j , c) = ↓-out R j c
info↓ (κ A)   x       = x
info↓ (σ A B) (a , b) = info↓ A a , info↓ (B _) b
info↓ (π A B) f       = λ a → info↓ (B _) (f a)

[_]⟦_⟧₀ : ∀ {X₀ X₁} (R : X₀ ⊇ X₁) (ρ : poly X₀) → ifam X₁ → fam (info' R ρ)
[ R ]⟦ ι i   ⟧₀ X = Σ (↓-in R ⁻¹ i) (λ { (ok j) → code (X j) }) , λ { (ok j , c) → ok j , dec (X j) c }
[ R ]⟦ κ A   ⟧₀ X = A , ↑
[ R ]⟦ σ A B ⟧₀ X = FΣ ([ R ]⟦ A ⟧₀ X) λ a → [ R ]⟦ B (info↓ A a) ⟧₀ X
[ R ]⟦ π A B ⟧₀ X = FΠ A λ a → [ R ]⟦ B a ⟧₀ X

[_]⟦_⟧ : ∀ {X₀ X₁} (R : X₀ ⊇ X₁) (ρ : IR X₀) → ifam X₁ → ifam X₀
[ R ]⟦ ρ ⟧ X i = (emit ρ i ∘ info↓ _) << [ R ]⟦ node ρ i ⟧₀ X-}
