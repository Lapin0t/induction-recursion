module cat where

open import prelude renaming (_∘_ to _∘f_)

record cat : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set

  _⇒_ : obj → obj → Set
  a ⇒ b = hom a b

  field
    _∘_ : ∀ {a b c} → b ⇒ c → a ⇒ b → a ⇒ c
    id : (a : obj) → a ⇒ a
    ∘-assoc : ∀ {a b c d} (f : c ⇒ d) (g : b ⇒ c) (h : a ⇒ b) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
    id-r : ∀ {a b} (f : a ⇒ b) → f ∘ id a ≡ f
    id-l : ∀ {a b} (f : a ⇒ b) → id b ∘ f ≡ f
open cat public hiding (_⇒_ ; _∘_)

_[_,_] : (C : cat) → obj C → obj C → Set
C [ a , b ] = cat._⇒_ C a b

_[_∘_] : (C : cat) {a b c : obj C} → C [ b , c ] → C [ a , b ] → C [ a , c ]
C [ f ∘ g ] = cat._∘_ C f g

record fct (C D : cat) : Set where
  field
    map₀ : obj C → obj D
    map₁ : ∀ {x y} → C [ x , y ] → D [ map₀ x , map₀ y ]

    prf-∘ : ∀ {x y z} (f : C [ y , z ]) (g : C [ x , y ]) → map₁ (C [ f ∘ g ]) ≡ D [ map₁ f ∘ map₁ g ]
    prf-id : (x : obj C) → map₁ (id C x) ≡ id D (map₀ x)
open fct public

_⊙_ : ∀ {C D E} → fct D E → fct C D → fct C E
map₀ (F ⊙ G) = map₀ F ∘f map₀ G
map₁ (F ⊙ G) = map₁ F ∘f map₁ G
prf-∘ (F ⊙ G) f g = trans (cong (map₁ F) (prf-∘ G f g)) (prf-∘ F _ _)
prf-id (F ⊙ G) x = trans (cong (map₁ F) (prf-id G x)) (prf-id F _)

id-fct : (C : cat) → fct C C
map₀ (id-fct C) x = x
map₁ (id-fct C) f = f
prf-∘ (id-fct C) _ _ = refl
prf-id (id-fct C) _ = refl

record nat-t {C D : cat} (F : fct C D) (G : fct C D) : Set where
  field
    η : (x : obj C) → D [ map₀ F x , map₀ G x ]
    prf-nat : ∀ {x y} (f : C [ x , y ]) → D [ η y ∘ map₁ F f ] ≡ D [ map₁ G f ∘ η x ]
open nat-t public

record adj (C D : cat) : Set where
  field
    left : fct D C
    right : fct C D
    unit : nat-t (left ⊙ right) (id-fct C)
    counit : nat-t (id-fct D) (right ⊙ left)
open adj public

arrow : cat → cat
obj (arrow C) = Σ (obj C × obj C) λ { (a , b) → C [ a , b ] }
cat.hom (arrow C) (a , b , _) (a' , b' , _) = (C [ a , a' ]) × (C [ b' , b ])
cat._∘_ (arrow C) (f , g) (f' , g') = (C [ f ∘ f' ]) , (C [ g' ∘ g ])
id (arrow C) _ = id C _ , id C _
∘-assoc (arrow C) _ _ _ = Σ-ext (∘-assoc C _ _ _) (sym (∘-assoc C _ _ _))
id-r (arrow C) _ = Σ-ext (id-r C _) (id-l C _)
id-l (arrow C) _ = Σ-ext (id-l C _) (id-r C _)

comma : ∀ {A B C} (S : fct A C) (T : fct B C) → cat
obj (comma {A} {B} {C} S T) = Σ (obj A × obj B) λ { (a , b) → C [ map₀ S a , map₀ T b ] }
cat.hom (comma {A} {B} {C} S T) (a , b , f) (a' , b' , f') =
  Σ ((A [ a , a' ]) × (B [ b , b' ])) λ { (m , m') →
    (C [ map₁ T m' ∘ f ]) ≡ (C [ f' ∘ map₁ S m ]) }
π₀ (cat._∘_ (comma {A} {B} S T) (f , g , _) (f' , g' , _)) =
  A [ f ∘ f' ] , B [ g ∘ g' ]
π₁ (cat._∘_ (comma {C = C} S T) (_ , p) (_ , p')) =
  subst₂ (λ x y → (C [ x ∘ _ ]) ≡ (C [ _ ∘ y ])) (sym (prf-∘ T _ _)) (sym (prf-∘ S _ _))
  (subst₂ (λ x y → x ≡ y) (sym (∘-assoc C _ _ _)) (∘-assoc C _ _ _)
   (subst₂ (λ x y → (C [ _ ∘ x ]) ≡ (C [ y ∘ _ ])) (sym p') p
    (sym (∘-assoc C _ _ _))))
π₀ (id (comma {A} {B} S T) (a , b , _)) = id A a , id B b
π₁ (id (comma {C = C} S T) (a , b , f)) =
  subst₂ (λ x y → (C [ x ∘ _ ]) ≡ (C [ _ ∘ y ])) (sym (prf-id T _)) (sym (prf-id S _))
  (trans (id-l C _) (sym (id-r C _)))
∘-assoc (comma {A} {B} {C} S T) f g h = Σ-ext (Σ-ext (∘-assoc A _ _ _) (∘-assoc B _ _ _)) {! uoip _ _  !}
id-r (comma {A} {B} S T) _ = Σ-ext (Σ-ext (id-r A _) (id-r B _)) ?
id-l (comma {A} {B} S T) _ = Σ-ext (Σ-ext (id-l A _) (id-l B _)) {! uoip _ _  !}
