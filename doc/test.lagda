%include agda.fmt

%format Set = "\DATA{Set}"
%format Set₁ = "\DATA{Set₁}"
%format ⊥ = "\DATA{⊥}"
%format ⊤ = "\DATA{⊤}"
%format * = "\CON{*}"
%format Σ = "\DATA{Σ}"
%format π₀ = "\FCT{π₀}"
%format π₁ = "\FCT{π₁}"
%format , = "\CON{,}"
%format _,_ = _ , _
%format lsuc = "\CON{lsuc}"
%format lzero = "\CON{lzero}"
%format ⊔ = "\FCT{⊔}"
%format Lift = "\DATA{Lift}"
%format lift = "\CON{lift}"
%format lower = "\FCT{lower}"
%format Fam = "\DATA{Fam}"
%format Code = "\FCT{Code}"
%format decode = "\FCT{decode}"
%format poly = "\DATA{poly}"
%format info = "\FCT{info}"
%format ι = "\CON{ι}"
%format κ = "\CON{κ}"
%format σ = "\CON{σ}"
%format π = "\CON{π}"

\begin{code}
module test where
open import Agda.Primitive public

data ⊥ : Set where
data ⊤ : Set where * : ⊤

infixr 4 _,_
record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀

open Σ public

record Lift {α β} (A : Set α) : Set (α ⊔ β) where
  constructor lift
  field lower : A

open Lift public
\end{code}

%<*fam>
\begin{code}
record Fam {-<-}{α}{->-} (X : Set α) : Set (lsuc lzero ⊔ α) where
  constructor _,_
  field
    Code : Set
    decode : Code → X

open Fam public

data poly (X : Fam Set₁) : Set₁
info : {X : Fam Set₁} → poly X → Set₁

data poly X where
  ι : Code X → poly X
  κ : (A : Set) → poly X
  σ : (A : poly X) → (B : info A → poly X) → poly X
  π : (A : Set) → (B : A → poly X) → poly X

info {-<-}{X}{->-} (ι i) = decode X i
info (κ A) = Lift A
info (σ A B) = Σ (info A) λ x → info (B x)
info (π A B) = (a : A) → info (B a)
\end{code}
%</fam>
