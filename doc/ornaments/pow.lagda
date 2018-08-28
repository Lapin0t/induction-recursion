%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.pow where
open import ornaments.prelude
open import ornaments.fam hiding (el; α₀; α₁; β₀; β₁)

variable
  {α₀ α₁} : Level
  {β₀ β₁} : Level

\end{code}


%<*pref>
\begin{code}
record PRef {-<-}{α₀ β₀}{->-}(α₁ β₁ : Level) (X : ISet α₀ β₀) : Set (α₀ ⊔ β₀ ⊔ lsuc α₁ ⊔ lsuc β₁) where
  field
    Code : Set α₁
    down : Code → Fam.Code X
    decode : (j : Code) → decode X (down j) → Set β₁
open PRef public
\end{code}
%</pref>

%<*pfam>
\begin{code}
PFam : {-<-}{X : ISet α₀ β₀} →{->-}PRef α₁ β₁ X → ISet α₁ (β₀ ⊔ β₁)
Code (PFam P) = Code P
decode (PFam P) j = Σ _ (decode P j)
\end{code}
%</pfam>

%<*ref>
\begin{code}
Ref : ∀ {α β γ} {X : ISet α β} (F : 𝔽 γ X) → PRef (α ⊔ γ) β X
Code (Ref F) = Σ _ (Code ∘ F)
down (Ref F) (i , _) = i
decode (Ref F) (i , j) x = decode (F i) j ≡ x
\end{code}
%</ref>


\begin{code}


PObj : {X : ISet α₀ β₀}(γ₁ : Level) (R : PRef α₁ β₁ X) (F : 𝔽 γ₀ X) → Set (α₁ ⊔ β₁ ⊔ lsuc (γ₀ ⊔ γ₁))
PObj {γ₀ = γ₀} γ₁ R F = (j : Code $ PFam R) → (x : Code (F $ down R j)) → Fam (γ₀ ⊔ γ₁) (decode R j (decode (F $ down R j) x))


{-infix 30 _&_
_&_ : {X : ISet α₀ β₀}{R : PRef α₁ β₁ X}(F : 𝔽 γ₀ X) (G : PObj γ₁ R F) → 𝔽 (γ₀ ⊔ γ₁) (PFam R)
Code ((F & G) j) = Σ _ (Code ∘ G j)
decode ((F & G) j) (x , y) = _ , decode (G j x) y-}





{-record PObj {α₀ α₁ β₀ β₁ γ₀} {X : ISet α₀ β₀} (γ₁ : Level) (R : PRef α₁ β₁ X) (F : 𝔽 γ₀ X) : Set (α₁ ⊔ β₁ ⊔ lsuc (γ₀ ⊔ γ₁)) where
  field
    addon : (j : Code $ PFam R) → (x : Code (F $ down R j)) → Fam (γ₀ ⊔ γ₁) (decode R j (decode (F $ down R j) x))

  pfam : 𝔽 (γ₀ ⊔ γ₁) (PFam R)
  Code (pfam j) = Σ _ (Code ∘ addon j)
  decode (pfam j) (x , y) = _ , decode (addon j x) y

open PObj public-}
\end{code}
