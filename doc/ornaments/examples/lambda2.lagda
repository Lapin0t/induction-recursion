%include agda.fmt
%include ornaments.fmt

\begin{code}
module ornaments.examples.lambda2 where

open import ornaments.prelude
open import ornaments.fam hiding (σ; π)
open import ornaments.pow
open import ornaments.iir hiding (α; β; γ; δ; ε; X; Y)
open import ornaments.orn hiding (α₀; α₁; β₀; β₁; γ₀; γ₁; δ; X; Y; R; S)
open import ornaments.induction hiding (α; β; γ; δ; ε; X; s)
\end{code}


%<*nat>
\begin{code}
data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ
\end{code}
%</nat>

%<*fin>
\begin{code}
data fin : ℕ → Set where
  ze : ∀ {n} → fin (su n)
  su : ∀ {n} → fin n → fin (su n)
\end{code}
%</fin>

%<*bwd>
\begin{code}
data bwd (X : Set) : Set where
  ε : bwd X
  _,,_ : bwd X → X → bwd X
\end{code}
%</bwd>

%<*length>
\begin{code}
length : ∀ {X} → bwd X → ℕ
length ε = ze
length (Γ ,, _) = su (length Γ)
\end{code}
%</length>

%<*idx>
\begin{code}
idx : ∀ {X} (Γ : bwd X) → Set
idx Γ = fin (length Γ)
\end{code}
%</idx>

%<*get>
\begin{code}
get : ∀ {X} (Γ : bwd X) → idx Γ → X
get (Γ ,, x) ze = x
get (Γ ,, x) (su n) = get Γ n
\end{code}
%</get>

----------------------
-- untyped lambda calculus

%<*ulam-ix>
\begin{code}
ulam-ix : ISet lzero lzero
Code ulam-ix = ℕ
decode ulam-ix = λ _ → ⊤
\end{code}
%</ulam-ix>

%<*ulam-c>
\begin{code}
data ulam-tag : Set where `var `app `lam `wrap : ulam-tag

ulam-c : IIR lzero ulam-ix ulam-ix
node ulam-c n = σ (κ ulam-tag) (λ {
  (lift `var)  → κ (fin n);
  (lift `app)  → σ (ι n) (λ _ → ι n);
  (lift `lam)  → ι (su n);
  (lift `wrap) → ι n })
emit ulam-c n _ = *
\end{code}
%</ulam-c>

%<*ulam>
\begin{code}
ulam : ℕ → Set
ulam n = μ-c ulam-c n
\end{code}
%</ulam>

-----------------------
-- STLC

%<*type>
\begin{code}
data type : Set where
  `base : type
  _`⇒_ : type → type → type
\end{code}
%</type>

%<*env>
\begin{code}
env : Set
env = bwd type
\end{code}
%</env>

%<*dir>
\begin{code}
data dir : Set where chk syn : dir
\end{code}
%</dir>

%<*IN>
\begin{code}
IN : dir → Set
IN chk = type
IN syn = ⊤
\end{code}
%</IN>

%<*OUT>
\begin{code}
OUT : dir → Set
OUT chk = ⊤
OUT syn = type
\end{code}
%</OUT>

%<*tlam-ix>
\begin{code}
tlam-ix : PRef lzero lzero ulam-ix
Code tlam-ix = env × Σ dir IN
down tlam-ix (Γ , _) = length Γ
decode tlam-ix (_ , d , _) _ = OUT d
\end{code}
%</tlam-ix>

%<*tlam-tags>
\begin{code}
data syn-tag : Set where `var `app `ann : syn-tag
data chk-tag : Set where `lam `vrf : chk-tag
\end{code}
%</tlam-tags>

%<*tlam-node>
\begin{code}
tlam-c : orn lzero tlam-ix tlam-ix ulam-c
node tlam-c (Γ , chk , `base)  =
  σ  (del-κ `wrap)
     λ _ → add₁ (ι (Γ , syn , *)) λ { (lift (_ , t)) → κ (t ≡ `base) }
node tlam-c (Γ , chk , r `⇒ s) = add₀ (κ chk-tag) λ {
  (lift `lam) → σ (del-κ `lam) λ _ → ι (Γ ,, r , chk , s);
  (lift `vrf) → σ (del-κ `wrap) λ _ → add₁ (ι (Γ , syn , *)) λ { (lift (_ , t)) → κ (t ≡ r `⇒ s) } }
node tlam-c (Γ , syn , _) = add₀ (κ syn-tag) λ {
  (lift `var) → σ (del-κ `var) λ _ → κ;
  (lift `app) → σ (del-κ `app) λ _ → σ (ι (Γ , syn , *)) (λ {
    (lift (_ , `base)) → add₀ (κ ⊥) λ ();
    (lift (_ , (r `⇒ s))) → ι (Γ , chk , r) });
  (lift `ann) → σ (del-κ `wrap) λ _ → add₀ (κ type) (λ { (lift r) → ι (Γ , chk , r) }) }
\end{code}
%</tlam-node>
%<*tlam-emit>
\begin{code}
emit tlam-c (Γ , chk , _) _ = *
emit tlam-c (Γ , syn , *) (lift `var , _ , lift (lift i)) = get Γ i
emit tlam-c (Γ , syn , *) (lift `app , _ , lift (_ , `base) , lift () , _)
emit tlam-c (Γ , syn , *) (lift `app , _ , lift (_ , (r `⇒ s)) , _) = s
emit tlam-c (Γ , syn , *) (lift `ann , _ , lift r , _) = r
\end{code}
%</tlam-emit>

%<*tlam>
\begin{code}
tlam : (Γ : env) (d : dir) (i : IN d) → Set
tlam Γ d i = μ-c ⌊ tlam-c ⌋ (Γ , d , i)
\end{code}
%</tlam>

%<*out>
\begin{code}
out : ∀ {Γ d i} → tlam Γ d i → OUT d
out x = π₁ $ μ-d ⌊ tlam-c ⌋ _ x
\end{code}
%</out>
