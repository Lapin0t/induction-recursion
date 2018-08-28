\documentclass[11pt,english]{article}

\usepackage{babel}
\usepackage{catchfilebetweentags}
\usepackage{natbib}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{prftree}
\usepackage{tikz-cd}
\usepackage{hyperref}
\usepackage[a4paper, margin=1.2in]{geometry}

%include agda.fmt
%include ornaments.fmt

\title{Ornamenting Inductive-Recursive Definitions}
\author{Peio Borthelle, Conor McBride}

\setlength{\abovedisplayskip}{10pt}

\newcommand{\todo}[1]{\textbf{TODO:}\textit{#1}}
\setlength\parindent{.7em}

\begin{document}

\maketitle


%%%%%%%%%%%%%%%%%%%%%%%%%%

%\newpage
\paragraph{Abstract}
We present a universe (a datatype of datatype descriptions) of endofunctors
with initial algebras that give rise to indexed inductive--recursive types,
\textit{eg} simultaneous definition of an inductive type family and a recursive
function on it. We provide a generic induction principle as well as some other
elimination rules.  Building upon that, we define a universe of
\textit{ornaments}, describing how to create an fancy version of a given
datatype by enriching its indexing sets while keeping the same inductive tree
shape. This allows us to introduce datatypes by giving more high--level
definitions than just their description, which in turns allows to collect free
theorems stated generically.


\tableofcontents

%%%%%%%%%%%%%%%%%%%%%%%%%%
%\newpage
\section{Introduction}
\label{sec:intro}

\paragraph{A Technical Preliminary} This research development has been
exclusively done formally, using the dependently--typed language Agda (U.
Norell, \cite{norell07}) as an interactive theorem--prover. As such this report is
full of code snippets, following the methodology of literate programming (D.
Knuth, \cite{knuth84}). Theorems are presented as type declaration, proofs are
implementations of such declarations and definitions are usually some kind of
datastructure introduction: it definitely lies on the \textit{program} side of
the Curry--Howard correspondance. The syntax and concepts of Agda should not be
too alien to a Haskell or Coq programmer but it might be interesting to start
out by reading the appendix \ref{sec:agda} which presents its most important
features. The full code can be found on
github\footnote{\url{https://github.com/Lapin0t/induction-recursion}}.

\paragraph{Motivations} Although they were probably first intended as theorem
provers, dependently--typed languages are currently evolving into
general--purpose programming languages, leveraging their expressivity to enable
correct--by--construction type--driven programming. But without the right tools
this new power is unmanageable. One issues is the need to prove over and over
again the same properties for similar datastructures. Ornaments (P-E. Dagand
and C. McBride \cite{dagand12}) tackle this problem by giving a formal syntax
to describe how datastructures might be \textit{similar}. Using these objects,
we can prove generic theorems once and for all. The broad idea behind this
approach is to ``speak in a more intelligible way to the computer'': if instead
of giving a concrete declarations we gave defining properties, we would be able
to systematically collect free theorems which hold by (some high level)
definition.

The present work aims to generalize ornaments to the widest possible notion of
datatypes: inductive--recursive families (or indexed inductive--recursive
types) as recently axiomatized by N. Ghani et al (\cite{ghani17}).

\paragraph{Acknowledgements}
This 3 month internship research project was conducted in the Mathematically
Structured Programming group of the University of Strathclyde, Glasgow under
supervision of Conor McBride as part of my M1 in theoretical computer science
at the university of ENS de Lyon. I spend an enjoyable time there with the
staff, PhD students and fellow interns, discovering a whole new world populated
by modalities, coinduction, quantitative types and cheering against England.
Many thanks to Ioan and Simone for sharing their roof. Last but not least I'm
grateful to Conor for sharing his insights on (protestant integrist) type
theory, taking the time to lead me through narrow difficulties or open doors
into new realms of thought. It was loads of fun and I'm looking forward to
collaborate again in some way or another.


{-<-}
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

open import ornaments.prelude
open import ornaments.fam hiding (el; σ; π)
open import ornaments.pow
open import ornaments.iir
open import ornaments.induction
open import ornaments.orn
\end{code}
{->-}

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Indexed Induction--Recursion}
\label{sec:iir}

%{
%format U = "\DATA{U}"
%format el = "\FCT{el}"
%format `ℕ = "\CON{`ℕ}"
%format `Π = "\CON{`Π}"
%format ℕ = "\DATA{ℕ}"

The motivation behind indexed induction--recursion is to provide a single rule
that can be specialized to create most of the types that are encountered in
Martin Loef's Intuitionistic Type Theory (ITT)\cite{loef84} such as inductive
types (W--types), inductive families \textit{etc}. This rule has been inspired
to P. Dybjer and A. Setzer (\cite{dybjer99,dybjer03}) by Martin Loef's
definition of a universe à--la--Tarski, an inductive set of codes |data U :
Set| and a recursive function |el : U → Set| reflecting codes into actual sets
(here a simple version with only natural numbers and Π--types).

{-<-}
\begin{code}
data U : Set
el : U → Set
\end{code}
{->-}

\noindent
\begin{minipage}[b]{0.5\textwidth}
\begin{code}
data U where
  `ℕ : U
  `Π : (A : U) (B : el A → U) → U
\end{code}
\end{minipage}
\begin{minipage}[b]{0.5\textwidth}
\begin{code}
el `ℕ        = ℕ
el (`Π A B)  = (a : el A) → el (B a)
\end{code}
\end{minipage}

%}

%\begin{center}\begin{tabular}{cc}
%\prftree[r]{$\DATA{U}$ intro}{\DATA{U}~\KW{set}}&
%\prftree[r]{$\FCT{el}$ intro}{\VAR{X} : \DATA{U}}{\FCT{el}~\VAR{X}~\KW{set}}\\
%&\\
%\prftree[r]{ℕ code}{\CON{\hat ℕ} : \DATA{U}}&
%\prftree[r]{ℕ decode}{\FCT{el}~\CON{\hat ℕ} = ℕ}\\
%&\\
%\prftree[r]{Π code}
%  {\VAR{A} : \DATA{U}}
%  {\VAR{B} : \FCT{el}~\VAR{A} → \DATA{U}}
%  {\CON{\hat Π}~\VAR{A}~\VAR{B} : \DATA{U}}&
%\prftree[r]{Π decode}
%  {\VAR{A} : \DATA{U}}
%  {\VAR{B} : \FCT{el}~\VAR{A} → \DATA{U}}
%  {\FCT{el}~(\CON{\hat Π}~\VAR{A}~\VAR{B}) = (\VAR{a} : \FCT{el}~\VAR{A}) → \FCT{el}~(\VAR{B}~\VAR{a})}\\
%\end{tabular}\end{center}

%{
%format U = "\DATA{U}"
%format X = "\DATA{X}"
%format I = "\DATA{I}"
%format f = "\FCT{f}"

We can see the most important caracteristic of inductive-recursive definitions:
the simultaneous definition of an inductive type and a recursive function on it
with the ability to use the recursive function in the type of the constructors,
even in negative positions (left of an arrow). \textit{Indexed}
inductive-recursive definitions are a slight generalization, similar to the
relationship between inductive types and inductive families. In its full
generality, indexed induction recursion \cite{dybjer06} allows to
simultaneously define an inductive predicate |U : I → Set| and an indexed
recursive function |f : (i : I) → U i → X i| for any |I : Set| and |X : I →
Set₁|. Using a vocabulary influenced by the \textit{bidirectional} paradigm for
typing (B. Pierce and D. Turner \cite{pierce00}) we will call |i : I| the
\textit{input index} and |X i| the \textit{output index}.  Indeed if we think
of the judgement |a : U i| as a typechecker would, the judgment requires the
validity of |i : I| and suffices to demonstrate the validity of |f a : X i|. We
will explore bidirectionality further in section \ref{sec:stlc}.

%}

Induction-recursion is arguably the most powerful set former (currently known)
for ITT. A. Setzer (\cite{setzer01}) has shown that its addition gives ITT a
proof-theoretic strength slightly greater than KPM, Kripke--Platek set theory
together with a recursive Mahlo universe. Although its proof-theoretic strength
is greater than $Γ₀$, ITT with induction--recursion is still considered
predicative in a looser constructivist sense: it arguably has bottom--to--top
construction.


%%%%%%%%%%


\subsection{Categories}

%{
%format C = "\DATA{C}"
%format D = "\DATA{D}"
%format ⇒ = "\DATA{⇒}"
%format _⇒_ = _ "\!" ⇒ "\!" _
%format 1 = "\FCT{1}"
%format ∘ = "\FCT{∘}"
%format _∘_ = _ "\!" ∘ "\!" _
%format F = "\FCT{F}"




%format F[_] = "\FCT{F[\anonymous]}"

Since we will use category theory as our main language we first recall the
definition of a category |C|:
\begin{itemize}
\item a collection of objects |C : Set|
\item a collection of morphisms (or arrows) |_⇒_ : (X Y : C) → Set|
\item an identity |1 : (X : C) → X ⇒ X|
\item a composition operation |_∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z| that is
  associative and respects the identity laws |1 X ∘ F ≡ F ≡ F ∘ 1 Y|
\end{itemize}

A functor |F| between categories |C| and |D| is a mapping of objects |F : C →
D| and a mapping of arrows |F[_] : ∀ {X Y} → X ⇒ F → F X ⇒ F Y|.

%}

\subsection{Data types}

The different notions of data types, by which we mean inductive types,
inductive--recursive types and their indexed variants, share their semantics:
initial algebras of endofunctors. In a first approximation, we can think of an
``initial algebra'' as the categorical notion for the ``least closed set''
(just not only for sets). As such, we will study a certain class of functors
with initial algebras that give rise to our indexed inductive--recursive types.

We shall determine the category our data types live in. The most simple data
types, inductive types, live in the category |Set|.  On the other hand,
as we have seen, inductive--recursive data types are formed by couples in
$(\DATA{U} : \DATA{Set})~×~(\DATA{U} → \DATA{X})$. Categorically, this an
$\DATA{X}$-indexed set and it is an object of the slice category of $\DATA{Set}
/ \DATA{X}$. We will be representing these objects by the record type |Fam γ
X|\footnote{See section \ref{sec:levels} for some explainations of |Level|, but for
most part it can be safely ignored, together with its artifacts |Lift|, |lift|
and the greek letters |α|, |β|, |γ| and |δ|.}.

\ExecuteMetaData[ornaments/fam.tex]{fam-def}
\ExecuteMetaData[ornaments/fam.tex]{morph}

This definition already gives us enough to express our first example of
inductive--recursive definition.

%format Πℕ-univ = "\VAR{Πℕ\!\!-\!\!univ}"

\begin{code}
Πℕ-univ : Fam lzero Set
Πℕ-univ = U , el
\end{code}

Now we can get to indexed inductive--recursive data types which essentially are
functions from an input index $\VAR{i} : \DATA{I}$ to
$(\DATA{X}~\VAR{i})$-indexed sets. We will use couples $(\DATA{I}~,~\DATA{X})$
a lot as they define the input and output indexing sets so we call their type
|ISet|.

\ExecuteMetaData[ornaments/fam.tex]{iset}
\ExecuteMetaData[ornaments/fam.tex]{ifam}
\ExecuteMetaData[ornaments/fam.tex]{ifam-arr}

Again we might consider our universe example as a trivially indexed type.

%format Πℕ-univᵢ = "\VAR{Πℕ\!\!-\!\!univᵢ}"
\begin{code}
Πℕ-univᵢ : 𝔽 lzero (⊤{-<-}{lzero}{->-} , λ _ → Set)
Πℕ-univᵢ _ = U , el
\end{code}

\subsection{A Universe of Strictly Positive Functors}

P. Dybjer and A. Setzer have first presented codes for (indexed)
inductive-recursive definitions by constructing a universe of functors.
However, as conjectured by \cite{ghani17}, this universe lacks closure under
composition, \textit{eg} if given the codes of two functors, we do not know how
to construct a code for the composition of the functors. We will thus use an
alternative universe construction devised by C. McBride (\cite{ghani17}) which
we call \textit{Irish} induction--recursion\footnote{It has also been called
\textit{polynomial} induction--recursion because it draws similarities to
polynomial functors, yet they are different notions and should not be
confused.}.

In this section we fix a given pair of input/output indexes |X Y : ISet α β|
and i will define codes |ρ : IIR δ X Y : Set| for some functors |⟦ ρ ⟧ : 𝔽 γ X → 𝔽
(γ ⊔ δ) Y|.

First we give a datatype of codes that will describe the first component
inductive--recursive functors. This definition is itself inductive--recursive:
we define a type |poly γ X : Set| representing the shape of the
constructor\footnote{It is easy to show that in a dependent theory, restricting
every type to a single constructor does not lose generality.} and a recursive
predicate |info : poly γ X → Set| representing the information contained in the
final datatype, underapproximating the information contained in a subnode by
the output index |X i| it delivers.

%\ExecuteMetaData[ornaments/iir.tex]{codes}

Lets give some intuition for these constructors.
\begin{itemize}
\item |ι i| codes an inductive position with input index |i|, \textit{eg} the
indexed identity functor. Its |info| is |decode X i| \textit{eg} the output
index that we will obtain from the later constructed recursive function.
\item |κ A| codes the constant functor, with straighforward information content |A|.
\item |σ A B| codes the dependent sum of a functor |A| and a functor family
|B| depending on |A|'s information.
\item |π A B| codes the dependent product, but strict positivity rules out
inductive positions in the domain. As such the functor |A| must be a constant
functor and we can (and must) make it range over |Set|, not |poly|.
\end{itemize}

The encoding of our Πℕ--universe goes as follows:

%format Πℕ-tag = "\DATA{Πℕ\!\!-\!\!tag}"
%format Πℕ₀ = "\VAR{Πℕ₀}"
%format Πℕc = "\VAR{Πℕc}"

\begin{code}
data Πℕ-tag : Set where `ℕ `Π : Πℕ-tag

Πℕ₀ : poly lzero (⊤{-<-}{lzero}{->-} , λ _ → Set)
Πℕ₀ = σ (κ Πℕ-tag) λ {   -- select a constructor
   -- no argument for `ℕ
  (lift `ℕ) → κ ⊤ ;
  -- first argument, an inductive position whose output index we bind to A
  -- second argument, a (non-dependent) Π type from A to an inductive position
  (lift `Π) → σ (ι *) λ { (lift A) → π A λ _ → ι * }}
\end{code}

We can now give the interpretation of a code |ρ : poly δ X| into a
functor |⟦ ρ ⟧₀|.

\ExecuteMetaData[ornaments/iir.tex]{fam-info}
\ExecuteMetaData[ornaments/iir.tex]{fct-hom-i}

The functors |f-σ| and |f-π| are functors that construct the dependent sum and
dependent product of families, allowing us to construct families and arrows on
them component by component. We will use them a couple more times in the same
kind of structural recursion on |poly|.

It would be time to check if this interpretation does the right thing on our
example, alas even simple examples of induction--recursion are somewhat
complicated, as such I do not think it would be informative to display here the
normalized expression of |⟦ Πℕc ⟧₀ F|. The reader is still encouraged to
normalize it by hand to familiarize with the interpretation.

While taking as parameter a indexed family |𝔽 γ X|, our intepreted functors
only output a family |Fam (γ ⊔ δ) (info ρ)|. In other words, |ρ : poly γ X|
only gives the structure of the definition for a given input index |i : Code
Y|. To account for that, the full description of the first component of
inductive--recursive functors has to be a function |node : Code Y → poly γ X|.
We are left to describe the recursive function, which can be done with a direct
|emit : (j : Code Y) → info (node j) → decode Y j| computing the output index
from the full information.

\ExecuteMetaData[ornaments/iir.tex]{iir}

We can now explain the index emitting function |el|, completing our encoding of
the Πℕ--universe.

\begin{code}
Πℕc : IIR lzero (⊤{-<-}{lzero}{->-} , λ _ → Set) (⊤{-<-}{lzero}{->-} , λ _ → Set)
node Πℕc _ = Πℕ₀
emit Πℕc _ (lift `ℕ , lift *)  = ℕ
emit Πℕc _ (lift `Π , A , B)   = (a : lower A) → lower $ B a
\end{code}

\ExecuteMetaData[ornaments/iir.tex]{fct-obj}
\ExecuteMetaData[ornaments/iir.tex]{fct-hom}

The post--composition functor we used is defined as follows:

\ExecuteMetaData[ornaments/fam.tex]{pcomp}
\ExecuteMetaData[ornaments/fam.tex]{pcomp-arr}

\subsection{Initial Algebra}

\subsubsection{Least Fixed--Point}
Now that we have a universe of functors, we need to translate that into actual
indexed inductive--recursive types. This amounts to taking its least
fixed--point |μ ρ|.

\ExecuteMetaData[ornaments/induction.tex]{mu-def}
~\\[-6ex]
\ExecuteMetaData[ornaments/induction.tex]{mu-impl}

It consists of two parts, the inductive family |μ-c ρ : Code X → Set| and the
recursive function |μ-d ρ : (i : Code X) → μ-c ρ i → decode X i|.  By chance
Agda has a primitive for constructing these kinds of sets: the |data| keyword.
Applying the interpreted functor to the least fixed--point with |⟦ ρ ⟧ (μ ρ)|
and the two components of the indexed family basically gives us the
implementation of respectively |μ-c ρ| and |μ-d ρ|.

\ExecuteMetaData[ornaments/induction.tex]{mu-tools}

We have now completed the encoding of Πℕ and we can write pretty versions the
constructors.

%{
%format U₁ = "\DATA{U₁}"
%format el₁ = "\FCT{el₁}"
%format `ℕ₁ = "\CON{`ℕ₁}"
%format `Π₁ = "\CON{`Π₁}"

\begin{minipage}[b]{0.5\textwidth}
\begin{code}
U₁ : Set
U₁ = μ-c Πℕc *
\end{code}
\end{minipage}
\begin{minipage}[b]{0.5\textwidth}
\begin{code}
el₁ : U₁ → Set
el₁ = μ-d Πℕc *
\end{code}
\end{minipage}

\begin{minipage}[b]{0.5\textwidth}
\begin{code}
`ℕ₁ : U₁
`ℕ₁ = ⟨ lift `ℕ , lift * ⟩
\end{code}
\end{minipage}
\begin{minipage}[b]{0.5\textwidth}
\begin{code}
`Π₁ : (A : U₁) (B : el₁ A → U₁) → U₁
`Π₁ A B = ⟨ lift `Π , lift A , lift ∘ B ⟩
\end{code}
\end{minipage}
%}

\subsubsection{Catamorphism and Paramorphism}

We previously said that this least--fixed point has in category theory the
semantic of an initial algebra. Let us break it down. Given an endofunctor |F :
C → C|, an |F|-algebras is a carrier |X : C| together with an arrow |F X ⇒ X|.
An arrow between two |F|-algebras |(X , φ)| and |(Y , ψ)| is an arrow |m : X ⇒
Y| subject to the commutativity of the usual square diagram |ψ ∘ F[ m ] ≡ m ∘
φ|.

%{
%format F = "\FCT{F}"
%format F[ = "\FCT{F[}"
%format ] = "\FCT{]}"
\begin{center}
\begin{tikzcd}
|F X| \arrow[r, "|φ|"] \arrow[d, "{|F[ m ]|}"'] & |X| \arrow[d, "|m|"] \\
|F Y| \arrow[r, "|ψ|"] & |Y|
\end{tikzcd}
\end{center}
%}


Additionaly, an object |X : C| is initial if for any |Y : C| we can give an
arrow |X ⇒ Y|.

We almost already have constructed an |⟦ ρ ⟧|-algebra with carrier |μ ρ| and
the constructor |⟨_⟩| mapping the object part of |⟦ ρ ⟧ (μ ρ)| to |μ ρ|. What
is left is to add a trivial proof.

\ExecuteMetaData[ornaments/induction.tex]{roll}


To prove the fact that our algebra is initial we have first have to formally
write the type of algebras.

\ExecuteMetaData[ornaments/induction.tex]{alg}

We can now give for every |φ : alg δ ρ| the initiality arrow |μ ρ ⇒ obj φ|.

\ExecuteMetaData[ornaments/induction.tex]{cata-def}
~\\[-6ex]
\ExecuteMetaData[ornaments/induction.tex]{cata-impl}

With the helper |foldm ρ| is defined as:

\ExecuteMetaData[ornaments/induction.tex]{catam-def}
~\\[-6ex]
\ExecuteMetaData[ornaments/induction.tex]{catam-impl}

Complying to the proof obligation for the equality condition, we get:

\ExecuteMetaData[ornaments/induction.tex]{cata-prop}

Note that we make use of |uoip| the unicity of identity proofs, together
with the associativity lemma |⊙-assoc|.

As hinted by its name, the initiality arrow |fold ρ| is in fact a generic fold
or with fancier wording an elimination rule, precisely the catamorphism (also
called recursor). An elimination rule is the semantic of recursive functions
with pattern matching. Diggressing a little on elimination rules, we can notice
that this is not the only one. Lets stop and write down the factorial function.

%{
%format foldℕ = "\FCT{foldℕ}"
%format +ℕ = "\FCT{+ℕ}"
%format _+ℕ_ = _ +ℕ _
%format *ℕ = "\FCT{*ℕ}"
%format _*ℕ_ = _ *ℕ _
%format fact = "\FCT{fact}"

\begin{code}
foldℕ : {-<-}∀ {α} {X : Set α}{->-} (f : X → X) (x : X) → ℕ → X
foldℕ f x zero = x
foldℕ f x (suc n) = f $ foldℕ f x n

_+ℕ_ : ℕ → ℕ → ℕ
_+ℕ_ = foldℕ suc

_*ℕ_ : ℕ → ℕ → ℕ
m *ℕ n = foldℕ (_+ℕ_ m) zero n

fact : ℕ → ℕ
fact zero = suc zero
fact (suc n) = suc n *ℕ fact n
\end{code}
%}

One should be convinced that |fact| cannot be expressed as |foldℕ f x|. Indeed
for the |suc n| case, besides the recursive call |fact n|, we need the
unchanged data |suc n|. To solve this we introduce \textit{paramorphisms} (the
equivalent notion of primitive recursion in category theory). The specification
is not an algebra |⟦ ρ ⟧ X ⇒ X| but an arrow |⟦ ρ ⟧ (μ ρ × X) ⇒ X|, the domain
of which is exactely a node where to every subnode we have added the recursive
computation (but also left them in place). Note that there is no added
power---only expressivity---since we can construct a fold with algebra |⟦ ρ ⟧
(μ ρ × X) ⇒ μ ρ × X| and drop the second component of the output. Every arrow
|μ ρ ⇒ X| can be expressed as |para φ| for some arrow |φ| (L. Merteens,
\cite{meertens92}), as such it is the most expressive (non--dependent)
eliminator. This expressivity of paramorphisms will be crucial in a later proof
on ornaments.

\ExecuteMetaData[ornaments/induction.tex]{p-alg}
\ExecuteMetaData[ornaments/induction.tex]{para-pre}
\ExecuteMetaData[ornaments/induction.tex]{para}

\subsection{Induction Principle}

We have given several elimination rules, but dependent languages are used to do
mathematics and the only elimination rule a mathematican would want on an
inductive type is the most powerful one: an induction principle. In substance
the induction principle states that, for any predicate |P : (i : Code X) (x :
Code (μ ρ i)) → Set|, if given that the predicate holds for every subnode we
can show it hold for the node itself, then we can show the predicate to hold
for every possible node.

Let us formalize that a bit. We define a predicate |all| stating that a property
hold for all subnodes.

\ExecuteMetaData[ornaments/induction.tex]{all}

Given that we can state the induction principle.

\ExecuteMetaData[ornaments/induction.tex]{induction}

We used the helper |every| which explains how to construct a proof of |all| for
|⟦ ρ ⟧ F| if we can prove the predicate for |F|.

\ExecuteMetaData[ornaments/induction.tex]{every}

Note that we could have derived the other elimination rules from this induction
principle, but cata-- and paramorphisms are very useful non--dependent special
cases that diserve to be treated separately and possibly optimized.
Non-dependent functions still have a place of choice in dependent languages:
just because we can replace every implication by universal quantification
does not mean we should.

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Ornaments}
\subsection{Fancy Data}

%{
%format list = "\DATA{list}"
%format vec = "\DATA{vec}"
%format nil = "\CON{nil}"
%format cons = "\CON{cons}"
%format zip = "\FCT{zip}"
%format zip' = "\FCT{zip}"

A major use for indexes in type families is to refine a type to contain
computational relevant information about objects of that type. Suppose we have
a type of lists.

\begin{code}
data list (X : Set) : Set where
  nil : list X
  cons : X → list X → list X
\end{code}

We may want to define a function |zip : list X → list Y → list (X × Y)| pairing
up the items of two arguments.

\begin{code}
zip' : {-<-}∀ {X Y} →{->-}list X → list Y → list (X × Y)
zip' nil          nil          = nil
zip' (cons x xs)  (cons y ys)  = cons (x , y) (zip' xs ys)
zip' (cons x xs)  nil          = ?
zip' nil          (cons y ys)  = ?
\end{code}

It is clear that there is nothing really sensible to do for the two last cases.
We should signal some incompatibility by throwing an exception or we may just
return an empty list. But this is not very principled. What we would like is to
enforce on the type level that the two arguments have the same length and that
we additionally will return a list of that exact length. This type is called |vec|.

\begin{code}
data vec (X : Set) : ℕ → Set where
  nil : vec X zero
  cons : ∀ {n} → X → vec X n → vec X (suc n)
\end{code}

We wrote the constructors such that they maintain the invariant that |vec X n|
is only inhabited by sequences of length |n|. We may now write the stronger
version of |zip| which explicitely states what is possible to zip.
\begin{code}
zip : {-<-}{X Y : Set} {n : ℕ} → {->-}vec X n → vec Y n → vec (X × Y) n
zip nil          nil          = nil
zip (cons x xs)  (cons y ys)  = cons (x , y) (zip xs ys)
\end{code}

This is made possible because of the power dependent pattern matching has:
knowing a value is of a particular constructor may add constraints to the type
of the expression we have to produce and to the type of other arguments. As
such when we pattern match with |cons| on the first argument, the implicit
index |n| gets unified with |suc m|, which implies that the second argument has
no choice but to be a |cons| too.

Several comments can be made about |vec| and |list|. The first one is that they
are almost same. More precisely, they have the same shape, the only added
argument is the natural number |n| in |cons| for |vec|\footnote{Actually this
|n| does not contain any information as it can be derived from the type index.
As such there is ongoing research to optimize away these kind of arguments and
we will see that because of our index--first formalism of indexed datatypes it
will not even be added in the first hand.}. Because only a sprinkle of
information has been added to something of the same shape, we should be able to
derive a function from |vec X n| to |list X|. The second comment is that there
is an straightforward isomorphism between |list X| and |Σ ℕ (vec X)|. As such
we should be able to come up with the reverse function |(x : list X) → vec X
(length x)|.

The rest of this section will be dedicated to formalizing prose definitions
such as ``vectors are lists indexed by their length'' and generically deriving
the properties that they imply.
%}

\subsection{Reindexing}
Another take on the previous example of lists and vectors is that vectors have
a more informative index (natural numbers) than lists (trivial indexation by
the unit type). This can be expressed by the fact that there is a function |ℕ →
⊤| giving a non-fancy index given a fancy one. Because we work with
inductive--recursive types and not just inductive ones, we have two
indexes---the input index $\DATA{I} : \DATA{Set}$ and the output index
$\DATA{X} : \DATA{I} → \DATA{Set}$---and we have to translate this notion. For
this we introduce the datatype |PRef| (index refinement using powersets).

\ExecuteMetaData[ornaments/pow.tex]{pref}

Let |X : ISet α₀ β₀| and |R : PRef α₁ β₁ X|. |Code R| represents the new input
index, together with the striping function |down R| taking new input indexes to
old ones. Additionaly we have to define a new output index |Y : Code R → Set|
such that we can derive a stripping function |(j : Code R) → Y j → X (down j)|.
Directly defining |Y| together with this second striping function would not
have been practical\footnote{Later we would have needed to define preimages
which necessarily embed some notion of equality. As explained in
\ref{sec:index-first} we want to avoid any mention of equality when formalizing
the unrelated matters of data types.}. Thus instead of the stripping function,
we ask for its fibers (called its graph), given by |decode R|. This reversal is
the classical choice between families |(A : Set) × A → X| and powersets |X →
Set| to represent indexation.

Because of the small fiber twist we operated, we have a bit of work to get the
new indexing pair (in |ISet|) from a |PRef|.

\ExecuteMetaData[ornaments/pow.tex]{pfam}

In substance, the new output index is simply the old one to which we add some
information that can depend on it. The stripping function is thus simply the
projection |π₀|.

\subsection{A Universe of Ornaments}

Step by step, following the construction of induction--recursion, we will start
by describing ornaments of |poly|, the inductive part of the definition. For |R
: PRef α₁ β₁ X| and |ρ : poly γ₀ X| we define a universe of decriptions |orn₀ γ
R ρ : Set _|. Simultaneously we define an interpretation |⌊ o ⌋₀ : poly (γ₀ ⊔
γ₁) (PFam R)| taking the description of the ``delta'' to the actual fancy
description it represents, and a stripping function |info↓ : info ⌊ o ⌋₀ → info
ρ| taking new node informations to old ones.

\ExecuteMetaData[ornaments/orn.tex]{code-def}
\ExecuteMetaData[ornaments/orn.tex]{code-impl}
\ExecuteMetaData[ornaments/orn.tex]{p-interp}
\ExecuteMetaData[ornaments/orn.tex]{infodown-impl}

Lets break down the constructors. First we have the constructors that look like
|poly|: |ι|, |κ|, |σ| and |π|. They essentially say that nothing is changed. |ι
j| ornaments |poly| of the form |ι i| where |down R j ≡ i| \textit{ie} we
replace inductive positions by a fancy index such that the stripping matches.
|σ A B| has to use the interpretation |⌊_⌋₀| and |info↓| to express how the
family |B| depends on the info of |A|. |κ| and |σ B| change nothing and as such
some of their arguments are implicit because there is no choice possible.

The next 3 constructors allow to change things. |add₀| allows to delay the
ornamenting, it interprets into a |σ| where the first component has no
counterpart in the initial data. In other words we add a new argument to the
constructor and then give an ornament which might depend on it. |add₁| is the
other way around, it gives an ornament and then adds new arguments which might
depend on it. And finally |del-κ| allows you to erase a constant argument given
that you can provide an element of it. It is restricted to delete only
constants because for an inductive position it is not really clear what the
notion of ``element of it'' is.

|⌊_⌋₀| and |info↓| are straightforward, the first 4 constructors are
unsurprising, the additions interpret into sigmas where |info↓| ignores the new
component and the deletion interprets into a trivial constant, |info↓| giving
back the element we have provided in the definition.

As for inductive--recursive types in this part of the construction we are not
yet taking input indexes into account so we can't give the ornament of lists
into vectors yet. But we can give the ornament of natural numbers into lists:
we identify |zero| with |nil| and |suc| with |cons| where |cons| demands an
additional constant argument in addition to the recursive position.

%{
%format ℕ-tag = "\DATA{ℕ\!\!-\!\!tag}"
%format `ze = "\CON{`ze}"
%format `su = "\CON{`su}"
%format nat-c = "\VAR{nat\!\!-\!\!c}"
%format list-R = "\VAR{list\!\!-\!\!R}"
%format list-o = "\VAR{list\!\!-\!\!o}"
\begin{code}
data ℕ-tag : Set where `ze `su : ℕ-tag

nat-c : poly lzero (⊤{-<-}{lzero}{->-} , λ _ → ⊤{-<-}{lzero}{->-})
nat-c = σ (κ ℕ-tag) λ {
  (lift `ze) → κ ⊤  ;
  (lift `su) → ι *  }

list-R : PRef lzero lzero (⊤{-<-}{lzero}{->-} , λ _ → ⊤{-<-}{lzero}{->-})
Code list-R = ⊤{-<-}{lzero}{->-}
down list-R _ = *
decode list-R _ _ = ⊤{-<-}{lzero}{->-}

list-o : (X : Set) → orn₀ lzero list-R nat-c
list-o X = σ κ λ {
  (lift (lift `ze)) → κ                     ;
  (lift (lift `su)) → add₀ (κ X) λ _ → ι *  }
\end{code}

We define the type |orn γ₁ R S ρ : Set| ornamenting |ρ : IIR γ₀ X Y|.

\ExecuteMetaData[ornaments/orn.tex]{orn}

|node| is not surprising, for every fancy input index we give an ornament of
the description with the corresponding old index. The |emit| function starts
off like the one for |IIR|, taking an input index and the info, here of the
interpretation of the ornament. Having that, we can already compute the old
decoding using |info↓| and |emit ρ (down R j)|. We thus require to generate an
output index compatible with the old output index we have derived.

We eventually reach the full interpretation |⌊_⌋| taking an ornament to a fancy
|IIR|.


\ExecuteMetaData[ornaments/orn.tex]{interp}


\subsection{Ornamental Algebra}

Recalling the first remark we made on the relation between an ornamented data
type and its original version, we want to generically derive an arrow mapping
the new fancy one to the old one. Note that I did write arrow and not simply
function: because we work in the category of indexed type families we do not
simply want a map from new inductive nodes to old ones, we want it to assign
output indexes consistently with the reindexing. The function we want to write
has the following type.

\begin{code}
forget : {-<-}∀ {α₀ β₀ α₁ β₁ γ₀ γ₁}{X : ISet α₀ β₀}{R : PRef α₁ β₁ X}{ρ : IIR γ₀ X X}{->-}(o : orn γ₁ R R ρ){s} → π₀< (μ ⌊ o ⌋ {-<-}{s}{->-}) ⇒ (μ ρ{-<-}{s}{->-} ∘ down R)
forget = ?
\end{code}

Because of some complications I didn't manage to implement it, but I am
convinced that the missing parts are not very consequent. Indeed for inductive
types, the proof is done by a fold, on the ornamental algebra |⟦ ⌊ o ⌋ ⟧ (F ∘
down R) ⇒ (⟦ ρ ⟧ F ∘ down R)|. The complication for induction--recursion is
that this arrow cannot exist since because of the output index the two objects
do not live in the same category and |F ∘ down R| is not a valid argument to |⟦
⌊ o ⌋ ⟧|.

Some analysis has shown that in fact |fold| is not powerful enough to express
|forget| and we need to resort to a paramorphism. To provide some intuition
lets break down |forget|. It has to turn an instance of a fancy datatype into
the base one. Naturally it will proceed by structural recursion, simplifying
the structure bottom up. This is what the ornamental algebra |erase : ⟦ ⌊ o ⌋ ⟧
(F ∘ down R) ⇒ (μ ρ ∘ down R)| should implement: given a node where every
subnode already has been simplified, simplify the current node. The reason why
this halfway simplified data structure cannot exist (signified by the type
mismatch of the object fed to the functor) is that this object |F ∘ down R|
does not contain enough information. In a fancy |σ A B| node, |A| might contain
inductive positions, such that the family |B| may depend on their (fancy)
output index, something we cannot get because being a subnode, |A| has already
been replaced by a simplified version that no longer contains this fancy output
index. As such, while simplifying the datastructure, we need to keep track not
only of simplified subnodes, but also of their original version, to be able to
simplify the current node. This makes explicit the need for paramorphisms.

Note that a finer approach would be not to resort to fully featured
paramorphisms. Indeed, to simplify a node we do not need the full couple of the
simplification and the fancy subnodes, we just need to reconstruct the fancy
output index and we already have the simplified subnode. Thus what we exactely
need is the information that is in the fancy node that isn't in the simplified
one. While seemingly tortuous, this notion is very familiar and we call it a
\textit{reornament}. Indeed we have seen that lists are an ornament of natural
numbers and vectors are lists indexed by natural number. Then what is a vector
if it is not \textit{all the information that is in a list but not in its
length}? This builds up a nice transition because reornaments will arise in the
next subsection. This last remark that the construction of the forgetful map
depends on the prior formalization of reornaments is a small funny discovery
because the notion had previously been presented only afterwards. It is indeed
not excluded that the two construction actually depend on each other and must
be constructed simultaneously.

\subsection{Algebraic Ornaments}

Lets focus on the second remark we stated on the relationship between lists and
vectors: the isomorphism between |list| and |Σ ℕ vec|. More precisely to for
each |xs : list| we can naturally associate |xs' : vec (length xs)|. |length|
is no stranger, it is a very simple fold, \textit{eg} the underlying core is an
algebra |⟦ list-c ⟧ ℕ ⇒ ℕ|. A natural generalization follows in which for a
given algebra |⟦ ρ ⟧ X ⇒ X| we create an ornament indexing elements of |μ ρ| by
the result of their fold. This is what we call an algebraic ornament.

In the theory of ornaments on inductive definitions there is only one index,
the input index. But since we now also have an output index we might ask wether
we want to algebraically ornament on the input or the output. In the case of
the length algebra of lists, the input algebraic ornament gives rise to
vectors, whereas the output algebraic ornament gives rise to an
inductive--recursive definition where the inductive part is still list and the
recursive part is the length function. As such, it seems to be a waste of power
to redefine lists inductive--recursively with their length if we already
separately have defined lists and the length algebra, from which we can derive
|length| with the generic fold. We will thus only present input algebraic
ornaments.

First lets define the reindexing. We suppose the indexes of our data type are
|X : ISet α₀ β₀| and the carrier of our algebra is |F : 𝔽 α₁ X|.

\ExecuteMetaData[ornaments/orn.tex]{algR}

This definition simply extends the input index by an inductive element of the
carrier, \textit{eg} the specification of what output we want for the fold.
Note that we also add something to the output index, namely a proof that the
recursive part of the carrier matches the original output index. This is not
just a \textit{by--the--way} property, it is provable but also a crucial lemma
for the construction.

As usual now we first give the pre--ornament |orn₀| for a |poly|, which we will
expand in a second step to full ornaments on |IIR|.

\ExecuteMetaData[ornaments/orn.tex]{algorn0}

Note that the two last parts of the type are similar to an arrow between on
|Fam|. I didn't look deeply into that but it seems like this is some sort of
arrow family from |⟦ ρ ⟧₀ F| to |(orn₀ (γ₀ ⊔ α₁) (AlgR F) ρ , λ o → (y : info ⌊
o ⌋₀) → info↓ y)|.

More importantly, |F| is still the carrier of the algebra and we recursively
construct an ornament whose |info↓| matches with the output of |⟦ ρ ⟧₀ F|. This
ensures that we propagate good shape constraints throughout the structure,
ensuring that we indeed constrain the node shapes to fold to a given target.
Before proceeding with the full definition we introduce the type of fibers for a
function\footnote{The careful reader will be puzzled by the fact that I
previously said wanting to avoid fibers and any mentionning of equality. But
here there is no way around and we really want this fiber. As a consolation we
can argue that this is no longer part of our \textit{core theory of datatypes}
and sidesteps are thus less consequential.}.

\ExecuteMetaData[ornaments/prelude.tex]{inv}

Now we have the building blocks for the final definition.

\ExecuteMetaData[ornaments/orn.tex]{algorn}

The type is straightforward but an interesting fact is that we do not directly
delegate the implementation of |node| to |algorn₀|. Indeed we have to come up
with an element |x : Code (⟦ ρ ⟧₀ F)|. The explaination for this is that unlike
our list and vector example, not every algebraic ornament has a single choice
for a given index: there might still be several possible choices of
constructors that will have a given fold value. We can't (and shouldn't) make
that choice so we have to ask it beforehand. This choice then uniquely
determines the shape of the ornament which we can unroll by a call to
|algorn₀|. The |emit| part simply fulfills the proof obligation that we added
in the output index.

The next step is to provide the injection from simple data into the new data
indexed by the value of its fold. Again I didn't fully finish this part because
the proof is tremendously hairy. The proof is done by induction, but it is
completely unscrutinable. Since we are working not on native Agda
datatypes but on our constructed versions, we cannot use native pattern
matching and recursion but have to call our generic induction principle. It's
not that there is much choice on what to do, but simply that because of all the
highly generic objects in use, Agda has a hard time helping us out and
expanding the the right definitions just as much as we want. All in all this
leads to huge theorem statements from which it is hard to tell apart the head
and the tail. The beginning goes as follows.

\ExecuteMetaData[ornaments/orn.tex]{algorn-inj}

We have now finished all our constructions. To familiarize themselves further
with them, the reader might continue with the case study in appendix
\ref{sec:stlc}, studying an example formalization of simply--typed λ→ calculus.

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discussion}

\subsection{Index-First Datatypes and a Principled Treatment of Equality}
\label{sec:index-first}

Intuitionistic Type Theory has long realised the unsufficient study of the
equality type, streched between a convenient extensional equality and
complicated computational interpretation. Already in 2007, T. Altenkirch and C.
McBride presented Observation Type Theory (\cite{altenkirch06}) which suggests
an alternative to inductive propositional equality, which can be related to the
non--higher--order fragment of the newer Homotopy Type
Theory\footnote{Amusingly \textit{OTT} is \textit{HoTT} without the
\textit{H}.} by V. Voevodsky (\cite{voevodsky10}).


The inductive definition of propositional equality is deceptive on several
matters. First it pollutes the formalization of datatypes, a matter which has
no reason not to be orthogonal to equality. More than that, because we had no
compelling alternative, the fantastic index--first presentation of datatypes
with pattern matching on the index has been left behind. Indeed index--first
presentation religously follows the bidirectional philosophy, ensuring that
there cannot be several converging information flows triggering local
definitional equality between expressions. This rules out every equality--like
definition (like our definition of fiber) whose use is to pattern match on the
proof to locally unify terms.

Regarding pattern matching on the index, from a very practical point of view it
is reassuring that most types encountered in formal developments are not
equality--like. When we do make use of input indexes depending on constructor
argument, most of the time these arguments are marked implicit and this is the
symptom of a hidden pattern matching: the two information flows do not really
collide since we delegate one of the sides to the implicits--solving machinery.
It is thus explicit that the only information flow indeed comes from the index,
confirming its qualification as an \textit{input} index. Acknowledging that
internally in the language construction would mean cheap eradication of a big
source of inefficiency that has already been investigated (E. Brady et al, \cite{brady03}).

Homotopy Type Theory seems to be where most of the research on equality is
currently at, already with several experimental implementation namely one for
Agda.  Because of this promising ongoing research, now seems the good time to
build tools that will enable the datatype theory to smoothly adapt to any new
development of equality.

\subsection{Further Work}

I hit the surprising obstactle of |forget| not being a catamorphism quite late
in the internship and as such, the study on paramorphisms is incomplete. The
question of non--dependent elimination rules be further investigated.

In the same veine, the story for algebraic ornaments is missing a finishing
touch. Given that we have formalized paramorphisms, there is a natural
generalization from algebraic ornaments to paramorphic ornaments, possibly
deriving the injection function for a wider array of ornaments. Additionally,
it is unsatisfactory that reornaments are not yet able to make use of
pattern--matching on the index to drive away more equality proofs (by
eliminating contradictory information sources). Indeed in a reornament, we
know the code of the index (which is the first in the sequence of the 3) and
the |erase| algebra gives us the raw expression of the fold.

When we start to have first--class description of datatypes, a new world is
open for exploration. G. Allais et al (\cite{allais18}) have characterised the
datatypes behaving like simply--typed syntaxes with binders. We might ask how
it fits with this development. What is the best way for a language to expose
primitive for syntax reflection, tying together the internal description of
datatypes with their native counter--part?

Induction--recursion has recently been generalized even further than indexation
by N. Ghani et al \cite{ghani13} in the form of induction--recursion for
arbitrary fibers. Fibers are a category theory notion giving a general account
of indexation. Indexed induction--recursion arises as a special case, but also
setoid induction--recursion or category with families\footnote{A model of type
theories introduced by A. Setzer.} induction--recursion (allowing one
to define a universe equiped with a notion of substitution). This seems like an
interesting step forward since by allowing one to explicitely state which
\textit{more specific than the most generic} notion of indexation we want, it
degenerates gracefully (even to basic inductive types) with no need for the
trivial indexation trick that we have used.

The last attack surface I can suggest is to work to achieving perhaps a more
principled set of operations for the universe of ornaments as we have seen that
they do not always mesh up very well and leave some trivial artifacts hanging
when they are interpreted. A related question but which should not be taken as
a reliable solution for the previous issue is the reorganization of
datastructures, otherwise said the optimization of descriptions. Although this
last project can probably only be effectively implemented in a language
typechecker or depends on good reflection primitives.


%%%%%%%%%%%%%%%%%%%%%%%%%%%
\appendix
\section{Bibliography}
\bibliographystyle{plain}
\bibliography{ornaments.bib}

\section{Introduction to Agda}
\label{sec:agda}

%{

Good introductory material is available
online\footnote{\url{http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf}
(U. Norell and J. Chapman)}. We present here a speed--run through it.

\subsection{Syntax and concepts}
Data types are introduced using the |data| keyword. Types are written in
\blueFG{blue} and constructors in \redFG{red}.

%format bool = "\DATA{bool}"
%format true = "\CON{true}"
%format false = "\CON{false}"

\begin{code}
data bool : Set where
  true : bool
  false : bool
\end{code}

|Set| is the type of small types. There is a hierarchy of types |Set : Set₁|,
|Set₁ : Set₂| and so one. More on that later.

Total functions can be defined by pattern matching in a similar way to haskell by
specifying several independent clauses. We write them in in \greenFG{green}.

%format not = "\FCT{not}"
%format && = "\FCT{\&\&}"
%format _&&_ = _ "\!" && "\!" _
%format if = "\FCT{if}"
%format then = "\FCT{then}"
%format else = "\FCT{else}"
%format if_then_else_ = if _ then _ else _
%format A = "\DATA{A}"

\begin{code}
not : bool → bool
not true = false
not false = true

_&&_ : bool → bool → bool
true   && true   = true
true   && false  = false
false  && true   = false
false  && false  = false

if_then_else_ : {A : Set} → bool → A → A → A
if true   then a else b = a
if false  then a else b = b
\end{code}

As we can see above, Agda has a powerful way of specifying mixfix operators,
where arguments might be placed in order in place of underscores in the
identifier. In other words, |x && y| is a shorthand for |_&&_ x y|. In fact
almost every unicode character is valid in an identifier (apart from
parenthesis, braces, dots, semicolons and at). The downside is that
 is a valid identifier and as such tokens must be separated by
spaces.

Function expressions are introduced by the |λ| keyword: |λ x → x|. They can
take several (curried) argument |λ x y → y| and can perform pattern matching
when enclosed in braces: |λ { true → false; false → true }|.

Recursion, self or mutual does not have to be declared, the only requirement is
scoping: an implementation has to follow (anywhere after) any declaration and
for every identifier used, its declaration must preceed.

%format nat = "\DATA{nat}"
%format zero = "\CON{zero}"
%format suc = "\CON{suc}"
%format even = "\FCT{even}"
%format odd = "\FCT{odd}"
\begin{code}
data nat : Set where
  zero : nat
  suc : nat → nat

even : nat → bool
odd : nat → bool

even zero = true
even (suc n) = odd n

odd zero = false
odd (suc n) = even n
\end{code}

%format B = "\DATA{B}"
The dependent function type is written |(x : A) → B| where |B| may mention |x|.

%format id = "\FCT{id}"
%format id' = "\FCT{id′}"

\begin{code}
id : {A : Set} → A → A
id x = x
\end{code}

%format Y = "\DATA{Y}"

As shown, implicit argument are marked by curly braces, we are not required to
pass them when calling or defining the function and they will be solved by
unification (not search). The |∀| symbol is a helper when we want to make the
range of an argument implicit: we could have written |id : ∀ {A} → A → A|. Note
that this also works with explicit arguments like |id' : ∀ A → A → A|. We may
drop arrows for dependent type: |(X : Set)(Y : Set) → X → Y| is a
shorthand for |(X : Set) → (Y : Set) → X → Y|. We can resort to
unification on explicit arguments by using an underscore in place of the
argument, \textit{eg} |id' _ x|.

Records are introduced by the |record| and |field| keywords. We write projectors
in \orangeFG{orange}.

\begin{spec}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    π₀ : A
    π₁ : B π₀
open Σ
\end{spec}

%format Σ.π₀ = "\PRO{Σ.π₀}"
%format Σ.π₁ = "\PRO{Σ.π₁}"

The last line brings into scope the projectors |π₀ : ∀ {A B} → Σ A B → A| and
|π₁ : ∀ {A B} (p : Σ A B) → B (π₀ p)|. Before that we would have referred to
them as |Σ.π₀| and |Σ.π₁|. To construct an element there are 3 methods: using
the defined constructor |x , y|, using generic record notation |record { π₀ =
x; π₁ = y}| or by using copatterns (the preferred method, especially for the
functions returning records):

\begin{spec}
p : Σ A B
π₀ p = foo
π₁ p = bar
\end{spec}

\subsection{Universe Levels}
\ref{sec:levels}

As explained previously, Agda has a tower of universes. The first ones have
names like |Set₂| but we can access any one by using levels (which are natural
numbers where the constructors are axioms to disable pattern matching). The
zero level is |lzero| and the sucessor is |lsuc|. We also have access to a max
function |_⊔_ : Level → Level → Level|. We can write
\textit{level--polymorphic} functions.

\begin{code}
id' : {α : Level} {X : Set α} → X → X
id' x = x
\end{code}

The tower of universes is not cumulative, if |X : Set α|, then we |X : Set
(lsuc α)| is not true. This is particularly painful as it adds a lot of noise: to embed a small set into a higher one we have to resort to a record (or a datatype) as they can be given any level which is high enough.

\ExecuteMetaData[ornaments/prelude.tex]{lift}

In the report i have hidden most prenex implicit arguments from function (using
a mix of an existing feature resembling Coq's \textit{Variable} and pure
typographic hacks) as these are mostly related to level polymorphism
bookkeeping. You should try to mentally remove every occurence of |Lift|,
|lift|, |lower| and of level variables (to which I reserved the first 4 greek
letters). \textit{Ie} instead of |∀ {α β} → Set α → Set β → Set (α ⊔ β)| I
might write |Set α → Set β → Set _|.

\subsection{Prelude}
We will briefly introduce the most important utility definitions we will use
throughout the report.

We already have seen the |Σ A B| type with projectors |π₀| and |π₁|. Its
non--dependent counterpart is |_×_ : Set α → Set β → Set _|.

Level polymorphic empty and unit types:
\ExecuteMetaData[ornaments/prelude.tex]{prop}

Dependent function composition is written |g ∘ f| and dependent application is
|f $ x|. I use this last definition a lot to escape a parenthesis hell.

Heterogeneous inductive equality is defined by:
\ExecuteMetaData[ornaments/prelude.tex]{equality}

We will use the usual lemmas |subst : (P : A → Set β) → x ≡ y → P x → P y|,
|cong : (f : (x : A) → B x) → x ≡ y → f x ≡ f y|, |trans : x ≡ y → y ≡ z → x ≡
z| and |sym : x ≡ y → y ≡ x|. Also their two argument version |subst₂ : (P : (a
: A) → B a → Set γ) → x₀ ≡ x₁ → y₀ ≡ y₁ → P x₀ y₀ → P x₁ y₁|, |cong₂ :
{-"\dots"-}| and |cong-Σ : π₀ p ≡ π₀ q → π₁ p ≡ π₁ q → p ≡ q|. We also make use of a postulated function extensionality:

\ExecuteMetaData[ornaments/prelude.tex]{funext}

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Case Study: Bidirectional Simply-Typed Lambda Calculus}
\label{sec:stlc}

As an application of the theories that we constructed, we will present in this
section a formalization of the bidirectional simply-typed λ→ calculus. This
will also provide a nice spot to take some time to motivate and explain
bidirectional typing.

\subsection{Bidirectional Typing}
Bidirectional typing has been devised by B. Pierce and D. Turner
(\cite{pierce00}) as a particular school of formalizing typing rules.
Bidirectional typing has been particularly successful in taking over
formalization but most importantly implementation of typecheckers for complex
languages like dependent or substructural theories such as Agda itself or
Idris. A motivation is the shortcoming of the Hindley--Milner algorithm for
type inferance: in these theories a most generic type is usually not computable
or may not even exist, yet we would like to avoid the necessity of annotating
every single expression. Thus it arises with the need for a finer understanding
of where type annotations are definitely not need and where they are, in the
absence of an inferance engine.

%{
%format ⊢ = "\DATA{⊢}"
%format ∈ = "\DATA{∈}"
%format ∋ = "\DATA{∋}"
%format <: = "\DATA{<\!:}"
%format lookup = "\FCT{lookup}"

Bidirectional typing emphasises the flow of information. One way to view a
typechecker is as a server, responding to judgment queries either directly by a
final answer or by a query itself, some sort of challenge. For example to the
query ``Does this variable |x| check to type |T| in context |Γ|?'' a
typechecker might offer responses such as ``Yes, because |lookup Γ x ≡ T|.'',
``Give me a proof that |U| is a type, |U <: T| and |x : U|.''. In these
dialogs, we refer to input judgments as judgments implied by the hypothesis
that the query is well-formed. A client might better be convinced that |T| is a
valid type when asking if |x : T| holds because the server will assume it. On
the other hand, if the query is ``What type has |x|?'' then if given the answer
|T|, the client can rightly assume that |T| is a valid type.

Precising things a bit we introduce not one but two typing judgement, with the
information flow from left to right. |Γ ⊢ x ∈ T| represents the query ``What is
the type |T| that |x| has?'' and |Γ ⊢ T ∋ x| represents ``Does |x| have type
|T|''. The first mode of operation is called \textit{synthesis}, with a |⊤| as
input and a type as output and the second is called \textit{checking}, with a
type as input and |⊤| as output.

%}

\subsection{Native Agda}

Before formalizing it with our encoding, we start of by giving the construction
as we would normally in Agda. Let us start off by some tools. First natural
numbers and finite sets.

\ExecuteMetaData[ornaments/examples/lambda2.tex]{nat}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{fin}

Then contexts, also known as snoc--lists, together with a length, indexation
and lookup.
\ExecuteMetaData[ornaments/examples/lambda2.tex]{bwd}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{length}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{idx}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{get}

The first judgements are |type| and |env|, giving the sets of types and valid
contexts.
\ExecuteMetaData[ornaments/examples/lambda2.tex]{type}

Know we can give the typing judgements. We will represent it by an indexed
inductive--recursive type with as input index a context, a direction (synthesis
or checking) and the associated input (|type| or |⊤|, depending on the
direction) and as output index the associated output (again |type| or |⊤|).

\ExecuteMetaData[ornaments/examples/lambda2.tex]{dir}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{IN}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{OUT}

%{
%format aux = "\DATA{aux}"
%format app = "\CON{app}"
\begin{code}
{-<-}
open import ornaments.examples.lambda2
{->-}
data tlam₀ (Γ : env) : (d : dir) (i : IN d) → Set
out₀ : ∀ {Γ d i} → tlam₀ Γ d i → OUT d

aux : env → type → Set
aux Γ `base    = ⊥ {lzero}
aux Γ (r `⇒ s) = tlam₀ Γ chk r

data tlam₀ Γ where
  lam : ∀ {r s} → tlam₀ (Γ ,, r) chk s            → tlam₀ Γ chk (r `⇒ s)
  vrf : ∀ {r} (e : tlam₀ Γ syn *) → out₀ e ≡ r    → tlam₀ Γ chk r
  var : idx Γ                                     → tlam₀ Γ syn *
  app : (f : tlam₀ Γ syn *) (x : aux Γ (out₀ f))  → tlam₀ Γ syn *
  ann : ∀ {r} → tlam₀ Γ chk r                     → tlam₀ Γ syn *

out₀ {Γ} {chk} {i} _            = *
out₀ {Γ} {syn} {*} (var i)      = get Γ i
out₀ {Γ} {syn} {*} (app f x)    with out₀ f  | x
...                             | `base      | ()
...                             | r `⇒ s     | _ = s
out₀ {Γ} {syn} {*} (ann {r} _)  = r
\end{code}
%}

Let us make sense from this mess! Looking at the constructors, we have the usual
|lam|, |var| and |app|. The constructor |lam| is in checking mode (it builds up
larger types using small parts of given information) and the two destructors
|var| and |app| (|var| can be interpreted as a destructor for the binding,
|app| for the function themselves) are in synthesis mode as they take big
arguments containing lots of information and represent smaller terms
constrained by them.

There is a little trick in the type of |app|, indeed it is key to have the
function argument |f| in synthesis mode, yet we want to \textit{panic} when |f|
does not synthetise a function type. For that we simply build a little helper
that will match on the type and demand an element of the empty type when the
type is |`base|. This way we are sure that no such element will be
constructible.

The output function is trivial in the checking mode and shouldn't be
challenging in the synthesis mode. We crucially make use of Agda's
\textit{|with|--abstraction}, a feature ressembling a case expression performed
left of the clause equation (which do not exist natively in Agda).

\subsection{Well--Scoped Terms}

We do not want to directly jump to encoding this syntax of λ→ calculus because
the funny part is that we will express it as an ornament on well--scoped
syntax. Well--scoped syntax is expressed as an |IIR| definition with natural
numbers as input index (the number of free variables) and a trivial output
index.

\ExecuteMetaData[ornaments/examples/lambda2.tex]{ulam-ix}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{ulam-c}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{ulam}

There is one surprise: the |`wrap| constructor, that---as its name hints---does
nothing really interesting, just adding a constructor layer for the sake of it.
It is only here as an artifact of my definition of the universe of ornaments
but I am not sure it could have been avoided. For now we can ignore it, the
reason will appear in the following section.

\subsection{Well--Typed Terms}

First we give the reindexation and the constructor tags, the new indexes being
as we have seen for |tlam₀| and the stripping function being the length of the
context.

\ExecuteMetaData[ornaments/examples/lambda2.tex]{tlam-ix}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{tlam-tags}

First let us look at the inductive part of the encoding.

\ExecuteMetaData[ornaments/examples/lambda2.tex]{tlam-node}

The first comment is probably that this is a bit clumsy. We could've written
special |syntax| rules to ease the programming with the encoding and the choice
of operation for ornaments is not set in stone, it may be later changed to
another combination.

We can note that we pattern match on the index, \textit{eg} before giving the
shape of the datatype (in this case the ornament). This is the full power of
index--first datatypes unleashed, as such we have constructors that do not have
any of the implicit quantification like in native Agda.

A pattern we notice is |add₀ (κ {-"…"-}) λ { (lift {-"…"-}) →
σ (del-κ {-"…"-}) {-"…"-} }|. The high--level operation going
on here is the replacement of some constant by another one (given a stripping
function which is implicit here). We might want to add special syntax for that.

Now it is clear what |`wrap| stood for: the ornament introduces new
constructors |`vrf| and |`ann| that do not exist in the original datatype.
Without |`wrap| we wouldn't know what constructor to choose from in the old
datatype. Note that this is an artifact in the sense that it might be
avoidable. Indeed these added constructors do not really change the shape from
untyped λ→ (without wrap), as they just add a \textit{transparent} layer that
we could very much erase systematically. It thus simply a matter of getting the
axiom right and adding it as a constructor to |orn₀|.

Finishing with the unsurprising recursive part and the fixed--point:

\ExecuteMetaData[ornaments/examples/lambda2.tex]{tlam-emit}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{tlam}
\ExecuteMetaData[ornaments/examples/lambda2.tex]{out}

We are now done! In the end the encoding has gone well but it stressed the need
for syntactic sugar and it raised the issue of wrapper--like constructors that
we should be allowed to add when ornamenting.
\end{document}
