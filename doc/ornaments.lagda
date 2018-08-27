\documentclass[11pt,english]{article}

\usepackage{babel}
\usepackage{catchfilebetweentags}
\usepackage{natbib}
\usepackage{amsmath}
\usepackage{prftree}

%include agda.fmt
%include ornaments.fmt

\title{Ornamenting Inductive-Recursive Definitions}
\author{Peio Borthelle, Conor McBride}


\newcommand{\Hom}{\operatorname{hom}}
\newcommand{\Ob}{\operatorname{ob}}
\newcommand{\CSet}{\mathbf{Set}}
\newcommand{\todo}[1]{\textbf{TODO:}\textit{#1}}
\setlength\parindent{.7em}

\begin{document}

\maketitle


%%%%%%%%%%%%%%%%%%%%%%%%%%

\newpage
\paragraph{Abstract}

\hrulefill

\tableofcontents

%%%%%%%%%%%%%%%%%%%%%%%%%%
\newpage
\section{Introduction}
\label{sec:intro}

\paragraph{A Technical Preliminary} This research development has been
exclusively done formally, using the dependently--typed language Agda
(\cite{agda}) as an interactive theorem--prover. As such this report is full of
code snippets, following the methodology of literate programming
(\cite{knuth84}). Theorems are presented as type declaration, proofs are
implementations of such declarations and definitions are usually some kind of
datastructure introduction: it definitely lies on the \textit{program} side of
the Curry--Howard correspondance. The syntax and concepts of Agda should not be
too alien to a Haskell or Coq programmer but it might be interesting to start
out by reading the appendix \ref{sec:agda} which presents its most important
features.

\paragraph{Motivations} Although they were probably first intended as theorem
provers, dependently--typed languages are currently evolving into
general--purpose programming languages, leveraging their expressivity to enable
correct--by--construction type--driven programming. But without the right tools
this new power is unmanageable. One issues is the need to prove over and over
again the same properties for similar datastructures. Ornaments (\todo{ref
mcbride}) tacle this problem by giving a formal syntax to describe how
datastructures might be \textit{similar}. Using these objects, we can prove
generic theorems once and for all. The broad idea behind this approach is to
``speak in a more intelligible way to the computer'': if instead of giving a
concrete declarations we gave defining properties, we would be able to
systematically collect free theorems which hold by (some high level)
definition.

The present work aims to generalize ornaments to the widest possible notion of
datatypes: inductive--recursive families (or indexed inductive--recursive
types) as recently axiomatized by Ghani et al (\ref{ghani17}).

\paragraph{Related Work}

\paragraph{Acknowledgements}


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
Martin Loef's Intuitionistic Type Theory (ITT) such as inductive types
(W--types), inductive families \textit{etc}. This rule has been inspired to
Dybjer (\todo{ref}) by Martin Loef's definition of a universe à--la--Tarski, an
inductive set of codes |data U : Set| and a recursive function |el : U → Set|
reflecting codes into actual sets (here a simple version with only natural
numbers and Π--types).

{-<-}
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

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
generality, indexed induction recursion allows to simultaneously define an
inductive predicate |U : I → Set| and an indexed recursive function |f : (i :
I) → U i → X i| for any |I : Set| and |X : I → Set₁|. Using a vocabulary
influenced by the \textit{bidirectional} paradigm for typing (\todo{ref}) we
will call |i : I| the \textit{input index} and |X i| the \textit{output index}.
Indeed if we think of the judgement |a : U i| as a typechecker would, the
judgment requires the validity of |i : I| and suffices to the validity of |f a
: X i|. We will explore bidirectionality further in section \ref{sec:stlc}.

%}

Induction-recursion is arguably the most powerful set former (currently known)
for ITT. \todo{who?} has shown that its addition gives ITT a proof-theoretic
strength slightly greater than KPM, Kripke--Platek set theory together with a
recursive Mahlo universe. Although its proof-theoretic strength is greater
than $Γ₀$, ITT with induction--recursion is still considered predicative in a
looser constructivist sense: it arguably has bottom--to--top construction.


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
  associative and respects the identity laws
\end{itemize}

A functor |F| between categories |C| and |D| is a mapping of objects |F : C →
D| and a mapping of arrows |F[_] : ∀ {X Y} → X ⇒ F → F X ⇒ F Y|.

%}

\subsection{Data types}

The different notions of data types, by which we mean inductive types,
inductive--recursive types and their indexed variants, share their semantics:
initial algebras of endfunctors. In a first approximation, we can think of an
``initial algebra'' as the categorical notion for the ``least closed set''
(just not only for sets). As such, we will study a certain class of functors
with initial algebras that give rise to our indexed inductive--recursive types.

We shall determine the category our data types live in. The most simple data
types, inductive types, live in the category $\DATA{Set}$.  On the other hand,
as we have seen, inductive--recursive data types are formed by couples in
$(\DATA{U} : \DATA{Set})~×~(\DATA{U} → \DATA{X})$. Categorically, this an
$\DATA{X}$-indexed set and it is an object of the slice category of $\DATA{Set}
/ \DATA{X}$. We will be representing these objects by the record type
|Fam γ X|.

\ExecuteMetaData[ornaments/fam.tex]{fam-def}
\ExecuteMetaData[ornaments/fam.tex]{morph}

Now we can get to indexed inductive--recursive data types which essentially are
functions from an input index $\VAR{i} : \DATA{I}$ to
$(\DATA{X}~\VAR{i})$-indexed sets. We will use couples $(\DATA{I}~,~\DATA{X})$
a lot as they define the input and output indexing sets so we call their type
$\DATA{ISet}$.

\ExecuteMetaData[ornaments/fam.tex]{iset}
\ExecuteMetaData[ornaments/fam.tex]{ifam}
\ExecuteMetaData[ornaments/fam.tex]{ifam-arr}

\subsection{A Universe of Strictly Positive Functors}

Dybjer and Setzer have first presented codes for (indexed) inductive-recursive
definitions (\todo{ref}) by constructing a universe of functors. However, as
conjectured by \cite{ghani17}, this universe lacks closure under composition,
\textit{eg} if given the codes of two functors, we don't know how to construct
a code for the composition of the functors. I will thus use an alternative
universe construction devised by McBride which we call \textit{irish}
induction--recursion\footnote{It has also been called \textit{polynomial}
induction--recursion because it draws similarities to polynomial functors, yet
they are different notions and should not be confused.}.

In this section we fix a given pair of input/output indexes |X Y : ISet α β|
and i will define codes |ρ : IIR δ X Y : Set| for some functors |⟦ ρ ⟧ : 𝔽 γ X → 𝔽
(γ ⊔ δ) Y|.

First we give a datatype of codes that will describe the first component
inductive--recursive functors. This definition is itself inductive--recursive:
we define a type |poly γ X : Set| representing the shape of the
constructor\footnote{It is easy to show that in a dependent theory, restricting
every type to a single constructor does not loose generality.} and a recursive
predicate $\DATA{info}:\DATA{poly}~\VAR{γ}~\VAR{X} → \DATA{Set}$ representing
the information contained in the final datatype.

\ExecuteMetaData[ornaments/iir.tex]{codes}

We can now give the interpretation of a code |ρ : poly δ X| into a
functor |⟦ ρ ⟧₀|.

\ExecuteMetaData[ornaments/iir.tex]{fam-info}
\ExecuteMetaData[ornaments/iir.tex]{fct-hom-i}

\todo{mention |FΣ| and |FΠ|}
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

While taking as parameter a indexed family |𝔽 γ X|, our intepreted functors
only outputs a family |Fam (γ ⊔ δ) (info ρ)|. In other words, |ρ : poly γ X|
only gives the structure of the definition for a given input index |i : Code
Y|.  To account for that, the full description of the first component of
inductive--recursive functors has to be a function |node : Code Y → poly γ X|.
We are left to describe the recursive function, which can be done with a direct
|emit : (i : Code Y) → info (node i) → decode Y i| computing the output index
from the full information.

\ExecuteMetaData[ornaments/iir.tex]{iir}
\ExecuteMetaData[ornaments/iir.tex]{fct-obj}
\ExecuteMetaData[ornaments/iir.tex]{fct-hom}

We have use the post--composition functor defined as follows:

$\FCT{f}$, a functor |Fam α X → Fam α Y|.

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

I previously said that this least--fixed point has in category theory the
semantic of an initial algebra. Let's break it down. Given an endofunctor |F :
C → C|, an |F|-algebras is a carrier |X : C| together with an arrow |F X ⇒ X|.
An arrow between two |F|-algebras |(X , φ)| and |(Y , ψ)| is an arrow |m : X ⇒
Y| subject to the commutativity of the usual square diagram |ψ ∘ F[ m ] ≡ m ∘
φ|. Additionaly, an object |X : C| is initial if for any |Y : C| we can give an
arrow |X ⇒ Y|.

\subsubsection{Catamorphism and Paramorphism}

We almost already have constructed an |⟦ ρ ⟧|-algebra with carrier |μ ρ| and
the constructor |⟨_⟩| mapping the object part of |⟦ ρ ⟧ (μ ρ)| to |μ ρ|. What
is left is to add a trivial proof.

\ExecuteMetaData[ornaments/induction.tex]{roll}

To prove the fact that our algebra is initial we have first have to formally write
the type of algebras.

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

As hinted by it's name, the initiality arrow |fold ρ| is in fact a generic fold
or with fancier wording an elimination rule, precisely a catamorphism. An
elimination scheme is the semantic of recursive functions with pattern
matching. Diggressing a little on elimination rules, we can notice that this is
not the only one.

\todo{introduce paramorphism, factorial on nat}
\todo{para is the most generic (non-dependent) eliminator, ref meeertens}

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

Let's formalize that a bit. I define a predicate |all| stating that a property
hold for all subnodes. It looks a lot like |⟦ ρ ⟧| but does something slightly
more powerful at inductive positions.

\ExecuteMetaData[ornaments/induction.tex]{all}

Given that I can state the induction principle.

\ExecuteMetaData[ornaments/induction.tex]{induction}

I used the helper |every| which explains how to construct a proof of |all| for
|⟦ ρ ⟧ F| if we can prove the predicate for |F|.

\ExecuteMetaData[ornaments/induction.tex]{every}

Note that I could have derived the other elimination rules from this induction
principle, but cata-- and paramorphisms are very useful non--dependent special
cases that diserve to be treated separately and possibly optimized.
Non-dependent functions still have a place of choice in dependent languages:
just because we can replace every implication by universal quantification
doesn't mean it's practical to.

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Ornaments}





%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Case Study: Bidirectional Simply-Typed Lambda Calculus}
\ref{sec:stlc}

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discussion}

\subsection{Index-First Datatypes and a Principled Treatment of Equality}
\todo{bidirectional flow discipline in formalizations}
\todo{no choice about equality, explicit proof obligation instead of weird
pattern matching conditions}

\subsection{Further Work}
\todo{extend to fibred IR}

\todo{precise the paramorphism thing}

\todo{study datastructure reorganizations (eg optimizations)}



%%%%%%%%%%%%%%%%%%%%%%%%%%%
\appendix
\section{Introduction to Agda}
\label{sec:agda}

\section{Bibliography}
\bibliographystyle{plain}
\bibliography{ornaments.bib}


%\section{Fam}

%\ExecuteMetaData[ornaments/fam.tex]{fam-def}

%Arrows of the $\DATA{Fam}\;\VAR{X}$ category.
%\ExecuteMetaData[ornaments/fam.tex]{morph}
%\ExecuteMetaData[ornaments/fam.tex]{fam-pi}
%\ExecuteMetaData[ornaments/fam.tex]{fam-sg}


%Functorial structure for $\DATA{Fam}$.
%\ExecuteMetaData[ornaments/fam.tex]{post-comp}

%Monadic structure for $\DATA{Fam}$.
%\vspace*{1ex}\\
%\parbox[t]{.4\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{monad-eta}}
%\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{monad-mu}}

%Indexed families; our main category from now on:
%\vspace*{1ex}\\
%\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{ifam}}
%\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{ifam-arr}}

%\section{IIR}

%\subsection{Codes}

%\ExecuteMetaData[ornaments/iir.tex]{codes}
%\ExecuteMetaData[ornaments/iir.tex]{iir}

%\subsection{Functor}

%Interpretation of $\DATA{poly}\;\VAR{X}$ as a functor.
%\vspace*{1ex}\\
%\ExecuteMetaData[ornaments/iir.tex]{fam-info}


%Interpretation of $\DATA{IIR}\;\VAR{X}\;\VAR{Y}$ definition as a functor
%from $\DATA{\mathbb{F}}\;\VAR{X}$ to $\DATA{\mathbb{F}}\;\VAR{Y}$.
%\vspace*{1ex}\\
%\ExecuteMetaData[ornaments/iir.tex]{fct-obj}

%Functorial action of $\FCT{⟦}\;\VAR{p}\;\FCT{⟧ᵢ}$ for
%$\VAR{p}\;\KW{\!:\!}\;\DATA{poly}\;\VAR{X}$.
%\vspace*{1ex}\\
%\ExecuteMetaData[ornaments/iir.tex]{fct-hom-i}

%Functorial action of $\FCT{⟦}\;\VAR{α}\;\FCT{⟧}$ for
%$\VAR{α}\;\KW{\!:\!}\;\DATA{IIR}\;\VAR{X}\;\VAR{Y}$.
%\vspace*{1ex}\\
%\ExecuteMetaData[ornaments/iir.tex]{fct-hom}

%\subsection{Initial Algebra}
%\ExecuteMetaData[ornaments/iir.tex]{init-alg-def}
%\ExecuteMetaData[ornaments/iir.tex]{init-alg-impl}
%\ExecuteMetaData[ornaments/iir.tex]{cata}

%\subsection{Composition}
%\ExecuteMetaData[ornaments/iir.tex]{iir-star}
%\ExecuteMetaData[ornaments/iir.tex]{iir-eta}
%\ExecuteMetaData[ornaments/iir.tex]{iir-mu}
%\ExecuteMetaData[ornaments/iir.tex]{iir-pow}
%\ExecuteMetaData[ornaments/iir.tex]{iir-bind}
%\ExecuteMetaData[ornaments/iir.tex]{iir-subst}
%\ExecuteMetaData[ornaments/iir.tex]{iir-comp}

%\subsection{Induction Scheme}
%\ExecuteMetaData[ornaments/iir.tex]{ind-all}
%\ExecuteMetaData[ornaments/iir.tex]{ind-everywhere}
%\ExecuteMetaData[ornaments/iir.tex]{induction}

%\section{Ornaments}

%\ExecuteMetaData[ornaments/orn.tex]{pow}
%\ExecuteMetaData[ornaments/orn.tex]{catholic}

%\subsection{Codes}
%\ExecuteMetaData[ornaments/orn.tex]{code-def}
%\ExecuteMetaData[ornaments/orn.tex]{code-impl}
%\ExecuteMetaData[ornaments/orn.tex]{info+-impl}
%\ExecuteMetaData[ornaments/orn.tex]{infodown-impl}
%\ExecuteMetaData[ornaments/orn.tex]{orn}

%\subsection{Interpretation}
%Interpretation of $\DATA{orn₀}$ to $\DATA{poly}$ is an arrow in a Fam
%$\DATA{Set₁}$ category between $(\DATA{orn₀}\;\CON{,}\;\DATA{info\!+})$ and
%$(\DATA{poly}\;\FCT{∘}\;\FCT{pow⁻¹}\;\CON{,}\;\DATA{info})$.
%\ExecuteMetaData[ornaments/orn.tex]{p-interp}
%\ExecuteMetaData[ornaments/orn.tex]{interp}

%\subsection{Forgetful map}
%\ExecuteMetaData[ornaments/orn.tex]{forget}


\end{document}
