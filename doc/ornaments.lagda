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
\setlength\parindent{1em}

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
types) as recently axiomatized by Ghani et al (\ref{ghani17}). In doing so we
we will provide a basic toolbox of results for these types, notably studying
some of their induction schemes.

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
numbers and Π--types):

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


We can see the most important caracteristic of inductive-recursive definitions:
the simultaneous definition of an inductive type and a recursive function on it
with the ability to use the recursive function in the type of the constructors,
even in negative positions (left of an arrow). \textit{Indexed}
inductive-recursive definitions are a slight generalization, similar to the
relationship between inductive types and inductive families. In its full
generality, indexed induction recursion allows to simultaneously define an
inductive predicate $\DATA{U} : \DATA{I} → \DATA{Set}$ and an indexed recursive
function $\FCT{f} : (\VAR{i} : \DATA{I}) → \DATA{U}~\VAR{i} → \DATA{X}~\VAR{i}$
for any $\DATA{I} : \DATA{Set}$ and $\DATA{X} : \DATA{I} → \DATA{Set₁}$. Using
a vocabulary influenced by the \textit{bidirectional} paradigm for typing
(\todo{ref}) we will call $\VAR{i}:\DATA{I}$ the \textit{input index} and
$\DATA{X}~\VAR{i}$ the \textit{output index}. Indeed if we think of the
judgement $a : \DATA{U}~\VAR{i}$ as a typechecker would, the judgment requires
the validity of $\VAR{i}:\DATA{I}$ and suffices to the validity of
$\FCT{f}~\VAR{a} : \DATA{X}~\VAR{i}$. We will explore bidirectionality further
in section \ref{sec:stlc}.

Induction-recursion is arguably the most powerful set former (currently known)
for ITT. \todo{who?} has shown that its addition gives ITT a proof-theoretic
strength slightly greater than KPM, Kripke--Platek set theory together with a
recursive Mahlo universe. Although its proof-theoretic strength is greater
than $Γ₀$, ITT with induction--recursion is still considered predicative in a
looser constructivist sense: it arguably has bottom--to--top construction.


%%%%%%%%%%


\subsection{Categories}

Since we will use category theory as our main language we first recall the
definition of a category $C$:
\begin{itemize}
\item a collection of objects $\DATA{C} : \DATA{Set}$
\item a collection of morphisms (or arrows) $\DATA{\anonymous\!⇒\!\anonymous} : (\VAR{x}~\VAR{y} : \DATA{C}) → \DATA{Set}$
\item an identity $\FCT{1} : (\VAR{x} : \DATA{C}) → \VAR{x} ⇒ \VAR{x}$
\item a composition operation $\anonymous\!∘\!\anonymous : ∀~\{\VAR{x}~\VAR{y}~\VAR{z}\} →
\VAR{y} ⇒ \VAR{z} → \VAR{x} ⇒ \VAR{y} → \VAR{x} ⇒ \VAR{z}$ that is associative and respects the identity laws
\end{itemize}

A functor $\FCT{F}$ between categories $\DATA{C}$ and $\DATA{D}$ is a mapping
of objects $\FCT{F} : \DATA{C} → \DATA{D}$ and a mapping of arrows $\FCT{F[\_]}
: ∀~\{\VAR{x}~\VAR{y}\} → \VAR{x} ⇒ \VAR{y} → \FCT{F}~\VAR{x} ⇒
\FCT{F}~\VAR{y}$.

\subsection{Data types}

The different notions of data types, by which we mean inductive types,
inductive--recursive types and their indexed variants, share their semantics:
initial algebras of endfunctors. In a first approximation, we can think of an
``initial algebra'' as the categorical notion for the ``least closed set''
(just not only for sets). As such, we will study a certain class of functors
with initial algebras that give rise to our indexed inductive--recursive types.

The most simple data types, inductive types, live in the category $\DATA{Set}$.
On the other hand, as we have seen, inductive--recursive data types are formed
by couples in $(\DATA{U} : \DATA{Set})~×~(\DATA{U} → \DATA{X})$. Categorically,
this an $\DATA{X}$-indexed set and it is an object of the slice category of
$\DATA{Set} / \DATA{X}$. We will be representing these objects by the record
type $\DATA{Fam}~\VAR{γ}~\VAR{X}$:

\ExecuteMetaData[ornaments/fam.tex]{fam-def}
\ExecuteMetaData[ornaments/fam.tex]{morph}

\todo{Introduce |𝔽|, name of that thing in category theory?}
\ExecuteMetaData[ornaments/fam.tex]{iset}
\ExecuteMetaData[ornaments/fam.tex]{ifam}
\ExecuteMetaData[ornaments/fam.tex]{ifam-arr}

\subsection{A Universe of Strictly Positive Functors}

Dybjer and Setzer have first presented codes for (indexed) inductive-recursive
definitions (\todo{ref}) by constructing a universe of functors. However, as
conjectured by \cite{ghani17}, this universe lacks closure under composition,
\textit{eg} if given the codes of two functors, we don't know how to construct
a code for the composition of the functors. We will thus use an alternative
universe construction devised by McBride which we call \textit{irish}
induction--recursion. It has also been called \textit{polynomial}
induction--recursion because it draws similarities to polynomial functors, yet
they are different notions and should not be confused.

We first give a definition that will encode the inductive part. This definition
is itself inductive--recursive: we define a type $\DATA{poly}~\VAR{γ}~\VAR{X}$
representing the shape of the constructor\footnote{It is easy to show that in a
dependent theory, restricting every type to a single constructor does not loose
generality.} and a recursive predicate $\DATA{info}:\DATA{poly}~\VAR{γ}~\VAR{X}
→ \DATA{Set}$ representing the set of information contained in the final
datatype:

\ExecuteMetaData[ornaments/iir.tex]{codes}

We can already give some intuition for the constructors. $\CON{ι}~\VAR{i}$
codes an inductive position with input index $\VAR{i}$, \textit{eg} something
related to the identity functor. Its contained information is
$\PRO{decode}~\VAR{X}~\VAR{i}$ \textit{eg} the output index that we will obtain
from the later constructed recursive function. $\CON{κ}~\VAR{A}$,
$\CON{σ}~\VAR{A}~\VAR{B}$ and $\CON{π}~\VAR{A}~\VAR{B}$ code respectively the
constant, dependent sum and dependent product functors, with straightforward
information. Note that the domain for our Π--functors is a $\DATA{Set}$ and not
a $\DATA{poly}$, indeed this corresponds to the strict positivity constraint
that no inductive position is allowed left of an arrow in the type of the
constructor.

We can already interpret these codes into functors from indexed families into families of node informations:
\ExecuteMetaData[ornaments/iir.tex]{fam-info}
\ExecuteMetaData[ornaments/iir.tex]{fct-hom-i}

\todo{Expand a bit on what node/emit means}
\ExecuteMetaData[ornaments/iir.tex]{iir}
\ExecuteMetaData[ornaments/iir.tex]{fct-obj}
\ExecuteMetaData[ornaments/iir.tex]{fam-hom}

\subsection{Fixpoint and Induction Schemes}

\todo{Initial algebra}
\ExecuteMetaData[ornaments/induction.tex]{init-alg}
\ExecuteMetaData[ornaments/induction.tex]{init-alg-in}

\todo{catamorphism}
\ExecuteMetaData[ornaments/induction.tex]{alg}
\ExecuteMetaData[ornaments/induction.tex]{cata}

\todo{induction principle}
\ExecuteMetaData[ornaments/induction.tex]{induction}
\ExecuteMetaData[ornaments/induction.tex]{ind-every}
\ExecuteMetaData[ornaments/induction.tex]{ind-all}

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Ornaments}




%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Case Study: Bidirectional Simply-Typed Lambda Calculus}
\ref{sec:stlc}

%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discussion}

\subsection{Index-First Datatypes and Principled Treatment of Equality}



%%%%%%%%%%%%%%%%%%%%%%%%%%%
\appendix
\section{Introduction to Agda}
\label{sec:agda}

\section{Bibliography}
\bibliographystyle{plain}
\bibliography{ornaments.bib}



%\ExecuteMetaData[ornaments/prelude.tex]{lift}
%\ExecuteMetaData[ornaments/prelude.tex]{sigma}
%\ExecuteMetaData[ornaments/prelude.tex]{prod}
%\ExecuteMetaData[ornaments/prelude.tex]{prop}
%\ExecuteMetaData[ornaments/prelude.tex]{equality}
%\ExecuteMetaData[ornaments/prelude.tex]{funext}

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
