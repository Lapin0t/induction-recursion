\documentclass[11pt,english]{article}

\usepackage{babel}
\usepackage{catchfilebetweentags}

%include agda.fmt
%include ornaments.fmt

\title{IIR Ornaments}
\author{Peio Borthelle, Conor McBride}

\begin{document}
\maketitle

\section{Prelude}

\ExecuteMetaData[ornaments/prelude.tex]{lift}
\ExecuteMetaData[ornaments/prelude.tex]{sigma}
\ExecuteMetaData[ornaments/prelude.tex]{prod}
\ExecuteMetaData[ornaments/prelude.tex]{prop}
\ExecuteMetaData[ornaments/prelude.tex]{equality}
\ExecuteMetaData[ornaments/prelude.tex]{funext}

\section{Fam}

\ExecuteMetaData[ornaments/fam.tex]{fam-def}

Arrows of the $\DATA{Fam}\;\VAR{X}$ category.
\ExecuteMetaData[ornaments/fam.tex]{morph}
\ExecuteMetaData[ornaments/fam.tex]{fam-pi}
\ExecuteMetaData[ornaments/fam.tex]{fam-sg}


Functorial structure for $\DATA{Fam}$.
\ExecuteMetaData[ornaments/fam.tex]{post-comp}

Monadic structure for $\DATA{Fam}$.
\vspace*{1ex}\\
\parbox[t]{.4\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{monad-eta}}
\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{monad-mu}}

Indexed families; our main category from now on:
\vspace*{1ex}\\
\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{ifam}}
\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{ifam-arr}}

\section{IIR}

\subsection{Codes}

\ExecuteMetaData[ornaments/iir.tex]{codes}
\ExecuteMetaData[ornaments/iir.tex]{iir}

\subsection{Functor}

Interpretation of $\DATA{poly}\;\VAR{X}$ as a functor.
\vspace*{1ex}\\
\ExecuteMetaData[ornaments/iir.tex]{fam-info}


Interpretation of $\DATA{IIR}\;\VAR{X}\;\VAR{Y}$ definition as a functor
from $\DATA{\mathbb{F}}\;\VAR{X}$ to $\DATA{\mathbb{F}}\;\VAR{Y}$.
\vspace*{1ex}\\
\ExecuteMetaData[ornaments/iir.tex]{fct-obj}

Functorial action of $\FCT{⟦}\;\VAR{p}\;\FCT{⟧ᵢ}$ for
$\VAR{p}\;\KW{\!:\!}\;\DATA{poly}\;\VAR{X}$.
\vspace*{1ex}\\
\ExecuteMetaData[ornaments/iir.tex]{fct-hom-i}

Functorial action of $\FCT{⟦}\;\VAR{α}\;\FCT{⟧}$ for
$\VAR{α}\;\KW{\!:\!}\;\DATA{IIR}\;\VAR{X}\;\VAR{Y}$.
\vspace*{1ex}\\
\ExecuteMetaData[ornaments/iir.tex]{fct-hom}

\subsection{Initial Algebra}
\ExecuteMetaData[ornaments/iir.tex]{init-alg-def}
\ExecuteMetaData[ornaments/iir.tex]{init-alg-impl}
\ExecuteMetaData[ornaments/iir.tex]{cata}

\subsection{Composition}
\ExecuteMetaData[ornaments/iir.tex]{iir-star}
\ExecuteMetaData[ornaments/iir.tex]{iir-eta}
\ExecuteMetaData[ornaments/iir.tex]{iir-mu}
\ExecuteMetaData[ornaments/iir.tex]{iir-pow}
\ExecuteMetaData[ornaments/iir.tex]{iir-bind}
\ExecuteMetaData[ornaments/iir.tex]{iir-subst}
\ExecuteMetaData[ornaments/iir.tex]{iir-comp}

\subsection{Induction Scheme}
\ExecuteMetaData[ornaments/iir.tex]{ind-all}
\ExecuteMetaData[ornaments/iir.tex]{ind-everywhere}
\ExecuteMetaData[ornaments/iir.tex]{induction}

\section{Ornaments}

\ExecuteMetaData[ornaments/orn.tex]{pow}
\ExecuteMetaData[ornaments/orn.tex]{catholic}

\subsection{Codes}
\ExecuteMetaData[ornaments/orn.tex]{code-def}
\ExecuteMetaData[ornaments/orn.tex]{code-impl}
\ExecuteMetaData[ornaments/orn.tex]{info+-impl}
\ExecuteMetaData[ornaments/orn.tex]{infodown-impl}
\ExecuteMetaData[ornaments/orn.tex]{orn}

\subsection{Interpretation}
Interpretation of $\DATA{orn₀}$ to $\DATA{poly}$ is an arrow in a Fam
$\DATA{Set₁}$ category between $(\DATA{orn₀}\;\CON{,}\;\DATA{info\!+})$ and
$(\DATA{poly}\;\FCT{∘}\;\FCT{pow⁻¹}\;\CON{,}\;\DATA{info})$.
\ExecuteMetaData[ornaments/orn.tex]{p-interp}
\ExecuteMetaData[ornaments/orn.tex]{interp}

\subsection{Forgetful map}
\ExecuteMetaData[ornaments/orn.tex]{forget}


\end{document}
