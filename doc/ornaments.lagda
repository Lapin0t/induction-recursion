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
\ExecuteMetaData[ornaments/fam.tex]{monad}

Indexed families; our main category from now on:
\vspace*{1ex}\\
\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{ifam}}
\parbox[t]{.5\textwidth}{\ExecuteMetaData[ornaments/fam.tex]{ifam-arr}}

\section{IIR}

\subsection{Codes}
\ExecuteMetaData[ornaments/iir.tex]{codes}

\subsection{Functor}
\ExecuteMetaData[ornaments/iir.tex]{iir}
\ExecuteMetaData[ornaments/iir.tex]{fam-info}

Interpretation of an $\DATA{IIR}\;\VAR{X}\;\VAR{X}$ definition as a functor on
$\DATA{𝔽}\;\VAR{X}$.
\ExecuteMetaData[ornaments/iir.tex]{fct-obj}

\ExecuteMetaData[ornaments/iir.tex]{fct-hom-i}

Functorial action on arrows of $\DATA{𝔽}\;\VAR{X}$.
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
\ExecuteMetaData[ornaments/orn.tex]{p-interp}
\ExecuteMetaData[ornaments/orn.tex]{interp}

\subsection{Forgetful map}
\ExecuteMetaData[ornaments/orn.tex]{forget}


\end{document}
