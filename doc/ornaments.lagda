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
\ExecuteMetaData[ornaments/prelude.tex]{prop}
\ExecuteMetaData[ornaments/prelude.tex]{equality}

\section{Fam}

\ExecuteMetaData[ornaments/fam.tex]{fam-def}
\ExecuteMetaData[ornaments/fam.tex]{post-comp}
\ExecuteMetaData[ornaments/fam.tex]{morph}
\ExecuteMetaData[ornaments/fam.tex]{fam-pi}
\ExecuteMetaData[ornaments/fam.tex]{fam-sg}
\ExecuteMetaData[ornaments/fam.tex]{monad}
\ExecuteMetaData[ornaments/fam.tex]{ifam}

\section{IIR}

\subsection{Codes}
\ExecuteMetaData[ornaments/iir.tex]{codes}

\subsection{Functor}
\ExecuteMetaData[ornaments/iir.tex]{iir}
\ExecuteMetaData[ornaments/iir.tex]{fam-info}
\ExecuteMetaData[ornaments/iir.tex]{fct-obj}
\ExecuteMetaData[ornaments/iir.tex]{fct-hom-i}
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

\end{document}
