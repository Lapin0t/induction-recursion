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

\end{document}
