\documentclass[a4paper]{article}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{hyperref}
\usepackage[draft]{todonotes}
% \usepackage[disable]{todonotes}
\usepackage{framed,color}
% \usepackage{multirow}
\usepackage{alltt}
\usepackage{amsthm}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt


% Frame color
\definecolor{shadecolor}{rgb}{1.0,0.9,0.7}

% Theorem styles
\newtheorem{theorem}{Theorem}[section]
\newtheorem{remark}{Remark}[section]
\newtheorem{conjecture}{Conjecture}[section]
\theoremstyle{definition}
% \newtheorem{example}{Example}[section]
\newtheorem{examplex}{Example}[section]
\newenvironment{example}
  {\pushQED{\qed}\renewcommand{\qedsymbol}{$\triangle$}\examplex}
  {\popQED\endexamplex}
\newtheorem{definition}{Definition}[section]

\newcommand{\definedin}[1]{\footnote{Module: #1}}
\newcommand{\args}[1]{\overline{#1}}
\newcommand{\ttargs}[1]{\(\args{\texttt{#1}}\)}
\newcommand{\ttunderline}[1]{\(\underline{\texttt{#1}}\)}
\definecolor{ttemph1}{HTML}{BB0000}
\definecolor{ttemph2}{HTML}{0000BB}
\newcommand{\ttemph}[2]{%
\ifnum#1=1\textcolor{ttemph1}{\textbf{#2}}%
\else\ifnum#1=2\textcolor{ttemph2}{\textbf{#2}}%
\else\textbf{#2}%
\fi\fi}

\newcommand{\Bool}{\textrm{Bool}}
\newcommand{\List}{\textrm{List}}
\newcommand{\Nat}{\textrm{Nat}} % or \mathit{N\!at}
\newcommand{\NatList}{\textrm{NatList}}
\newcommand{\PairOfBools}{\textrm{PairOfBools}}
\newcommand{\RoseTree}{\textrm{RoseTree}}
\newcommand{\Tree}{\textrm{Tree}}

%--------------------------------------------------

%  Agda mess

\usepackage{agda}
\usepackage{catchfilebetweentags}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AS}{\AgdaString}
\newcommand{\AY}{\AgdaSymbol}
\newcommand{\AN}{\AgdaNumber}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AO}{\AgdaOperator}
\newcommand{\AI}{\AgdaInductiveConstructor}
\newcommand{\AC}{\AgdaCoinductiveConstructor}
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AL}{\AgdaField}
\newcommand{\AR}{\AgdaArgument}
\newcommand{\AT}{\AgdaIndent}
\newcommand{\ARR}{\AgdaRecord}
\newcommand{\AP}{\AgdaPostulate}

\newcommand{\InsertCodeInline}[2][Proposal.tex]{\codeinlinetrue\ExecuteMetaData[../src-tex/#1]{#2}}
\newcommand{\InsertCode}[2][Proposal.tex]{
  \codeinlinefalse
  \medskip
  \ExecuteMetaData[../src-tex/#1]{#2}

  \medskip}
\newcommand{\InsertCodeN}[2][Proposal.tex]{
  \codeinlinefalse
  \medskip
  \ExecuteMetaData[../src-tex/#1]{#2}\refstepcounter{codeblock}\begin{center}Listing \thecodeblock\end{center}\label{code:#2}%

  \medskip}

\newcounter{codeblock}
\newcommand{\labelcodeblock}[2]{\refstepcounter{codeblock}\label{#1}\begin{center}Listing \thecodeblock\end{center}}

%--------------------------------------------------

\setmainfont[ItalicFont = xits-italic.otf
, BoldFont = xits-bold.otf
, BoldItalicFont = xits-bolditalic.otf]{xits-regular.otf}
\setmathfont[BoldFont = xits-mathbold.otf]{xits-math.otf}
\setsansfont[Scale=MatchLowercase
, ItalicFont = DejaVuSans-Oblique.ttf
, BoldFont = DejaVuSans-Bold.ttf
, BoldItalicFont = DejaVuSans-BoldOblique.ttf]{DejaVuSans.ttf}
\setmonofont[Scale=MatchLowercase
, ItalicFont = DejaVuSansMono-Oblique.ttf
, BoldFont = DejaVuSansMono-Bold.ttf
, BoldItalicFont = DejaVuSansMono-BoldOblique.ttf]{DejaVuSansMono.ttf}

\newfontfamily{\xitsfont}[Scale=MatchLowercase]{xits-regular.otf}

\DeclareTextFontCommand{\textxits}{\xitsfont}

\usepackage{newunicodechar}

% \newunicodechar{●}{\textxits{•}}
% \newunicodechar{⌷}{\textxits{$\vrectangle$}}
% \newunicodechar{▱}{\textxits{\rotatebox[origin=c]{105}{▱}}}
\newunicodechar{⊎}{\textxits{⊎}}

%--------------------------------------------------

\title{Implementing Ornaments - Thesis Proposal}
\date{\today}
\author{Yorick Sijsling}

\begin{document}

\maketitle

\begin{flushright}
\emph{Supervised by} Wouter Swierstra\\
\emph{Second examiner} Johan Jeuring
\end{flushright}

\listoftodos
\input{introduction.tex}
\input{literature.tex}
\input{prototype.tex}
\input{overview.tex}
\input{plan.tex}

\bibliographystyle{plain}
% \bibliographystyle{alpha}
% \bibliographystyle{apa}
\bibliography{main}

\end{document}