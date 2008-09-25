%%
%% This is file 'cupbook.cls'
%%
%% A LaTeX class file for the CUP standard designs 5a to 9b
%%
%% Copyright (1995-2004) Cambridge University Press
%%
%% by Ali Woollatt and Mark Reed
%%   based on cupbook.sty v1.2 <1993/03/18>
%%
%% changes in this version include: 
%%   improved toc design
%%   changed part titles to Roman
%%   justified bibliographies
%%
%% Bugs (in the case of unchanged files) should be reported to
%% texline@cambridge.org
%%
%% This software may only be used in the preparation of journal articles
%% or books or parts of books to be published by Cambridge University Press.
%% Any other use constitutes an infringement of copyright.
%%
%% \CharacterTable
%%  {Upper-case    \A\B\C\D\E\F\G\H\I\J\K\L\M\N\O\P\Q\R\S\T\U\V\W\X\Y\Z
%%   Lower-case    \a\b\c\d\e\f\g\h\i\j\k\l\m\n\o\p\q\r\s\t\u\v\w\x\y\z
%%   Digits        \0\1\2\3\4\5\6\7\8\9
%%   Exclamation   \!     Double quote  \"     Hash (number) \#
%%   Dollar        \$     Percent       \%     Ampersand     \&
%%   Acute accent  \'     Left paren    \(     Right paren   \)
%%   Asterisk      \*     Plus          \+     Comma         \,
%%   Minus         \-     Point         \.     Solidus       \/
%%   Colon         \:     Semicolon     \;     Less than     \<
%%   Equals        \=     Greater than  \>     Question mark \?
%%   Commercial at \@     Left bracket  \[     Backslash     \\
%%   Right bracket \]     Circumflex    \^     Underscore    \_
%%   Grave accent  \`     Left brace    \{     Vertical bar  \|
%%   Right brace   \}     Tilde         \~}
%%

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{cupbook}[2004/06/10 v2.1 CUP LaTeX2e document class]

% font sizes for cupbook
% \tiny                        5/6
% \footnotesize                8/9
% \large                      11/14
% \Large                      12/17
% \LARGE                      16/19 (chaptertitle size)
% \let\Huge\huge              18/24 (chapternumber size)

% for large sizes (247x174mm - cup5 and cup6 designs)
% \scriptsize                  8/9
% \enotesize                   9/10
% \let\tablesize\small        10/11
% \let\smallish\normalsmall   10/12
% \listsize                   10/13
% \normalsize                 11/14
%
% for small sizes (228x152mm - cup7, cup8 and cup9 designs)
% \scriptsize                  7/8
% \let\tablesize\small         9/10
% \let\enotesize\small         9/10
% \smallish                    9/11
% \normalsmall                10/12
% \let\listsize\normalsize    10/13

\newif\ifSFB@multisty
\newif\ifSFB@largesty
\newif\ifSFB@indentsty
\newif\ifSFB@landscape
\newif\if@openright
\newif\ifSFB@truesize
\newdimen\SFB@indent
\newdimen\SFB@floatindent
\SFB@indent \z@

\DeclareOption{cup5a}{\SFB@largestytrue\SFB@indentstytrue\SFB@indent 3pc}
\DeclareOption{CUP5A}{\@nameuse{ds@cup5a}}
\DeclareOption{cup5b}{\SFB@multistytrue\SFB@largestytrue
  \SFB@indentstytrue\SFB@indent 3pc}
\DeclareOption{CUP5B}{\@nameuse{ds@cup5b}}
\DeclareOption{cup6a}{\SFB@largestytrue}
\DeclareOption{CUP6A}{\@nameuse{ds@cup6a}}
\DeclareOption{cup6b}{\SFB@multistytrue\SFB@largestytrue}
\DeclareOption{CUP6B}{\@nameuse{ds@cup6b}}
\DeclareOption{cup7a}{\relax}
\DeclareOption{CUP7A}{\relax}
\DeclareOption{cup7b}{\SFB@multistytrue}
\DeclareOption{CUP7B}{\@nameuse{ds@cup7b}}
\DeclareOption{cup8a}{\SFB@indentstytrue\SFB@indent 3pc}
\DeclareOption{CUP8A}{\@nameuse{ds@cup8a}}
\DeclareOption{cup8b}{\SFB@multistytrue\SFB@indentstytrue\SFB@indent 3pc}
\DeclareOption{CUP8B}{\@nameuse{ds@cup8b}}
\DeclareOption{cup9a}{\SFB@indentstytrue\SFB@indent=\z@}
\DeclareOption{CUP9A}{\@nameuse{ds@cup9a}}
\DeclareOption{cup9b}{\SFB@multistytrue\SFB@indentstytrue}
\DeclareOption{CUP9B}{\@nameuse{ds@cup9b}}
\DeclareOption{oneside}{\relax}
\DeclareOption{twoside}{\@twosidetrue \@mparswitchtrue}
\DeclareOption{onecolumn}{\@twocolumnfalse}
\DeclareOption{twocolumn}{\@twocolumntrue}
\DeclareOption{draft}{\setlength\overfullrule{5\p@}}
\DeclareOption{final}{\setlength\overfullrule{\z@}}
\DeclareOption{openright}{\@openrighttrue}
\DeclareOption{openany}{\@openrightfalse}
\DeclareOption{a4paper}
  {\setlength\paperheight {297mm}%
   \setlength\paperwidth  {210mm}}
\DeclareOption{landscape}
  {\setlength\@tempdima   {\paperheight}%
   \setlength\paperheight {\paperwidth}%
   \setlength\paperwidth  {\@tempdima}%
   \SFB@landscapetrue}
\DeclareOption{truesize}{\SFB@truesizetrue}

\ExecuteOptions{a4paper,twoside,onecolumn,final,openright}
\ProcessOptions\relax

\newcommand\cls@pttxt[1]{\typeout{Document Class: cupbook, option\space CUP#1.}}
\newcommand\CUP@five{\ifSFB@multisty \cls@pttxt{5b}\else \cls@pttxt{5a}\fi}
\newcommand\CUP@six{\ifSFB@multisty \cls@pttxt{6b}\else \cls@pttxt{6a}\fi}
\newcommand\CUP@seven{\ifSFB@multisty \cls@pttxt{7b}\else \cls@pttxt{7a}\fi}
\newcommand\CUP@eight{\ifSFB@multisty \cls@pttxt{8b}\else \cls@pttxt{8a}\fi}
\newcommand\CUP@nine{\ifSFB@multisty \cls@pttxt{9b}\else \cls@pttxt{9a}\fi}

\ifSFB@largesty
  \ifSFB@indentsty \CUP@five\else \CUP@six\fi
\else
  \ifSFB@indentsty {\ifdim\SFB@indent=\z@ \CUP@nine\else \CUP@eight\fi}%
  \else
    \CUP@seven
  \fi
\fi

\newif\if@mainmatter \@mainmattertrue
\newcommand\frontmatter{\cleardoublepage
            \@mainmatterfalse\pagenumbering{roman}}
\newcommand\mainmatter{\cleardoublepage
       \@mainmattertrue\pagenumbering{arabic}}
\newcommand\backmatter{\if@openright\cleardoublepage\else\clearpage\fi
      \@mainmatterfalse}

%  ****************************************
%  *               FONTS                  *
%  ****************************************
%
\setlength\lineskip{1\p@}
\setlength\normallineskip{1\p@}
\renewcommand\baselinestretch{}
\newskip\SFB@baseskip
\newskip\SFB@theskip
\def\SFB@setskips#1{\SFB@theskip #1\relax%
  \abovedisplayskip      0.50\SFB@theskip \@plus 0.25\SFB@theskip \@minus 1\p@%
  \belowdisplayskip      \abovedisplayskip
  \abovedisplayshortskip 0.25\SFB@theskip \@plus 0.25\SFB@theskip
  \belowdisplayshortskip 0.50\SFB@theskip \@plus 0.25\SFB@theskip \@minus 1\p@%
}
\def\SFB@setlists#1{\SFB@theskip #1\relax%
 \def\@listi{\leftmargin\leftmargini
  \topsep  0.5\SFB@theskip \@plus 2\p@ \@minus 1\p@%
  \parsep  \z@
  \itemsep \z@}}
%
%
% common sizes
\newcommand{\@xvipt}{16}%                     16pt size
\DeclareMathSizes{\@xvipt}{\@xvipt}{\@xiipt}{\@xpt}
\newcommand{\@xviiipt}{18}%                   18pt size
\DeclareMathSizes{\@xviiipt}{\@xviiipt}{\@xiipt}{\@xpt}

\newcommand\tiny{\@setfontsize\tiny\@vpt{6}\SFB@setskips\SFB@setlists}
\newcommand\footnotesize{\SFB@baseskip 9pt%
  \@setfontsize\footnotesize\@viiipt{9}\SFB@setskips\SFB@setlists}
\newcommand\large{\@setfontsize\large\@xipt{14}\SFB@setskips\SFB@setlists}
\newcommand\Large{\@setfontsize\Large\@xiipt{17}\SFB@setskips\SFB@setlists}
\newcommand\LARGE{\@setfontsize\LARGE\@xvipt{19}\SFB@setskips\SFB@setlists}
\newcommand\huge{\@setfontsize\huge\@xviiipt{24}\SFB@setskips\SFB@setlists}
\let\Huge\huge

\ifSFB@largesty
  \newcommand\scriptsize{%
    \@setfontsize\scriptsize\@viiipt{9}\SFB@setskips\SFB@setlists}
  \newcommand\enotesize{\SFB@baseskip 10pt%
    \@setfontsize\enotesize\@ixpt{10}\SFB@setskips\SFB@setlists}
  \newcommand\small{\SFB@baseskip 11pt%
    \@setfontsize\small\@xpt{11}\SFB@setskips\SFB@setlists}
  \let\tablesize\small
  \newcommand\normalsmall{\SFB@baseskip 12pt%
    \@setfontsize\normalsmall\@xpt{12}\SFB@setskips\SFB@setlists}
  \let\smallish\normalsmall
  \newcommand\listsize{\SFB@baseskip 13pt%
    \@setfontsize\listsize\@xpt{13}\SFB@setskips\SFB@setlists}
  \renewcommand\normalsize{\SFB@baseskip 14pt%
    \@setfontsize\normalsize\@xipt{14}\SFB@setskips{\SFB@baseskip}%
    \let\@listi\@listI}
\else
  \newcommand\scriptsize{%
    \@setfontsize\scriptsize\@viipt{8}\SFB@setskips\SFB@setlists}
  \newcommand\small{\SFB@baseskip 10pt%
    \@setfontsize\small\@ixpt{10}\SFB@setskips\SFB@setlists}
  \let\tablesize\small
  \let\enotesize\small
  \newcommand\smallish{\SFB@baseskip 11pt%
    \@setfontsize\smallish\@ixpt{11}\SFB@setskips\SFB@setlists}
  \newcommand\normalsmall{\SFB@baseskip 12pt%
    \@setfontsize\normalsmall\@xpt{12}\SFB@setskips\SFB@setlists}
  \renewcommand\normalsize{\SFB@baseskip 13pt%
    \@setfontsize\normalsize\@xpt{13}\SFB@setskips{\SFB@baseskip}%
    \let\@listi\@listI}
  \let\listsize\normalsize
\fi
\normalsize

\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*\cal{\@fontswitch{\relax}{\mathcal}}
\DeclareRobustCommand*\mit{\@fontswitch{\relax}{\mathnormal}}


%  ****************************************
%  *            PAGE LAYOUT               *
%  ****************************************
%
% All margin dimensions measured from a point one inch from top and side
% of page.
%
% SIDE MARGINS:
%
  \setlength\oddsidemargin{4pc}
  \setlength\evensidemargin{4pc}
  \setlength\marginparwidth{4pc}
  \setlength\marginparsep{0.5pc}
\ifSFB@largesty
  \setlength\topmargin{34\p@}
  \setlength\headheight{14\p@}
 %% \setlength\footheight{14\p@}
  \setlength\footskip{28\p@}
  \setlength\topskip{11\p@}
\else
  \setlength\topmargin{29\p@}
  \setlength\headheight{13\p@}
%%  \setlength\footheight{13\p@}
  \setlength\footskip{26\p@}
  \setlength\topskip{10\p@}
\fi
  \setlength\headsep{10\p@}
%
% DIMENSION OF TEXT:
%
\newdimen\SFB@measure
\setlength\textheight{39\baselineskip}
\addtolength\textheight{\topskip}

\ifSFB@largesty
  \SFB@measure 30pc
\else
  \SFB@measure 26pc
\fi
\textwidth\SFB@measure
\ifSFB@landscape
  \textwidth\textheight
  \textheight\SFB@measure
\fi
\setlength\columnsep{1pc}
\setlength\columnseprule{0\p@}
%
% FOOTNOTES
%
\setlength\footnotesep{6.5\p@}
\setlength{\skip\footins}{9\p@ \@plus 4\p@ \@minus 2\p@}% top of first footnote.
%
% FLOATS
%
\setlength\floatsep{13\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\textfloatsep{20\p@ \@plus 2\p@ \@minus 4\p@}
\setlength\intextsep{13\p@ \@plus 2\p@ \@minus 2\p@}
%%\setlength\@maxsep{20\p@}
\setlength\dblfloatsep{13\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\dbltextfloatsep{20\p@ \@plus 2\p@ \@minus 4\p@}
%%\setlength\@dblmaxsep{20\p@}
%
%  for floats on a separate float page
\setlength\@fptop{0\p@ \@plus 0fil}
\setlength\@fpsep{13\p@ \@plus 0fil}
\setlength\@fpbot{0\p@ \@plus 3fil}
%
%   wide floats
\setlength\@dblfptop{0\p@ \@plus 0fil}
\setlength\@dblfpsep{13\p@ \@plus 0fil}
\setlength\@dblfpbot{0\p@ \@plus 3fil}
%
%
% MARGINAL NOTES:
%
\setlength\marginparpush{5\p@}

%  ****************************************
%  *           PARAGRAPHING               *
%  ****************************************
%
\setlength\parskip{0\p@ \@plus .25\p@}
\setlength\parindent{1em}
\listparindent\parindent
\setlength\partopsep{0\p@ \@plus 1\p@}
%
% The following page-breaking penalties are defined
%
\@lowpenalty   51
\@medpenalty  151
\@highpenalty 301
\@beginparpenalty -\@lowpenalty
\@endparpenalty   -\@lowpenalty
\@itempenalty     -\@lowpenalty
%
  \clubpenalty=0       % 'Club line'  at bottom of page.
  \widowpenalty=10000  % 'Widow line' at top of page.
% \displaywidowpenalty % Math display widow line.
% \predisplaypenalty   % Breaking before a math display.
% \postdisplaypenalty  % Breaking after a math display.
% \interlinepenalty    % Breaking at a line within a paragraph.
% \brokenpenalty       % Breaking after a hyphenated line.

%    ****************************************
%    *        CHAPTERS AND SECTIONS         *
%    ****************************************
%
% Heading for the \chapter command -- fixed depth chapter headings...
%
\newdimen\SFB@headwidth
\SFB@headwidth \textwidth
\addtolength{\SFB@headwidth}{-\SFB@indent}
\def\@makechapterhead#1{{\normalsize
  \parindent 0\p@
  \vspace*{-0.5\baselineskip}
  \ifnum \c@secnumdepth >\m@ne
   \raisebox{0.5\baselineskip}[0\p@][0\p@]{\mbox{\hspace*{\SFB@indent}}%
    \begin{minipage}[t]{\SFB@headwidth}
     \ifSFB@indentsty \raggedright \else \centering \fi
     \ifSFB@appendix {\huge Appendix \thechapter}%
               \else {\huge\bfseries \thechapter}%
     \fi
     \par
     \ifSFB@largesty \vskip 9\p@ \else \vskip 7\p@ \fi
     \LARGE\rm #1
     \nobreak
     \par
     \ifSFB@multisty
      \vskip 7\p@
      \normalsize
      \ifSFB@indentsty \begin{author@tabular}[t]{@{}l@{}}
                 \else \begin{author@tabular}[t]{c}
      \fi
        \@author
      \end{author@tabular}
      \par
     \fi
    \end{minipage}}
  \else
   \raisebox{0.5\baselineskip}[0\p@][0\p@]{\mbox{\hspace*{\SFB@indent}}%
    \begin{minipage}[t]{\SFB@headwidth}
     \ifSFB@indentsty \raggedright \else \centering \fi
     {\huge\bfseries \mbox{}}
     \par
     \ifSFB@largesty \vskip 9\p@ \else \vskip 7\p@ \fi
     \LARGE\rm #1
     \nobreak
     \par
    \end{minipage}}
  \fi
  \par \nobreak
  \vskip 10.5\baselineskip% 2.5 less than the first line of text
  }
}
\def\@makeschapterhead#1{{\normalsize
  \parindent 0\p@
  \vspace*{-0.5\baselineskip}
  \raisebox{0.5\baselineskip}[0\p@][0\p@]{\mbox{\hspace*{\SFB@indent}}%
   \begin{minipage}[t]{\SFB@headwidth}
    \ifSFB@indentsty \raggedright \else \centering \fi
    {\huge\bfseries \mbox{}}
    \par
    \ifSFB@largesty \vskip 9\p@ \else \vskip 7\p@ \fi
    \LARGE\rm #1
    \nobreak
    \par
   \end{minipage}}
  \par \nobreak
  \vskip 10.5\baselineskip % 2.5 less than the first line of text
  }
}
%
% \secdef{UNSTARCMDS}{STARCMDS} :
%
\def\chapter{\clearpage
   \thispagestyle{plain}
   \global\@topnum\z@
   \@afterindentfalse
   \secdef\@chapter\@schapter}
\def\@chapter[#1]#2{%
 \ifnum \c@secnumdepth >\m@ne
   \refstepcounter{chapter}
   \typeout{\@chapapp\space\thechapter.}
   \ifSFB@multisty
    \ifx\@shortauthor\@empty
     \addcontentsline{toc}{chapter}{\protect\numberline{\thechapter}#1}
    \else
     \addcontentsline{toc}{chapter}{\protect
      \numberline{\thechapter}#1\hspace{1em}{\itshape \@shortauthor\/}}
    \fi
   \else
     \ifSFB@appendix
      \addcontentsline{toc}{chapter}{\protect\SFB@numberline{\thechapter}#1}
     \else
      \addcontentsline{toc}{chapter}{\protect\numberline{\thechapter}#1}
     \fi
   \fi
  \else
   \addcontentsline{toc}{chapter}{#1}
  \fi
  \ifSFB@multisty
   \markboth{\@shortauthor}{#1}
   \gdef\SFB@endnotehead{\relax}
  \else
   \chaptermark{#1}
   \gdef\SFB@endnotehead{\@chapapp\ \thechapter}
  \fi
  \if@twocolumn
    \@topnewpage[\@makechapterhead{#2}]
   \else
    \@makechapterhead{#2}
    \@afterheading
  \fi
  \ifSFB@multisty
   \gdef\@author{}
   \gdef\@shortauthor{}
  \fi
}
\def\@schapter#1{%
 \ifSFB@addtoc
  \ifSFB@indentsty
   \ifdim\SFB@indent>\z@
    \addcontentsline{toc}{schapter}{\protect\numberline{\mbox{}}#1}
   \else
    \addcontentsline{toc}{schapter}{#1}
   \fi
  \else
   \addcontentsline{toc}{schapter}{#1}
  \fi
 \fi
 \ifSFB@multisty
  \markboth{#1}{#1}
  \gdef\SFB@endnotehead{\relax}
 \else
  \chaptermark{#1}
  \gdef\SFB@endnotehead{#1}
 \fi
 \if@twocolumn
  \@topnewpage[\@makeschapterhead{#1}]
 \else
  \@makeschapterhead{#1}
  \@afterheading
 \fi
 \normalsize
}
%
% \@startsection {NAME}{LEVEL}{INDENT}{BEFORESKIP}{AFTERSKIP}{STYLE}
%            optional * [ALTHEADING]{HEADING}
%
\ifSFB@indentsty
 \def\section{\@startsection {section}{1}{\SFB@indent}
  {-23\p@ \@plus-6.5\p@ \@minus-2\p@}{3\p@ \@plus 1\p@}
  {\normalsize\bfseries\SFB@hangraggedright}}
 \def\subsection{\@startsection{subsection}{2}{\SFB@indent}
  {-23\p@ \@plus-6.5\p@ \@minus-2\p@}{3\p@ \@plus 1\p@}
  {\normalsize\itshape\bfseries\SFB@hangraggedright}}
 \def\subsubsection{\@startsection{subsubsection}{3}{\SFB@indent}
  {-10\p@ \@plus-6.5\p@ \@minus-2\p@}{3\p@ \@plus 1\p@}
  {\normalsize\itshape\SFB@hangraggedright}}
 \def\paragraph{\@startsection{paragraph}{4}{\SFB@indent}
  {13\p@ \@plus6.5\p@ \@minus2\p@}{-0.5em}{\normalsize\bfseries\SFB@raggedright}}
 \def\subparagraph{\@startsection{subparagraph}{5}{\SFB@indent}
  {13\p@ \@plus6.5\p@ \@minus2\p@}{-0.5em}{\normalsize\itshape\SFB@raggedright}}
\else
 \def\section{\@startsection {section}{1}{\z@}
  {-23\p@ \@plus-6.5\p@ \@minus-2\p@}{3\p@ \@plus 1\p@}{\normalsize\bfseries\centering}}
 \def\subsection{\@startsection{subsection}{2}{\z@}
  {-23\p@ \@plus-6.5\p@ \@minus-2\p@}{3\p@ \@plus 1\p@}{\normalsize\itshape\bfseries\centering}}
 \def\subsubsection{\@startsection{subsubsection}{3}{\z@}
  {-10\p@ \@plus-6.5\p@ \@minus-2\p@}{3\p@ \@plus 1\p@}{\normalsize\itshape\centering}}
 \def\paragraph{\@startsection{paragraph}{4}{\z@}
  {13\p@ \@plus6.5\p@ \@minus2\p@}{-0.5em}{\normalsize\bfseries}}
 \def\subparagraph{\@startsection{subparagraph}{5}{\z@}
  {13\p@ \@plus6.5\p@ \@minus2\p@}{-0.5em}{\normalsize\itshape}}
\fi
\def\SFB@hangraggedright{\rightskip\@flushglue \let\\=\newline}
\def\SFB@raggedright{\rightskip\@flushglue \let\\=\@centercr
 \parindent=\SFB@indent}
%
% Default initializations of \...mark commands
%
%\def\chaptermark#1{}
\newcommand*\chaptermark[1]{}
\setcounter{secnumdepth}{3}
%
% APPENDIX
%
\newif\ifSFB@appendix
\def\appendix{\par\clearpage
% \small
 \SFB@appendixtrue
 \setcounter{chapter}{0}
 \setcounter{section}{0}
% set tocdepth to chapter heads only whether multi-author or single-author
 \addtocontents{toc}{\protect\setcounter{tocdepth}{0}}
 \def\@chapapp{Appendix}
 \def\thesection{A\thechapter.\arabic{section}}
 \def\thetable  {A\thechapter.\@arabic\c@table}
 \def\thefigure {A\thechapter.\@arabic\c@figure}
}

%    ****************************************
%    *                LISTS                 *
%    ****************************************
%
\ifSFB@indentsty
 \ifdim \SFB@indent=\z@ \setlength\leftmargini{1em}
                  \else \setlength\leftmargini{\SFB@indent}
              \fi \else \setlength\leftmargini{1em}
\fi
\setlength\leftmarginii{1em}
\setlength\leftmarginiii{1em}
\setlength\leftmarginiv{1em}
\setlength\leftmarginv{1em}
\setlength\leftmarginvi{1em}
\leftmargin\leftmargini
\setlength\labelsep{0.5em}
\labelwidth\leftmargini \advance\labelwidth-\labelsep
\def\@listI{\leftmargin\leftmargini
 \parsep    \z@ \@plus 2\p@
 \partopsep \z@ \@plus 1\p@
 \topsep  6.5\p@ \@plus 3.25\p@ \@minus 1\p@%
 \itemsep   \z@ \@plus.1\p@
 \listparindent \parindent
}
\let\@listi\@listI
\@listi
\def\@listii{\leftmargin\leftmarginii
 \labelwidth\leftmarginii \advance\labelwidth-\labelsep
 \parsep    \z@ \@plus 2\p@
 \partopsep \z@ \@plus 1\p@
 \topsep 3.25\p@ \@plus .5\p@ \@minus 1\p@%
 \itemsep   \z@ \@plus.1\p@
}
\def\@listiii{\leftmargin\leftmarginiii
 \labelwidth\leftmarginiii \advance\labelwidth-\labelsep
 \parsep    \z@ \@plus 2\p@
 \partopsep \z@ \@plus 1\p@
 \topsep 3.25\p@ \@plus .5\p@ \@minus 1\p@%
 \itemsep   \z@ \@plus.1\p@
}
\def\@listiv{\leftmargin\leftmarginiv
 \labelwidth\leftmarginiv \advance\labelwidth-\labelsep}
\def\@listv{\leftmargin\leftmarginv
 \labelwidth\leftmarginv  \advance\labelwidth-\labelsep}
\def\@listvi{\leftmargin\leftmarginvi
 \labelwidth\leftmarginvi \advance\labelwidth-\labelsep}

%    ****************************************
%    *           LIST ENVIRONMENTS          *
%    ****************************************
%
%
% ENUMERATE -- with optional argument to set left margin
%
\def\makeRRlabel#1{\hss\llap{#1}}

\def\enumerate{\ifnum \@enumdepth >3 \@toodeep \else
  \advance\@enumdepth \@ne
  \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
 \fi
 \@ifnextchar [{\@enumeratetwo}{\@enumerateone}%
}
\def\@enumeratetwo[#1]{%
 \list{\csname label\@enumctr\endcsname}%
  {\settowidth\labelwidth{#1}%
   \leftmargin\labelwidth \advance\leftmargin\labelsep
   \usecounter{\@enumctr}%
   \let\makelabel\makeRRlabel}%
}
\def\@enumerateone{%\listsize
 \list{\csname label\@enumctr\endcsname}%
  {\usecounter{\@enumctr}%
   \ifSFB@indentsty
    \ifdim \SFB@indent=\z@ \leftmargin 3em % overrides \leftmargini,ii,iii...
                 \fi \else \leftmargin 3em
   \fi
   \let\makelabel\makeRRlabel}}

\renewcommand\theenumi{{\rm (\roman{enumi})}}
\renewcommand\theenumii{{\rm (\alph{enumii})}}
\renewcommand\theenumiii{{\rm \arabic{enumiii}.}}
\renewcommand\theenumiv{{\rm \Alph{enumiv}.}}

\newcommand\labelenumi{\theenumi}
\newcommand\labelenumii{\theenumii}
\newcommand\labelenumiii{\theenumiii}
\newcommand\labelenumiv{\theenumiv}

\renewcommand\p@enumii{\theenumi}
\renewcommand\p@enumiii{\theenumi(\theenumii)}
\renewcommand\p@enumiv{\p@enumiii\theenumiii}
%
% ITEMIZE
%
\def\itemize{\ifnum \@itemdepth >3 \@toodeep \else
  \advance\@itemdepth \@ne
  \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
%  \listsize
  \list{\csname\@itemitem\endcsname}%
   {\def\makelabel##1{\hss\llap{##1}}}
 \fi
}
\newcommand\labelitemi{$\bullet$}
\newcommand\labelitemii{\bfseries --}
\newcommand\labelitemiii{$\circ$}
\newcommand\labelitemiv{$\diamond$}
%
% DESCRIPTION
%
\newcommand*\descriptionlabel[1]{\hspace\labelsep\bfseries #1}
\def\description{%\listsize
 \list{}{\labelwidth\z@
%  \leftmargin 2em \advance\leftmargin\labelsep
  \leftmargin 3pc
  \itemindent-\leftmargin
  \let\makelabel\descriptionlabel
 }}
\let\enddescription\endlist
%
% EXERCISES
%
\newcounter{ex@bean}
\def\exerciselist{\@ifnextchar [{\@exerciselisttwo}{\@exerciselistone}}
\def\@exerciselistone{\ifnum \@enumdepth >3 \@toodeep \else
  \advance\@enumdepth \@ne
  \def\exerciselabel##1{\rm \thechapter.##1\hss}
  \list{\arabic{ex@bean}}%
       {\usecounter{ex@bean}%
        \leftmargin 3pc
        \labelwidth \leftmargin
        \addtolength{\labelwidth}{-\labelsep}
  \let\makelabel\exerciselabel}%
\fi}
\def\@exerciselisttwo[#1]{\ifnum \@enumdepth >3 \@toodeep \else
  \advance\@enumdepth \@ne
  \def\exerciselabel##1{\rm #1.##1\hss}
  \list{\arabic{ex@bean}}%
       {\usecounter{ex@bean}%
        \leftmargin 3pc
        \labelwidth \leftmargin
        \addtolength{\labelwidth}{-\labelsep}
  \let\makelabel\exerciselabel}%
\fi}
\let\endexerciselist=\endlist

\def\exercises{\section*{Exercises}
\markright{Exercises}
\exerciselist
\setcounter{equation}{0}
\def\theequation{E\thechapter.\arabic{equation}}
}
\let\endexercises=\endexerciselist
\let\exercise=\item

%    ****************************************
%    *         OTHER ENVIRONMENTS           *
%    ****************************************
%
% VERSE
%
\def\verse{\let\\=\@centercr
  \list{}{\itemsep\z@ \itemindent -1em\listparindent \itemindent
          \rightmargin\z@
          \leftmargin\SFB@indent\advance\leftmargin 1em}\item[]\smallish}
\let\endverse=\endlist
%
% QUOTATION
%
\def\quotation{\list{}{\leftmargin\SFB@indent\rightmargin\z@}\item[]\smallish}
\let\endquotation=\endlist
%
% QUOTE
%
\def\quote{\list{}{\leftmargin\SFB@indent \rightmargin\z@}\item[]\smallish}
\let\endquote=\endlist
%
% INDENTED (for use in title pages)
%
\def\indented{\list{}{\leftmargin\SFB@indent
 \listparindent\z@\rightmargin\z@}\raggedright\item[]}
\let\endindented=\endlist
%
% ARRAY AND TABULAR
%
\setlength\arraycolsep{5\p@}
\setlength\tabcolsep{6\p@}
\setlength\arrayrulewidth{.5\p@}
\setlength\doublerulesep{2\p@}
%
% TABBING
%
\tabbingsep\labelsep
%
% FRAMEBOX
%
\setlength\fboxsep{3\p@}
\setlength\fboxrule{.5\p@}
%
% THEOREM
%
\def\@begintheorem#1#2{\par\addvspace{12\p@}
 \list{}{\leftmargin\z@\rightmargin\leftmargin}%
 \ifSFB@indentsty
  \item[]\hspace*{\SFB@indent}{\bfseries #1\ #2 }\itshape
  \ifdim \SFB@indent=\z@ \leftmarginii 3em \else \leftmarginii \SFB@indent \fi
 \else
  \item[]{\bfseries #1\ #2 }\itshape
  \leftmarginii 3em
 \fi}
\def\@opargbegintheorem#1#2#3{\par\addvspace{12\p@}
 \list{}{\leftmargin\z@\rightmargin\leftmargin}%
 \ifSFB@indentsty
  \item[]\hspace*{\SFB@indent}{\bfseries #1\ #2 (#3) }\itshape
  \ifdim \SFB@indent=\z@ \leftmarginii 3em \else \leftmarginii \SFB@indent \fi
 \else
  \item[]{\bfseries #1\ #2 (#3) }\itshape
  \leftmarginii 3em
 \fi}
\def\@endtheorem{\endlist}
%
% PROOFs
%
\def\proof{\par\addvspace{13\p@}
 \list{}{\leftmargin\z@\rightmargin\leftmargin}%
 \ifSFB@indentsty
  \item[]\hspace*{\SFB@indent}{\itshape Proof\ }%
  \ifdim \SFB@indent=\z@ \leftmarginii 3em \else \leftmarginii \SFB@indent \fi
 \else
  \item[]{\itshape Proof\ }%
  \leftmarginii 3em
 \fi}
\def\endproof{\hspace*{1em \@plus 1000fil}\nolinebreak\proofbox\endlist}
\@namedef{proof*}{\par\addvspace{13\p@}
 \list{}{\leftmargin\z@\rightmargin\leftmargin}%
 \ifSFB@indentsty
  \item[]\hspace*{\SFB@indent}{\itshape Proof\ }%
  \ifdim \SFB@indent=\z@ \leftmarginii 3em \else \leftmarginii \SFB@indent \fi
 \else
  \item[]{\itshape Proof\ }%
  \leftmarginii 3em
 \fi}
\@namedef{endproof*}{\endlist}
\def\proofbox{\begin{picture}(6.5,6.5)%
 \put(0,0){\framebox(6.5,6.5){}}\end{picture}}

%    ****************************************
%    *        CHAPTERS AND SECTIONS         *
%    ****************************************
%
% DEFINE COUNTERS:
%
\newcounter {part}
\newcounter {chapter}
\newcounter {section}[chapter]
\newcounter {subsection}[section]
\newcounter {subsubsection}[subsection]
\newcounter {paragraph}[subsubsection]
\newcounter {subparagraph}[paragraph]
%\def\thepart          {\arabic{part}}
\renewcommand \thepart {\Roman{part}}
\def\thechapter       {\arabic{chapter}}
\def\thesection       {\thechapter.\arabic{section}}
\def\thesubsection    {\thesection.\arabic{subsection}}
\def\thesubsubsection {\thesubsection .\arabic{subsubsection}}
\def\theparagraph     {\thesubsubsection.\arabic{paragraph}}
\def\thesubparagraph  {\theparagraph.\arabic{subparagraph}}
\def\@chapapp{Chapter}

%    ****************************************
%    *                 PARTS                *
%    ****************************************
%
\def\part{\cleardoublepage
 \thispagestyle{empty}
 \if@twocolumn
   \onecolumn
   \@tempswatrue
  \else \@tempswafalse
 \fi
 \secdef\@part\@spart
}
\def\@part[#1]#2{\ifnum \c@secnumdepth >-2\relax
  \refstepcounter{part}
  \ifSFB@indentsty
   \ifdim\SFB@indent>\z@
    \ifSFB@multisty
     \addcontentsline{toc}{part}{Part \thepart\quad #1}
    \else
     \addcontentsline{toc}{part}{Part \thepart\quad #1}
    \fi
   \else
     \addcontentsline{toc}{part}{Part \thepart\quad #1}
   \fi
  \else
    \addcontentsline{toc}{part}{Part \thepart\quad #1}
  \fi
  \else
    \addcontentsline{toc}{part}{#1}
  \fi
  \@mkboth{}{}
  {\ifSFB@indentsty \raggedright \else \centering \fi
   \vspace*{-\baselineskip}
   \ifnum \c@secnumdepth >-2\relax
    {\huge\bfseries \hspace*{\SFB@indent}Part \thepart}%\enskip #1
    \par
    \ifSFB@largesty \vskip 9\p@ \else \vskip 7\p@ \fi
   \else
    \par
    \vskip 2.5\baselineskip
  \fi
  \LARGE \rm \hspace*{\SFB@indent}#2\par}
  \@endpart
}


\def\@spart#1{{\ifSFB@indentsty \raggedright \else \centering \fi
  \vspace*{-\baselineskip}
  \par
  \vskip 19.5\p@ % 1.5\baselineskip
  \LARGE \rm #1\par}
\@endpart}
%
% \@endpart finishes the part page
%
\def\@endpart{\cleardoublepage}

%    ****************************************
%    *         TABLE OF CONTENTS, ETC.      *
%    ****************************************
%
\newdimen\SFB@tocindent
\ifSFB@largesty \SFB@tocindent=65\p@ \else \SFB@tocindent=60\p@ \fi
% \def\numberline#1{\hbox to\@tempdima{#1\hfil}}
\def\SFB@numberline#1{\hbox to 1.15\SFB@tocindent {{\itshape Appendix #1\hfil}}}%1.15
\ifSFB@indentsty \ifdim\SFB@indent>\z@
 \def\numberline#1{\hbox to\@tempdima{\hfil#1\hspace*{0.5em}}}
 \def\SFB@numberline#1{\hspace*{\@tempdima}%
  \hbox to 1.15\SFB@tocindent {{\itshape Appendix #1\hfil}}}
\fi \fi
%
\newif\ifSFB@addtoc        \SFB@addtocfalse
\newif\ifSFB@firstTOCentry \SFB@firstTOCentrytrue
\newdimen\SFB@toclmarg
\ifSFB@multisty
 \setcounter{tocdepth}{0}
 \SFB@toclmarg 16\p@
\else
 \setcounter{tocdepth}{2}
 \SFB@toclmarg 28\p@
\fi
\ifSFB@indentsty %and
 \ifdim\SFB@indent>\z@
   \SFB@toclmarg \SFB@indent
 \fi
\fi
\def\@pnumwidth{1.55em}
\def\@tocrmarg {2.55em}
\def\@dotsep{4.5}
%
% TABLEOFCONTENTS
%
\newcommand\tableofcontents{\@restonecolfalse
 \if@twocolumn\@restonecoltrue\onecolumn\fi
 \SFB@addtocfalse
 \chapter*{Contents}
 \@starttoc{toc}
 \SFB@addtoctrue
 \if@restonecol\twocolumn\fi
}

\newcommand*\l@part[2]{\vspace{\baselineskip}%
 \addpenalty{-\@highpenalty}%
 \begingroup
  \parindent \z@ \rightskip \@pnumwidth
  \parfillskip -\@pnumwidth
  \leavevmode
  \ifSFB@multisty \else \hspace*{\SFB@toclmarg}\fi
  \ifSFB@firstTOCentry
    {\normalfont\bfseries #1} \hfil \hbox to\@pnumwidth{\hss {\normalfont\itshape page\/} #2}\par
    \global\SFB@firstTOCentryfalse
  \else
    {\normalfont\bfseries #1} \hfil \hbox to\@pnumwidth{\hss #2}\par
  \fi
  \nobreak
 \endgroup
}

\newcommand*\l@chapter[2]{\pagebreak[3]
 \vspace{3pt plus 2pt}%
 \@tempdima \SFB@toclmarg
 \begingroup
  \parindent \z@  \rightskip \@pnumwidth  \parfillskip -\@pnumwidth
  \leavevmode
  \advance \leftskip \@tempdima  \hskip -\leftskip
  \ifSFB@firstTOCentry
   {\normalfont\bfseries #1}\nobreak\hfil \nobreak\hbox to\@pnumwidth{\hss {\normalfont\itshape page\/} #2}\par
   \global\SFB@firstTOCentryfalse
  \else
   {\normalfont\bfseries #1}\nobreak\hfil \nobreak\hbox to\@pnumwidth{\hss #2}\par
  \fi
 \endgroup
}

\newcommand*\l@schapter[2]{\pagebreak[3]
 \@tempdima \SFB@toclmarg
 \begingroup
  \parindent \z@  \rightskip \@pnumwidth  \parfillskip -\@pnumwidth
  \leavevmode
  \advance \leftskip \@tempdima  \hskip -\leftskip
  \ifSFB@firstTOCentry
   {\itshape #1}\nobreak\hfil \nobreak\hbox to\@pnumwidth{\hss {\itshape page\/} #2}\par
   \global\SFB@firstTOCentryfalse
  \else
   {\itshape #1}\nobreak\hfil \nobreak\hbox to\@pnumwidth{\hss #2}\par
  \fi
 \endgroup
}

% instead of using \SFB@toclmarg, revert to 28pt throughout
% (sections not listed in multi-author designs)

\newcommand*\l@section      {\@dottedtocline{1}{28pt}{28pt}}
\newcommand*\l@subsection   {\@dottedtocline{2}{56pt}{34pt}}

% these are not used
\newcommand*\l@subsubsection{\@dottedtocline{3}{\z@}{\SFB@toclmarg}}
\newcommand*\l@paragraph    {\@dottedtocline{4}{\z@}{\SFB@toclmarg}}
\newcommand*\l@subparagraph {\@dottedtocline{5}{\z@}{\SFB@toclmarg}}
%
% LIST OF FIGURES
%
\newcommand\listoffigures{\@restonecolfalse
 \if@twocolumn\@restonecoltrue\onecolumn\fi
 \bgroup
  \chapter*{List of Illustrations}
  \normalsmall
  \setcounter{tocdepth}{1}
  \@starttoc{lof}
 \egroup
 \if@restonecol\twocolumn\fi
}
\newcommand*\l@figure{\@dottedtocline{1}{\z@}{\SFB@toclmarg}}
%
% LIST OF TABLES
%
\newcommand\listoftables{\@restonecolfalse
 \if@twocolumn\@restonecoltrue\onecolumn\fi
 \bgroup
  \chapter*{List of Tables}
  \normalsmall
  \setcounter{tocdepth}{1}
  \@starttoc{lot}
 \egroup
 \if@restonecol\twocolumn\fi
}
\let\l@table\l@figure
%
% \@dottedtocline{LEVEL}{INDENT}{NUMWIDTH}{TITLE}{PAGE} without the dots
%

\def\@dottedtocline#1#2#3#4#5{% For toc alone, all designs assume \SFB@indent=0pc
 \ifnum #1>\c@tocdepth
 \else
  \vskip \z@ \@plus .2\p@
  {\leftskip #2\relax 
   \rightskip \@tocrmarg \@plus2em % for ragged right entries
   \parfillskip -\rightskip
   \parindent #2\relax
   \@afterindenttrue
   \interlinepenalty\@M
   \leavevmode
   \@tempdima #3\relax \advance\leftskip \@tempdima \hbox{}\hskip -\leftskip
   #4\nobreak
   \hfill \nobreak
   \ifSFB@firstTOCentry
    \hbox to\@pnumwidth{\hfil\rm {\itshape page\/} #5}\par
    \global\SFB@firstTOCentryfalse
   \else
    \hbox to\@pnumwidth{\hfil\rm #5}\par
   \fi}%
 \fi
}



%    ****************************************
%    *             BIBLIOGRAPHY             *
%    ****************************************
%
\ifSFB@multisty
 \newenvironment{thebibliography}[1]%
   {\section*{Bibliography}\bibliographylist}{\endlist}
\else
 \newenvironment{thebibliography}[1]%
   {\chapter*{Bibliography}\typeout{Bibliography.}\bibliographylist}{\endlist}
\fi

\ifSFB@multisty
 \newenvironment{thereferences}[1]%
   {\section*{References}\bibliographylist}{\endlist}
\else
 \newenvironment{thereferences}[1]%
   {\chapter*{References}\typeout{References.}\bibliographylist}{\endlist}
\fi

\newcounter{dummy}
\def\bibliographylist{%
 \small%\raggedright
  \list{}{\usecounter{dummy}\labelwidth\z@
  \leftmargin 2em% \advance\leftmargin\labelsep
  \itemsep \z@ \@plus .1\p@
  \itemindent-\leftmargin}
 \parindent\z@
 \parskip\z@ \@plus .1\p@\relax
 \def\newblock{\hskip .11em \@plus .33em \@minus .07em}
 \sloppy\clubpenalty4000\widowpenalty4000
 \sfcode`\.=1000\relax
}
\let\endbibliographylist=\endlist

%    ****************************************
%    *              THE INDEX               *
%    ****************************************
%
% THE THEINDEX ENVIRONMENT
%
\newif\if@restonecol
\newenvironment{theindex}{\the@index{Index}}{\par\endthe@index}
\newenvironment{theauthorindex}{\the@index{Author index}}{\par\endthe@index}
\newenvironment{thesubjectindex}{\the@index{Subject index}}{\par\endthe@index}

\newcommand\the@index[1]{\@restonecoltrue
 \if@twocolumn\@restonecolfalse\fi
 \columnseprule \z@
 \columnsep 1pc
 \twocolumn[\vspace*{11\p@}\mbox{}\par\@makeschapterhead{#1}]
 \@mkboth{#1}{#1}
 \typeout{#1.}
 \ifSFB@indentsty
  \ifdim\SFB@indent>\z@
   \addcontentsline{toc}{schapter}{\protect\numberline{\mbox{}}#1}
  \else
   \addcontentsline{toc}{schapter}{#1}
  \fi
 \else
  \addcontentsline{toc}{schapter}{#1}
 \fi
 \thispagestyle{plain}
 \footnotesize\raggedright
 \parindent\z@
 \parskip\z@ \@plus.3\p@\relax
 \let\item=\@idxitem
}
\def\endthe@index{\if@restonecol\onecolumn\else\clearpage\fi}

\newcommand\@idxitem{\par\hangindent 2em}
\newcommand\subitem{\par\hangindent 3em \hspace*{1em}}
\newcommand\subsubitem{\par\hangindent 4em \hspace*{2em}}
\newcommand\indexspace{\par \vskip 9\p@ \@plus 5\p@ \@minus 3\p@\relax}

%    ****************************************
%    *        FOOTNOTES with SYMBOLS        *
%    ****************************************
%
\newskip\@footindent
\@footindent=1em

\renewcommand\footnoterule{\kern-3\p@ \hrule width 0\columnwidth \kern 2.6\p@}
\@addtoreset{footnote}{page}

\long\def\@makefntext#1{\@setpar{\@@par\@tempdima \hsize
 \advance\@tempdima-\@footindent
 \parshape \@ne \@footindent \@tempdima}\par
 \noindent \hbox to \z@{\hss\@thefnmark\hspace{0.5em}}#1}

\renewcommand\thefootnote{\mbox{$\fnsymbol{footnote}$}}
\def\@makefnmark{\hbox{\@thefnmark}}

\def\@fnsymbol#1{\ifcase#1\or \dagger\or \ddagger\or
   \S \or \P \or \|\or \dagger\dagger
   \or \ddagger\ddagger\or \S\S\or \P\P\or \|\|\else *\fi\relax}
%
% MINIPAGE
%
\skip\@mpfootins = 4\p@ \@plus 1\p@ \@minus .1\p@  % top of first minipage footnote.
\def\thempfootnote{\alph{mpfootnote}}
\def\@makempfnmark{\hbox{$^{\@thefnmark}$}}
%
\long\def\@makempfntext#1{\@setpar{\@@par\@tempdima \hsize
 \advance\@tempdima-\@footindent
 \parshape \@ne \@footindent \@tempdima}\par
 \noindent \hbox to \z@{\hss$^{\@thefnmark}$\hspace{0.5em}}#1} % v.01.10 SFB
%
% redefine minipage to reset footnotemark as well as text and counters...
%
%\def\@iminipage[#1]#2{\leavevmode \@pboxswfalse
% \if #1b\vbox
%  \else \if #1t\vtop
%         \else \ifmmode \vcenter
%                \else \@pboxswtrue $\vcenter
%               \fi
%        \fi
% \fi\bgroup
% \hsize #2\textwidth\hsize \columnwidth\hsize
% \@parboxrestore
% \def\@mpfn{mpfootnote}
% \def\thempfn{\thempfootnote}\c@mpfootnote\z@
% \let\@makefnmark\@makempfnmark % v.01.03 SFB
% \let\@footnotetext\@mpfootnotetext
% \let\@listdepth\@mplistdepth \@mplistdepth\z@
% \@minipagerestore\global\@minipagetrue
% \everypar{\global\@minipagefalse\everypar{}}}

\def\@iiiminipage#1#2[#3]#4{% from latex.ltx
  \leavevmode
  \@pboxswfalse
  \setlength\@tempdima{#4}%
  \def\@mpargs{{#1}{#2}[#3]{#4}}%
  \setbox\@tempboxa\vbox\bgroup
    \color@begingroup
      \hsize\@tempdima
      \textwidth\hsize \columnwidth\hsize
      \@parboxrestore
      \def\@mpfn{mpfootnote}\def\thempfn{\thempfootnote}\c@mpfootnote\z@
      \let\@makefnmark\@makempfnmark % from v1.2 ajw
      \let\@footnotetext\@mpfootnotetext
      \let\@listdepth\@mplistdepth \@mplistdepth\z@
      \@minipagerestore\global\@minipagetrue %% \global added 24 May 89
      \everypar{\global\@minipagefalse\everypar{}}}

\long\def\@mpfootnotetext#1{\global\setbox\@mpfootins
 \vbox{\unvbox\@mpfootins
  \footnotesize
  \hsize\columnwidth \@parboxrestore
  \edef\@currentlabel{\csname p@mpfootnote\endcsname\@thefnmark}
  \@makempfntext{\rule{\z@}{\footnotesep}\ignorespaces #1\strut}}}

%       ****************************************
%       *               ENDNOTES               *
%       ****************************************
%
\newcounter{endnote}[chapter] \def\theendnote{\arabic{endnote}}
\newdimen\endnotesep
\newwrite\@enotes
\newif\if@enotesopen          \global\@enotesopenfalse
\newif\ifSFB@firstendnote     \global\SFB@firstendnotefalse

\def\@makeenmark{\hbox{$^{\@theenmark}$}}

\def\endnote{%
 \ifSFB@multisty \SFB@firstendnotefalse
        \else \ifnum \c@endnote = \z@ \SFB@firstendnotetrue
                                \else \SFB@firstendnotefalse \fi
 \fi
 \@ifnextchar[{\@xendnote
  }{\stepcounter{endnote}%
    \xdef\@theenmark{\theendnote}%
   }%
 \@endnotemark
 \@endnotetext
}
\def\@xendnote[#1]{\begingroup \c@endnote=#1\relax
  \xdef\@theenmark{\theendnote}\endgroup
}
\let\@doanenote=0
\let\@endanenote=0
\def\@openenotes{\immediate\openout\@enotes=\jobname.ent\relax
 \global\@enotesopentrue
}
\gdef\SFB@endnotehead{\relax}
\long\def\@endnotetext#1{%
 \if@enotesopen \else \@openenotes \fi
 \ifSFB@firstendnote
  \addtoendnotes{\protect\endnoteheading*{\SFB@endnotehead}}%
  \addtoendnotes{\protect\noindent}%
 \fi
 \ifSFB@multisty\else
  \addtoendnotes{\protect\mark{\thepage}}%
 \fi
 \immediate\write\@enotes{\@doanenote{\@theenmark}}%
 \begingroup
  \def\next{#1}%
  \newlinechar='40
  \immediate\write\@enotes{\meaning\next}%
 \endgroup
 \immediate\write\@enotes{\@endanenote}%
 \edef\@currentlabel{\csname p@endnote\endcsname\@theenmark}%
}
\long\def\addtoendnotes#1{%
 \if@enotesopen \else \@openenotes \fi
 \begingroup
  \newlinechar='40
  \let\protect\string
  \immediate\write\@enotes{#1}%
 \endgroup
}
\def\endnotemark{\@ifnextchar [{\@xendnotemark
 }{\stepcounter{endnote}%
   \xdef\@theenmark{\theendnote}}%
 \@endnotemark
}
\def\@xendnotemark[#1]{\begingroup
  \c@endnote #1\relax
  \xdef\@theenmark{\theendnote}\endgroup
}
\def\@endnotemark{\leavevmode
 \ifhmode \edef\@x@sf{\the\spacefactor}\fi
 \@makeenmark
 \ifhmode\spacefactor\@x@sf\fi\relax
}
\def\endnotetext{\@ifnextchar [{\@xendnotenext
  }{\xdef\@theenmark{\theendnote}}%
 \@endnotetext
}
\def\@xendnotenext[#1]{\begingroup
  \c@endnote=#1\relax \xdef\@theenmark{\theendnote}\endgroup
}
\ifSFB@multisty
 \def\enoteheading{\section*{Notes}}
\else
 \def\enoteheading{\chapter*{Notes}\leavevmode\par\vskip-\baselineskip}
\fi
\def\enoteformat{\raggedright
 \ifSFB@indentsty
  \@tempdima = 3pc
 \else
  \@tempdima = 1.5em
 \fi
 \leftskip \@tempdima \parindent=1em%
 \leavevmode
 \hskip-\@tempdima
 \hskip-\parindent
 \hbox to \@tempdima {\hfil\@theenmark\hspace*{0.5em}}%
}
\ifSFB@multisty\else
 \def\SFB@enoteheadline{Notes to pp. \firstmark--\botmark}
\fi
\def\theendnotes{\immediate\closeout\@enotes
 \global\@enotesopenfalse
 \begingroup
  \makeatletter
  \def\@doanenote##1##2>{\def\@theenmark{##1}\par\begingroup\enoteformat}%
  \def\@endanenote{\par\endgroup}%
  \def\ETC.{\@warning{[CUPBOOK] Some long endnotes will be truncated}
   \def\ETC.{\relax}}
  \enoteheading
  \ifSFB@multisty\else % redefine marking for running heads
   \def\chaptermark##1{}
   \def\leftmark{\SFB@enoteheadline}
   \def\rightmark{\SFB@enoteheadline}
  \fi
  \enotesize
  \noindent
  \@input{\jobname.ent}%
  \ifSFB@multisty\else\clearpage\fi
 \endgroup
}
\ifSFB@indentsty
 \def\endnoteheading{\@startsection {endnoteheading}{1}{\z@}
  {-11\p@ \@plus-3.25\p@ \@minus-1\p@}{3\p@ \@plus 1\p@}{\normalsize\bfseries\raggedright}}
\else
 \def\endnoteheading{\@startsection {endnoteheading}{1}{\z@}
  {-11\p@ \@plus-3.25\p@ \@minus-1\p@}{3\p@ \@plus 1\p@}{\normalsize\bfseries\centering}}
\fi
%    ****************************************
%    *         FIGURES AND TABLES           *
%    ****************************************
%
% Float placement parameters.
%
\setcounter{topnumber}{2}
\renewcommand\topfraction{0.9}
\setcounter{bottomnumber}{2}
\renewcommand\bottomfraction{0.5}
\setcounter{totalnumber}{3}
\renewcommand\textfraction{0.05}
\renewcommand\floatpagefraction{0.95}
\setcounter{dbltopnumber}{2}
\renewcommand\dbltopfraction{0.9}
\renewcommand\dblfloatpagefraction{0.8}
%
% \@makecaption{NUMBER}{TEXT} : Macro to make a figure or table caption.
%
\long\def\make@table@caption#1#2{\vskip 10\p@%
  \setbox\@tempboxa\hbox{{\rm #1.\hspace{0.5em}\itshape #2}}%
  \ifdim \wd\@tempboxa >\hsize
    {\ifSFB@indentsty \raggedright\else \centering\fi
    \rm #1.\hspace{0.5em}{\itshape #2}\par}%
  \else
    \ifSFB@indentsty
      \hbox to\hsize{\box\@tempboxa\hfill}\par
    \else
      \hbox to\hsize{\hfil\box\@tempboxa\hfil}\par
    \fi
  \fi
  \vspace*{2.5\p@}\par
}
%
\long\def\make@figure@caption#1#2{\vskip 10\p@
 \setbox\@tempboxa\hbox{{\small\rm #1.\hspace{0.5em}#2}}
 \ifdim \wd\@tempboxa >\hsize
   {\small\rm #1.\hspace{0.5em}#2\par}
  \else
   \ifSFB@indentsty
    \hbox to\hsize{\box\@tempboxa\hfill}\par
   \else
    \hbox to\hsize{\hfil\box\@tempboxa\hfil}\par
   \fi
 \fi
}
%
% Float control
%
\newdimen\SFB@floatwidth

\def\SFB@float{\SFB@floatwidth \textwidth
 \addtolength{\SFB@floatwidth}{-\SFB@floatindent}
 \hspace*{\SFB@floatindent}\minipage{\SFB@floatwidth}%
 \ifSFB@indentsty\raggedright\else\centering\fi\small}
\def\endSFB@float{\endminipage}
\def\SFB@widefloat{\minipage{\textwidth}\raggedright\small}
\let\endSFB@widefloat=\endSFB@float
%
% FIGURE
%
\newcounter{figure}[chapter]
\def\thefigure{\thechapter.\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{Fig.\ \thefigure}

\def\figure{\let\@makecaption=\make@figure@caption
 \SFB@floatindent=\SFB@indent
 \@ifnextchar[{\SFB@figone}{\SFB@figzero}}
\def\SFB@figone[#1]{\@xfloat{figure}[#1]\SFB@float}
\edef\SFB@figzero{\noexpand\@xfloat{figure}[\fps@figure]\noexpand\SFB@float}
\def\endfigure{\endSFB@float\end@float}

\@namedef{figure*}{\let\@makecaption=\make@figure@caption
 \@ifnextchar[{\SFB@widefigone}{\SFB@widefigzero}}
\def\SFB@widefigone[#1]{\@xfloat{figure}[#1]\SFB@widefloat}
%\edef\SFB@widefigzero{\noexpand\@xfloat{figure}[p]\noexpand\SFB@widefloat}
\edef\SFB@widefigzero{\noexpand\@xfloat{figure}[\fps@figure]\noexpand
  \SFB@widefloat}
\@namedef{endfigure*}{\endSFB@widefloat\end@float}
%
% TABLE
%
\newcounter{table}[chapter]
\def\thetable{\thechapter.\@arabic\c@table}
\def\fps@table{tp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{Table \thetable}

\newenvironment{table}{%
  \let\@makecaption=\make@table@caption
  \ifSFB@indentsty
    \ifdim\SFB@indent>\z@
      \ifSFB@largesty
        \SFB@floatindent=\SFB@indent
      \else
        \SFB@floatindent=\z@ %\typeout{CUP8a tables}%
      \fi
    \fi
  \fi
  \@ifnextchar[{\SFB@tabone}{\SFB@tabzero}%
  }%
  {\endSFB@float\end@float}

\def\SFB@tabone[#1]{\@xfloat{table}[#1]\SFB@float}
\edef\SFB@tabzero{%
  \noexpand\@xfloat{table}[\fps@table]\noexpand\SFB@float}

\newenvironment{table*}{%
  \let\@makecaption=\make@table@caption
  \let\SFB@currenthline=\SFB@fullhline
  \@ifnextchar[{\SFB@widetabone}{\SFB@widetabzero}%
  }%
  {\endSFB@widefloat\end@float}

\def\SFB@widetabone[#1]{\@xfloat{table}[#1]\SFB@widefloat}
%\edef\SFB@widetabzero{\noexpand\@xfloat{table}[p]\noexpand\SFB@widefloat}
\edef\SFB@widetabzero{\noexpand\@xfloat{table}[\fps@table]\noexpand\SFB@widefloat}

%    ****************************************
%    *                TITLE                 *
%    ****************************************
%
% TITLEPAGE
%
\newif\ifSFB@titlepage
\def\titlepage{\@restonecolfalse
 \if@twocolumn\@restonecoltrue\onecolumn
  \else \newpage
 \fi
 \SFB@titlepagetrue
 \thispagestyle{empty}%
}
\def\endtitlepage{\if@restonecol\twocolumn \else \newpage \fi
  \SFB@titlepagefalse}
%
\def\maketitle{\openin1 \jobname.ttl
 \ifeof1
  \typeout{No file \jobname.ttl.}
  \begin{titlepage}
   \ifSFB@indentsty \begin{indented}
              \else \begin{center}
   \fi
   \ifSFB@largesty \vspace*{4\p@} \else \vspace*{2\p@} \fi
   \huge \@title \par
   \if\@subtitle\empty\else \vskip 9\p@ \Large\@subtitle \par \fi
   \vspace{28\p@}
   {\large
     \ifSFB@multisty {\itshape Edited by} \\ \fi
     \ifSFB@indentsty \begin{author@tabular}[t]{@{}l@{}}
                \else \begin{author@tabular}[t]{c}
      \fi \@author
     \end{author@tabular}\par}
   \vfill
%   \large CAMBRIDGE UNIVERSITY PRESS \\[2\p@]
%     {\itshape Cambridge \\
%          New York \hspace*{1em}
%          Port Chester\hspace*{1em}
%          Melbourne\hspace*{1em}
%          Sydney}
   \ifSFB@indentsty \end{indented}
              \else \end{center}
   \fi
  \end{titlepage}
  \cleardoublepage
 \else
  \closein1 \relax\@@input \jobname.ttl
 \fi
 \setcounter{footnote}{0} % Reset definitions
 \let\thanks\relax
 \gdef\@thanks{}
 \gdef\@author{}
 \gdef\@shortauthor{}
 \gdef\@title{}
 \let\maketitle\relax
}
\gdef\@title{\mbox{}}
\def\title{\@ifnextchar[ {\@titletwo}{\@titleone}}
\def\@titletwo[#1]#2{\gdef\@title{#2}\gdef\@subtitle{#1}}
\def\@titleone#1{\gdef\@title{#1}\gdef\@subtitle{}}
\def\subtitle#1{\gdef\@subtitle{#1}}
\gdef\@subtitle{}
\def\halftitle#1{\gdef\@halftitle{#1}}
\gdef\@halftitle{\@title}
%
\gdef\@author{\mbox{}}
\gdef\@shortauthor{}
\def\author{\@ifnextchar [{\@authortwo}{\@authorone}}
\def\@authortwo[#1]#2{\gdef\@author{#2}\gdef\@shortauthor{#1}}
\def\@authorone#1{\gdef\@author{#1}\gdef\@shortauthor{}}

\def\author@tabular{\def\@halignto{}\@authortable}
\let\endauthor@tabular=\endtabular
\def\@authortable{\leavevmode \hbox \bgroup $\let\@acol=\@tabacol
 \let\@classz=\@tabclassz \let\@classiv=\@tabclassiv
 \ifSFB@titlepage \let\\=\SFBauthor@tabcrone
            \else \let\\=\author@tabcrone
 \fi
 \ignorespaces \@tabarray}
\def\author@tabcrone{{\ifnum0=`}\fi\@xtabularcr\enotesize\itshape
 \ifSFB@titlepage \let\\=\SFBauthor@tabcrtwo
            \else \let\\=\author@tabcrtwo
 \fi
 \ignorespaces}
\def\author@tabcrtwo{{\ifnum0=`}\fi\@xtabularcr[-3\p@]\enotesize\itshape
 \ifSFB@titlepage \let\\=\SFBauthor@tabcrtwo
            \else \let\\=\author@tabcrtwo
 \fi
 \ignorespaces}
\def\SFBauthor@tabcrone{{\ifnum0=`}\fi\@xtabularcr[-2\p@]\footnotesize\itshape
 \let\\=\SFBauthor@tabcrtwo\ignorespaces}
\def\SFBauthor@tabcrtwo{{\ifnum0=`}\fi\@xtabularcr[-5\p@]\footnotesize\itshape
 \let\\=\SFBauthor@tabcrtwo\ignorespaces}
\def\and{\end{author@tabular}\vskip 6\p@\par
 \ifSFB@indentsty \begin{author@tabular}[t]{@{}l@{}}
            \else \begin{author@tabular}[t]{c}
 \fi}

%    ****************************************
%    *            PAGE STYLES               *
%    ****************************************
%
% Initializes TeX's marks
%
\mark{{}{}}
%
% centred \ps@plain and \ps@empty defined in LATEX.TEX
%
\ifSFB@indentsty
 \def\ps@plain{\let\@mkboth=\@gobbletwo
  \def\@oddfoot {\listsize\rm\hfill\thepage}
  \def\@evenfoot{\listsize\rm\thepage\hfill}
  \def\@oddhead {}
  \def\@evenhead{}}
\fi
%
% Definition of 'headings' page style
%
\def\ps@headings{\let\@mkboth=\markboth
 \def\@oddfoot {}
 \def\@evenfoot{}
 \ifSFB@indentsty
  \ifdim\SFB@indent=\z@
   \def\@oddhead {\listsize\itshape \rightmark \hfill \rm \thepage}
   \def\@evenhead{\listsize\rm \thepage \hfill \itshape \leftmark}
  \else
   \def\@oddhead {\listsize
                  \hspace*{\SFB@indent}\itshape \rightmark \hfil \rm\thepage}
   \def\@evenhead{\listsize
                  \makebox[\z@][l]{\rm \thepage}\hspace*{\SFB@indent}\itshape
                  \leftmark \hfill}
  \fi
 \else
  \def\@oddhead {\listsize
                 \hfil \itshape \rightmark \hfil \makebox[\z@][r]{\rm \thepage}}
  \def\@evenhead{\listsize
                 \makebox[\z@][l]{\rm \thepage}\hfil \itshape \leftmark \hfil}
 \fi
 \ifSFB@multisty
  \def\chaptermark##1{}
  \def\sectionmark##1{}
 \else
  \def\chaptermark##1{\markboth{##1}{##1}}
  \def\sectionmark##1{\markright{\ifnum \c@secnumdepth >\z@
   \thesection\hspace{0.5em}\fi ##1}}%
 \fi
}
%
% Definition of 'myheadings' page style.
%
\def\ps@myheadings{\let\@mkboth=\@gobbletwo
 \def\@oddfoot {}
 \def\@evenfoot{}
 \def\@oddhead {\listsize\hfil \itshape\rightmark \hfil \rm\thepage}
 \def\@evenhead{\listsize\rm \thepage\hfil\itshape\leftmark\hfil}
 \def\chaptermark##1{}
 \def\sectionmark##1{}
 \def\subsectionmark##1{}}

%    ****************************************
%    *            MISCELLANEOUS             *
%    ****************************************
%
% DATE
%
\def\today{\ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \space\number\day, \number\year}
%
% EQUATION and EQNARRAY -- put here because it must follow \chapter definition
%
\@addtoreset{equation}{chapter}
\def\theequation{\thechapter.\arabic{equation}}
% \jot = 3\p@ % Extra space added between lines of an eqnarray environment
%
% Flush left / indented equations
%
% FLEQN DOCUMENT-STYLE OPTION - released 9 March 1987
%    for LaTeX version 2.09
% Copyright (C) 1987 by Leslie Lamport
%
\ifSFB@indentsty
 \def\[{\relax\ifmmode\@badmath\else\begin{trivlist}\item[]\leavevmode
  \hbox to\linewidth\bgroup$ \displaystyle \hskip\SFB@indent\bgroup\fi}
 \def\]{\relax\ifmmode \egroup $\hfil \egroup \end{trivlist}%
  \else \@badmath \fi}
 \def\equation{\refstepcounter{equation}\trivlist \item[]\leavevmode
  \hbox to\linewidth\bgroup $ \displaystyle \hskip\SFB@indent}
 \def\endequation{$\hfil \displaywidth\linewidth\@eqnnum\egroup \endtrivlist}
 \def\eqnarray{\stepcounter{equation}\let\@currentlabel=\theequation
  \global\@eqnswtrue
  \global\@eqcnt\z@\tabskip\SFB@indent\let\\=\@eqncr
  \abovedisplayskip\topsep\ifvmode\advance\abovedisplayskip\partopsep\fi
  \belowdisplayskip\abovedisplayskip
  \belowdisplayshortskip\abovedisplayskip
  \abovedisplayshortskip\abovedisplayskip
  $$\halign
   to \linewidth\bgroup\@eqnsel\hskip\@centering$\displaystyle\tabskip\z@
   {##}$&\global\@eqcnt\@ne \hskip 2\arraycolsep \hfil${##}$\hfil
   &\global\@eqcnt\tw@ \hskip 2\arraycolsep $\displaystyle{##}$\hfil
    \tabskip\@centering&\llap{##}\tabskip\z@\cr}
 \def\endeqnarray{\@@eqncr\egroup
  \global\advance\c@equation\m@ne$$\global\@ignoretrue}%
\fi

%    ****************************************
%    *            CUP SPECIALS              *
%    ****************************************
%
% redefinition of \cleardoublepage to get blank empty pages
%
\def\clearemptypage{\clearpage
 \if@twoside
  \ifodd\c@page
   \else
    \thispagestyle{empty}
    \mbox{}\newpage
    \if@twocolumn
      \hbox{}\newpage
    \fi
  \fi
 \fi
}
\let\cleardoublepage=\clearemptypage
%
% redefinition of sections to get en space after chapter number
%
\def\@sect#1#2#3#4#5#6[#7]#8{%
 \ifnum #2>\c@secnumdepth % LEVEL -- is heading to be numbered?
  \def\@svsec{}%
 \else
  \refstepcounter{#1}
  \edef\@svsec{\csname the#1\endcsname\hskip 0.5em}
 \fi
 \@tempskipa #5\relax % AFTERSKIP (-ve indicates a run-in heading)
 \ifdim \@tempskipa>\z@
  \begingroup #6\relax
   \@hangfrom{\hskip #3\relax\@svsec}{\interlinepenalty \@M #8\par}
  \endgroup
  \csname #1mark\endcsname{#7}%
  \addcontentsline{toc}{#1}{\ifnum #2>\c@secnumdepth \else
   \protect\numberline{\csname the#1\endcsname}\fi #7}
 \else
  \def\@svsechd{#6\hskip #3\@svsec #8%
   \csname #1mark\endcsname{#7}%
   \addcontentsline{toc}{#1}{\ifnum #2>\c@secnumdepth \else
    \protect\numberline{\csname the#1\endcsname}\fi#7}}%
 \fi
 \@xsect{#5}}
%
% redefinition of \hline to get extra space
%
%\def\hline{\noalign{\ifnum0=`}\fi \vskip 6\p@
% \hrule \@height \arrayrulewidth \vskip 6\p@
% \futurelet \@tempa\@xhline}
%\def\@xhline{\ifx\@tempa\hline \vskip -12\p@
% \vskip \doublerulesep \fi \ifnum0=`{\fi}}
\def\SFB@fullhline{\noalign{\ifnum0=`}\fi \vskip 3\p@
 \hrule \@height\arrayrulewidth width\textwidth
 \vskip 3\p@
 \futurelet \@tempa\@xhline}
\def\SFB@hline{\noalign{\ifnum0=`}\fi
  \vskip 3\p@
  \hrule \@height \arrayrulewidth
  \vskip 3\p@
  \futurelet \@tempa\@xhline}
\let\SFB@currenthline=\SFB@hline
%
% redefinition of tabular to get rid of vertical lines in tables
%
\def\tabular{\def\@halignto{}%
 \let\hline=\SFB@currenthline
 \def\@xhline{\ifx\@tempa\hline
   \vskip -6\p@
   \vskip \doublerulesep
  \fi
  \ifnum0=`{\fi}}%
 \def\@arrayrule{\@addtopreamble{\hskip -.5\arrayrulewidth
%                                  \vrule \@width \arrayrulewidth
                                  \hskip .5\arrayrulewidth}}%
 \@tabular}

%    ****************************************
%    *         MULTI-AUTHOR OPTION          *
%    ****************************************
%
\ifSFB@multisty % variations for multi-author editions
%
% ABSTRACT and LIST OF CONTRIBUTORS
%
\newenvironment{abstract}{\section*{Abstract}\trivlist\item[]%
 }{\endtrivlist\addvspace{13\p@}}
%
\def\listofcontributors{%
 \@makeschapterhead{Contributors}
 \@mkboth{Contributors}{Contributors}
 \typeout{List of contributors.}
 \ifSFB@indentsty
  \ifdim\SFB@indent>\z@
   \addcontentsline{toc}{schapter}{\protect
    \numberline{\mbox{}}List of contributors}
  \else
   \addcontentsline{toc}{schapter}{List of contributors}
  \fi
 \else
  \addcontentsline{toc}{schapter}{List of contributors}
 \fi
 \thispagestyle{plain}
 \list{}{\labelwidth\z@
  \labelsep \z@
  \topsep 1\p@
  \leftmargin \z@
  \itemsep 3\p@ \@plus .1\p@
  \itemindent \z@
  \let\makelabel=\contributor
 }\normalsmall\itshape\sloppy
 \def\item{\@ifnextchar [{\SFB@item
  }{\@noitemargtrue \@item[\hspace*{-\labelsep}]}}
}
\def\SFB@item[#1]{\@noitemargtrue
 \@item[\hspace*{-\labelsep}]{\rm #1}\newline\nopagebreak}
\def\contributor#1{\hspace\labelsep \rm #1 \newline\mbox{}\par}
\let\endlistofcontributors=\endlist

\fi % end of multi-author options

%    ****************************************
%    *           INITIALIZATION             *
%    ****************************************
%
% Default initializations
%
\ifSFB@landscape \pagestyle{empty}\else \pagestyle{headings}\fi
\pagenumbering{arabic}
\onecolumn
\flushbottom
\nonfrenchspacing
%
%\ifx\CUP@mtlplain@loaded\undefined
%  \ifSFB@largesty
%    \newfont{\itshape\bfseries}{cmbxti10 scaled\magstephalf}%
%  \else
%    \newfont{\itshape\bfseries}{cmbxti10}%
%  \fi
%\else
%  \ifSFB@largesty
%    \newfont{\itshape\bfseries}{mtbxti10 scaled\magstephalf}%
%  \else
%    \newfont{\itshape\bfseries}{mtbxti10}%
%  \fi
%\fi
%
%\let\bfit=\itbf
%
% end of CUPBOOK.CLS

\endinput

