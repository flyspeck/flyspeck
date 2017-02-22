%%
%% This is file `cuparticle.cls',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% cuparticle.dtx  (with options: `class')
%% 
%% Copyright 2012-2013 Cambridge University Press
%% 
%% This file is part of the 'CUParticle Bundle'.
%% -------------------------------------------
%% 
%% It may be distributed under the conditions of the LaTeX Project Public
%% License, either version 1.2 of this license or (at your option) any
%% later version.  The latest version of this license is in
%%    http://www.latex-project.org/lppl.txt
%% and version 1.2 or later is part of all distributions of LaTeX
%% version 1999/12/01 or later.
%% 
%% The list of all files belonging to the 'CUParticle Bundle' is
%% given in the file `manifest.txt'.
%% 
%% $URL: $
%% $Id: $
%%
 \def\RCSfile{cuparticle}%
 \def\RCSversion{0.1}%
 \def\RCSdate{2012/10/15}%
 \def\@shortjnl{\relax}
 \def\@journal{Cambridge University Press Journal} 
 \def\@company{Cambridge University Press}
 \def\@issn{000-0000}
 \def\@shortjid{cuparticle}
\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{\@shortjid}[\RCSdate, \RCSversion: \@journal]
\def\ABD{\AtBeginDocument}
\newif\ifpreprint \preprintfalse
\newif\ifnonatbib \nonatbibfalse
\newif\iflongmktitle \longmktitlefalse
\newif\ifnopreprintline \nopreprintlinefalse
\newif\ifc@loured\c@louredtrue \c@louredfalse
\def\cuplastauthor{0}
\def\@emailauthorname{}
\def\@emailauthorid{}

\def\@blstr{1}
\newdimen\@bls
\@bls=\baselineskip

\def\@finalWarning{%
  *****************************************************\MessageBreak
   This document is typeset in the CRC style which\MessageBreak
   is not suitable for submission.\MessageBreak
   \MessageBreak
   Please typeset again using 'preprint' option\MessageBreak
   for creating PDF suitable for submission.\MessageBreak
  ******************************************************\MessageBreak
}

\DeclareOption{preprint}{%\global\preprinttrue
  \gdef\@blstr{1}\xdef\jtype{0}}
\DeclareOption{nopreprintline}{\global\nopreprintlinetrue}
\DeclareOption{final}{\gdef\@blstr{1}\global\preprintfalse}
\DeclareOption{review}{\global\preprinttrue\gdef\@blstr{2}}
\DeclareOption{authoryear}{\xdef\@biboptions{round,authoryear}}
\DeclareOption{number}{\xdef\@biboptions{numbers}}
\DeclareOption{numbers}{\xdef\@biboptions{numbers}}
\DeclareOption{nonatbib}{\global\nonatbibtrue}
\DeclareOption{longtitle}{\global\longmktitletrue}
\DeclareOption{plain}{\c@louredfalse}
\DeclareOption{footmarks}{\nofootmarksfalse}
\newif\ifnofootmarks\nofootmarkstrue
\newif\iftimesfont\timesfontfalse

\def\fps@figure{t}

\DeclareOption{fmpi}{\xdef\jtype{1}\global\preprintfalse%
           \AtBeginDocument{\@twocolumnfalse}%
           \def\@journal{Forum of Mathematics, Pi}%
           \gdef\@jid{fmp}}

\DeclareOption{fmp}{\ExecuteOptions{fmpi}}

\DeclareOption{fms}{\xdef\jtype{1}\global\preprintfalse%
           \AtBeginDocument{\@twocolumnfalse}%
           \def\@journal{Forum of Mathematics, Sigma}%
           \gdef\@jid{fms}}

%%--- Not correct
\DeclareOption{5p}{\xdef\jtype{5}\global\preprintfalse
  \ExecuteOptions{twocolumn}}
  \def\jtype{0}
\DeclareOption{3p}{\xdef\jtype{3}\global\preprintfalse}
%%--- 

\let\@mymainhead\@empty
\def\@mymainhead{%
 \vspace*{0pt}%
 \vspace*{-12pt}%
 %\setbox\@tempboxa=\hbox{\includegraphics{\@jid-logo.pdf}}%
 %\minipage[c]{\wd\@tempboxa}\usebox\@tempboxa\endminipage%
 \minipage[c][26pt][t]{0pc}\usebox\@tempboxa\endminipage%
 %\hspace*{8.5pt}%
 \minipage[c]{22pc}\fontsize{9.5pt}{11pt}%
   \selectfont\journalreprintline\endminipage%
 \hfill%
 \minipage[c]{1pc}\fontsize{9.5pt}{11pt}%
   \selectfont\hfill\thepage\endminipage%
}

\DeclareOption{times}{\IfFileExists{txfonts.sty}%
  {\AtEndOfClass{\RequirePackage{txfonts}%
  \gdef\ttdefault{cmtt}%
   \timesfonttrue
   \let\iint\relax
  \let\iiint\relax
  \let\iiiint\relax
  \let\idotsint\relax
  \let\openbox\relax}}{\AtEndOfClass{\RequirePackage{times}}}}

\DeclareOption{endfloat}{\IfFileExists{endfloat.sty}
   {\AtEndOfClass{\RequirePackage[markers]{endfloat}}}{}}
\DeclareOption{endfloats}{\IfFileExists{endfloat.sty}
   {\AtEndOfClass{\RequirePackage[markers]{endfloat}}}{}}
\DeclareOption{numafflabel}
   {\AtBeginDocument{\def\theaffn{\arabic{affn}}}} %*%
\DeclareOption{lefttitle}
   {\AtBeginDocument{\def\cuparticletitlealign{flushleft}}} %*%
\DeclareOption{centertitle}
   {\AtBeginDocument{\def\cuparticletitlealign{center}}} %*%
\DeclareOption{reversenotenum}
   {\AtBeginDocument{\def\theaffn{\arabic{affn}}
    \def\thefnote{\alph{fnote}}}}

\ExecuteOptions{b5paper,1p,10pt,number,preprint,centertitle}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions
\LoadClass{article}
\RequirePackage{graphicx}
\RequirePackage{xcolor}%cup
\RequirePackage{textcase}%cup
\RequirePackage{xspace}%
\RequirePackage{pifont}

\def\volume#1{\gdef\@volume{#1}}
\def\doi#1{\gdef\@doi{#1}}
\def\@Lastpage{\def\@linkcolor{cupblue}\pageref{journal@Last@page}}

\let\comma\@empty
\let\tnotesep\@empty
\let\@title\@empty
\def\useelstitle{}

%CUP

\def\belowtitleskip#1{\gdef\@belowtitleskip{#1}}
\def\abovetitleskip#1{\gdef\@abovetitleskip{#1}}
\def\belowhistoryskip#1{\gdef\@belowhistoryskip{#1}}
\def\abovehistoryskip#1{\gdef\@abovehistoryskip{#1}}


%\belowtitleskip{14pt}
\belowtitleskip{17pt}
%\abovetitleskip{12mm}
\abovetitleskip{10mm}
\belowhistoryskip{10pt}
\abovehistoryskip{0pt}
\newskip\beforehistoryskip
\newskip\beforededicationskip
\newskip\aboveabsskip
\newskip\belowabsskip
\beforehistoryskip=18\p@ plus 6\p@ minus 6\p@
\beforededicationskip=8\p@ plus 4\p@ minus 4\p@
\aboveabsskip=15\p@ plus2\p@ minus 1\p@
\belowabsskip=7\p@ plus2\p@ minus1\p@

\hyphenpenalty=100
\pretolerance=500
%\tolerance=1000
\hbadness=2000
\vbadness=2000
\setcounter{topnumber}{5}
\def\topfraction{1}
\setcounter{bottomnumber}{5}
\def\bottomfraction{.8}
\setcounter{totalnumber}{10}
\def\textfraction{0}
\def\floatpagefraction{.8}
\def\nfontsize#1#2{\fontsize{#1}{#2}\selectfont}

\renewcommand\normalsize{%
   \@setfontsize\normalsize{10.5}{12.6\p@ \@plus.3\p@ \@minus .3\p@}%
   \abovedisplayskip 8\p@ \@plus2\p@ \@minus5\p@%
   \abovedisplayshortskip \z@ \@plus3\p@%
   \belowdisplayshortskip 6\p@ \@plus3\p@ \@minus3\p@%
   \belowdisplayskip \abovedisplayskip%
   \let\@listi\@listI}
\renewcommand{\small}{\fontsize{9}{11pt}\selectfont}
\renewcommand{\scriptsize}{\fontsize{7}{9pt}\selectfont}
\renewcommand\footnotesize{%
   \@setfontsize\footnotesize{8.6}{10.3}
   \abovedisplayskip 6\p@ \@plus2\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus\p@
   \belowdisplayshortskip 3\p@ \@plus\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 3\p@ \@plus\p@ \@minus\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\renewcommand{\tiny}{\fontsize{5}{6\p@}\selectfont}
\renewcommand{\large}{\fontsize{12}{14\p@}\selectfont}
\renewcommand{\Large}{\fontsize{13}{18\p@}\selectfont}
\renewcommand{\LARGE}{\fontsize{17}{22\p@}\selectfont}
\renewcommand{\huge}{\fontsize{20}{26\p@}\selectfont}
\renewcommand{\Huge}{\fontsize{25}{30\p@}\selectfont}

\long\def\@footnotetext#1{\insert\footins{%
    \reset@font\footnotesize
    \interlinepenalty\interfootnotelinepenalty
    \splittopskip\footnotesep
    \splitmaxdepth \dp\strutbox \floatingpenalty \@MM
    \hsize\columnwidth \@parboxrestore
    \protected@edef\@currentlabel{%
       \csname p@footnote\endcsname\@thefnmark
    }%
    \color@begingroup
      \@makefntext{%
        \rule\z@\footnotesep\ignorespaces\hspace*{-8pt}#1\@finalstrut\strutbox}%
    \color@endgroup}}%
    
\def\@makefnmark{\hbox{\@textsuperscript{\normalfont\@thefnmark}}}    

\long\def\@makefntext#1{\parindent 1em\noindent
            \hb@xt@1.8em{%
                \hspace*{3pt}\@textsuperscript{\normalfont\@thefnmark}}#1}%

        
\def\footnoterule{%\color{cupgreen}
\kern-3\p@
  \hrule \@width 28mm \kern 2.6\p@} % the \hrule is .4pt high

\def\journal#1{\gdef\@journal{#1}}
\newcommand\submittedto{%
  Submitted to the %
   \ifx\@journal\@empty Cambridge University Press Journal%
    \else%
     \@journal%
   \fi}
%Bulletin of the Australian Mathematical Society}

\def\ps@pprintTitle{%\@mainheadline%
     \let\@mkboth\@gobbletwo
     \def\@oddhead{\parbox[t]{\textwidth}{\@mymainhead}}\def\@evenhead{}%
     \def\@oddfoot{}%\parbox[t]{\textwidth}{%
     %{\let\t@fill\hfill\let\t@lap\relax%
     %\hfill\hbox{\hskip-8pt\foot@pagenum}}\def\@evenfoot{}}
     }

\def\ps@austms{%
      \let\@mkboth\@gobbletwo
      \def\@evenhead{\parbox[b]{\textwidth}%
        {\cup@pages@banner\textcolor{cupgreen}{\nfontsize{8.6}{10.3}%
        %\thepage\hfill{\leftmark}\hfill[\thepage]
         %\setbox\@tempboxa=\hbox{\includegraphics[scale=.56]{\@jid-logo.pdf}}%
         %\minipage[c]{\wd\@tempboxa}\usebox\@tempboxa\endminipage%
         \hfill
         \hbox{\itshape\ifodd\thepage\@recto\else\@verso\fi}%
         \hfill%
         \thepage%
        }}}%
       \let\@oddhead\@evenhead%
      \def\@evenfoot{}%\let\t@fill\hfill\let\t@lap\relax\foot@pagenum}
      \def\@oddfoot{}%\let\t@fill\hfill\let\t@lap\relax\foot@pagenum}
}
\def\foot@pagenum{\t@fill\relax{%\ifodd\thepage\hspace*{5pt}\fi%
  \ooalign{\color{cupblue}\fontsize{50pt}{50pt}\selectfont%
  $\bullet$\crcr \hfill
  \ifnum\thepage=1 \raise11.5pt\else\raise9.5pt\fi%
  \hbox{\textcolor{white}%
  {\bf\thepage}}\hfill}%\ifodd\thepage\else\hspace*{5pt}\fi%
  \kern-3pt}}
\def\@recto{Please supply a running title}
\def\@verso{Please supply the list of authors}
\newcommand\runningtitle[1]{\gdef\@recto{#1}}
\newcommand\authorheadline[1]{\gdef\@verso{#1}}
\def\@typesetRunningHeads{\markboth{\@verso}{\@recto}}
\newcommand\support[1]{\footnotetext[2]{\noindent #1}}
\expandafter\def\csname mn@0\endcsname{Month}
\expandafter\def\csname mn@00\endcsname{Month}
\expandafter\def\csname mn@1\endcsname{January}
\expandafter\def\csname mn@01\endcsname{January}
\expandafter\def\csname mn@2\endcsname{February}
\expandafter\def\csname mn@02\endcsname{February}
\expandafter\def\csname mn@3\endcsname{March}
\expandafter\def\csname mn@03\endcsname{March}
\expandafter\def\csname mn@4\endcsname{April}
\expandafter\def\csname mn@04\endcsname{April}
\expandafter\def\csname mn@5\endcsname{May}
\expandafter\def\csname mn@05\endcsname{May}
\expandafter\def\csname mn@6\endcsname{June}
\expandafter\def\csname mn@06\endcsname{June}
\expandafter\def\csname mn@7\endcsname{July}
\expandafter\def\csname mn@07\endcsname{July}
\expandafter\def\csname mn@8\endcsname{August}
\expandafter\def\csname mn@08\endcsname{August}
\expandafter\def\csname mn@9\endcsname{September}
\expandafter\def\csname mn@09\endcsname{September}
\expandafter\def\csname mn@10\endcsname{October}
\expandafter\def\csname mn@11\endcsname{November}
\expandafter\def\csname mn@12\endcsname{December}
\let\@received\@empty
\let\@accepted\@empty

\newcommand\received[1]{\gdef\@received{#1}}
\newcommand\accepted[1]{\gdef\@accepted{#1}}
%\newcommand\received[1]{\p@rseRecd#1\@nil}
%\def\p@rseRecd#1 #2 #3\@nil{%
%       \gdef\recddt{#1}%
%       \gdef\recdmnt{#2}%
%       \gdef\recdyr{#3}%
%       \gdef\@received{$\recddt$\space
%       \csname mn@\recdmnt\endcsname
%       \space$\recdyr$}%
%}

\def\@mainheadline{%
      \gdef\@mymainhead{%
         \parbox[t]{\textwidth}{\color{cupgreen}%
         \nfontsize{8.6}{10.3}%
         \ifnopreprintline\relax\else%
           \textit{\submittedto}\hfill\mbox{}\\
         doi:10.1017/S \dots \hfill\mbox{}\fi}}%
         \setcounter{page}{1}%
}

\def\nfontsize#1#2{\fontsize{#1}{#2}\selectfont}

\def\titleattrib#1{\bfseries%
       \nfontsize{11.5}{13.8}%
       \mathversion{bold}{\color{cupblue}%
       \MakeTextUppercase{#1}}}

\def\authorattrib#1{\bfseries%
       \nfontsize{11.5}{13.8}%
       \mathversion{bold}{\color{cupblue}%
       \MakeTextUppercase{#1}}}

\def\historyattrib#1{{\nfontsize{8.6}{10.3}#1}}

\def\abstitlealignment#1{\mbox{}\hfill#1\hfill\mbox{}}
\def\abstitleattrib#1{{\bfseries\nfontsize{8.6}{10.3}\color{cupblue}#1}}

\def\abstextfontattrib{\nfontsize{8.6}{10.3}}

\def\msctitlefontattrib#1{\footnotesize%
       {\color{cupblue}%
       {#1}}}

\def\mscyearfontattrib#1{\footnotesize%
       {\color{cupblue}%
       {\rmfamily#1}}}

\def\msckwdfontattrib#1{\footnotesize%
       {%\color{cupgreen}%
       {\rmfamily#1}}}

\def\kwdtitlefontattrib#1{\footnotesize%
       {\color{cupgreen}%
       {\itshape#1}}}
                          
\def\kwdfontattrib{\footnotesize%
       \color{cupgreen}%
       \nfontsize{8.6}{10.3}\rmfamily}

\def\msctitle#1{\gdef\@msctitle{\msctitlefontattrib{#1}}}
\msctitle{Mathematics Subject Classification}
\def\mscbelowskip#1{\gdef\@mscbelowskip{#1}}
\mscbelowskip{6pt}

%%%%

\def\title#1{\g@addto@macro\@title{\titleattrib{#1}%cup
       \global\let\tnoteref\@gobble%
       \@ifundefined{mark@title}{\ignorespaces}%
        {\xdef\@tmp{\@nameuse{mark@title}}%
          \@for\p@mark:=\@tmp\do
          {\ifnofootmarks%
           \else%
             \textsuperscript{\ifcase\p@mark\or$\star$\or
               \unskip,$\star\star$\fi}
           \fi%
           }}}
       \g@addto@macro\useelstitle{#1}}

\def\OpenAccessNotice{%
\def\thefootnote{}%
\footnotetext{%
  \ifx\@cornotes\@empty%
     \unskip\ignorespaces\hskip-.9\parindent%
   \else\vskip1pt%
    \hskip-\parindent%
  \fi%
%\fontsize{6.15pt}{7.2pt}\selectfont\textcopyright~The Author(s) \the\year.
%The online version of this article is published within an Open Access
%environment subject to the conditions of the Creative Commons
%Attribution %-NonCommercial-ShareAlike 
%licence
%\underbar{$<$http://creativecommons.org/licenses/by/3.0/$>$.}%
\fontsize{6.15pt}{7.2pt}\selectfont\textcopyright~The Author(s) \the\year.
This is an Open Access article, 
distributed under the terms of the Creative Commons
Attribution licence
(\underbar{$<$http://creativecommons.org/licenses/by/3.0/$>$}),
which permits unrestricted re-use, distribution, and
reproduction in any medium, provided the original work is properly
cited.
}%
}

 


\def\journalreprintline{%\hskip-8pt
 \@journal\ %
 \color{cupblue}(\the\year), vol. \@volume, 
 e1, \@Lastpage\ pages\newline%
 doi:\@doi}


\def\elsLabel#1{\@bsphack\protected@write\@auxout{}%
         {\string\Newlabel{#1}{\@currentlabel}}\@esphack}
\def\Newlabel#1#2{\expandafter\xdef\csname X@#1\endcsname{#2}}
\def\writemarks#1#2{\immediate\write\@auxout{
    \string\expandafter\string\gdef\string\csname\space
      mark@#1\string\endcsname{#2}}}

\def\elsRef#1{\@ifundefined{X@#1}{0}{\csname X@#1\endcsname}}

\let\@tnotemark\@empty

\def\tnoteref#1{\@for\mytmark:=#1\do{%
       \expandafter\ifcase\csname X@\mytmark\endcsname\or$^{\star}$\or
       $^{,\star\star}$\fi
    }%
}

\def\tnotemark[#1]{\writemarks{title}{#1}}
     
\let\@tnotes\@empty
\newcounter{tnote}
\def\tnotetext[#1]#2{%
    \expandafter\ifcat\@car#1\@nil a\relax
     \typeout{---------------[tnote]--[alpha]-----------------------------}%
     \g@addto@macro\@tnotes{%
     \refstepcounter{tnote}\elsLabel{#1}%
     \def\thefootnote{\ifcase\c@tnote\or$\star$\or$\star\star$\fi}%
     \footnotetext{#2}}%
   \else
     \g@addto@macro\@tnotes{%
     \@tempcnta=#1\relax%
      \ifnofootmarks%
       \def\thefootnote{}%
      \else%
       \def\thefootnote{\ifcase\@tempcnta\or$\star$\or$\star\star$\fi}%
      \fi%
     \footnotetext{#2}}%
   \fi
}

\let\@nonumnotes\@empty
\def\nonumnote#1{\g@addto@macro\@nonumnotes{%
     \let\thefootnote\relax\footnotetext{#1}}}

\newcounter{fnote}
\def\thefnote{\arabic{fnote}}
\def\fnref#1{\let\comma\@empty
    \def\@fnmark{\@for\@@fnmark:=#1\do{%
    \edef\fnotenum{\@ifundefined{X@\@@fnmark}{1}{\elsRef{\@@fnmark}}}%
  \unskip\comma\fnotenum\let\comma,}}%
}
\def\fnmark[#1]{\writemarks{fnau\theau@}{#1}}

\let\@fnotes\@empty\let\@fnmark\@empty
\def\fntext[#1]#2{%
    \expandafter\ifcat\@car#1\@nil a\relax
     \typeout{------------------------alpha-----------------------------}%
     \g@addto@macro\@fnotes{%
     \refstepcounter{fnote}\elsLabel{#1}%
\ifnofootmarks
     \def\thefootnote{}%
\else
     \def\thefootnote{\@arabic\c@fnote}%
\fi
     \global\setcounter{footnote}{\c@fnote}%
     \footnotetext{#2}}%
    \else
     \typeout{------------------------number-----------------------------}%
     \g@addto@macro\@fnotes{%
\ifnofootmarks
     \def\thefootnote{}%
\else
     \def\thefootnote{\@arabic#1}%
\fi
     \footnotetext{#2}}%
    \fi
}

\def\cormark[#1]{\expandafter\ifcat\@car#1\@nil a\relax%
       \@tempcnta=\csname thealphctr#1\endcsname%
			 \writemarks{corau\theau@}{\the\@tempcnta}%       
       \else%
			 \writemarks{corau\theau@}{#1}%       
       \fi%
}

\let\@cormark\@empty
\let\@cornotes\@empty
\newcounter{cnote}

\def\cortext[#1]#2{%
    \expandafter\ifcat\@car#1\@nil a\relax
    \typeout{------------------------alpha-----------------------------}%
     \g@addto@macro\@cornotes{%
     \refstepcounter{cnote}\elsLabel{#1}%
     \def\thefootnote{\ifcase\thecnote\or%
      $\,{^\dag}$\or
      $\,{\hbox{\ding{41}\ding{41}\ding{41}}}$\or%
      \sep$\,{\hbox{\ding{41}\ding{41}\ding{41}}}$\fi}%
     \footnotetext{#2}}%
    \else
%    \typeout{------------------------number-----------------------------}%
     \g@addto@macro\@cornotes{%
     \@tempcnta=#1\relax%
     \def\thefootnote{\ifcase\@tempcnta\or%
      $\,{^\dag}$\or
      $\,{\hbox{\ding{41}\ding{41}}}$\or%
      $\,{\hbox{\ding{41}\ding{41}\ding{41}}}$\fi}%
     \footnotetext{#2: \@emailauthorname, email: \@emailauthorid}
     }%
    \fi
}

\let\@corref\@empty
\def\corref#1{\edef\cnotenum{\elsRef{#1}}%
    \edef\@corref{\ifcase\cnotenum\or
         $\ast$\or$\ast\ast$\or$\ast\ast\ast$\fi\hskip-1pt}}

\def\resetTitleCounters{\c@cnote=0
   \c@fnote=0 \c@tnote=0 \c@footnote=0}

\let\eadsep\@empty
\def\@elseads{}
\let\@elsuads\@empty
\let\@cormark\@empty
\def\hashchar{\expandafter\@gobble\string\~}
\def\underscorechar{\expandafter\@gobble\string\_}
\def\lbracechar{\expandafter\@gobble\string\{}
\def\rbracechar{\expandafter\@gobble\string\}}

\gdef\ead{\@ifnextchar[{\@uad}{\@ead}}
\gdef\@ead#1{\bgroup
   \def\_{\underscorechar}%
   \def\{{\lbracechar}%
   \def~{\hashchar}%
   \def\}{\rbracechar}%
   \edef\tmp{\the\@eadauthor}%
   \immediate\write\@auxout{\string\emailauthor
     {#1}{\expandafter\strip@prefix\meaning\tmp}}%
   \egroup
   \immediate\write\@auxout{\string\expandafter\string\gdef
     \string\csname\space mark@ead\theauthor\string\endcsname{1}}%
  \@ifundefined{cupeads\theaublock}{\expandafter\let
      \csname cupeads\theaublock\endcsname\@empty}{}%
   \expandafter\g@addto@macro\csname cupeads\theaublock\endcsname
      {\eadsep#1\def\eadsep{\unskip,\space}}
}
\newcounter{ead}
\gdef\emailauthor#1#2{%
     \gdef\@emailauthorid{#1}
     \gdef\@emailauthorname{#2}
     \stepcounter{ead}%
     \g@addto@macro\@elseads{\raggedright%
      \let\corref\@gobble\def\@@tmp{#1}%
      \eadsep{\ttfamily\expandafter\strip@prefix\meaning\@@tmp}
      (#2)\def\eadsep{\unskip,\space}}%
}
\gdef\@uad[#1]#2{\bgroup
   \def~{\hashchar}%
   \def\_{\underscorechar}%
   \def~{\hashchar}%
   \def\}{\rbracechar}%
   \edef\tmp{\the\@eadauthor}
   \immediate\write\@auxout{\string\urlauthor
     {#2}{\expandafter\strip@prefix\meaning\tmp}}%
  \egroup
}
\gdef\urlauthor#1#2{\g@addto@macro\@elsuads{\let\corref\@gobble%
     \def\@@tmp{#1}\raggedright\eadsep
     {\ttfamily\expandafter\strip@prefix\meaning\@@tmp}\space(#2)%
     \def\eadsep{\unskip,\space}}%
}

\def\cupauthors{}
\def\cuptitlepageauthors{}
\def\Xcuptitlepageauthors{}
\def\useauthors{}

\def\pprinttitle{}
\let\authorsep\@empty
\let\sep\@empty
\def\@exp{\expandafter\expandafter\expandafter}
\def\process@marks{%
      \@ifundefined{mark@address\theauthor}{\ignorespaces}%
        {\xdef\@tmp{\@nameuse{mark@address\theauthor}}%
          \let\comma\@empty
          \@for\p@mark:=\@tmp\do{%
           \comma{\p@mark}\let\comma=,}%
         \def\sep{\unskip,}}
      \@ifundefined{mark@corau\theauthor}{\ignorespaces}%
        {\edef\@tmp{\csname mark@corau\theauthor\endcsname}%
          \unskip\ifcase\@tmp\or\sep$^\dag$\or
           \sep$\ast\ast$\or\sep$\ast\ast\ast$\fi
           \def\sep{\unskip,}}%
      \@ifundefined{mark@fnau\theauthor}{\ignorespaces}%
        {\unskip\let\comma\@empty
          \edef\@@tmp{\csname mark@fnau\theauthor\endcsname}%
          \sep\@for\p@mark:=\@@tmp\do{%
           \comma{\p@mark}\let\comma=,}%
         \def\sep{\unskip,}}%
\unskip}

\newcounter{author}
\newcounter{au@}
\newcounter{title@au}
\def\author{\stepcounter{au@}\@ifnextchar[{\@@author}{\@@author[]}}
\def\authorandsep{~and }
%\def\ischar#1{%
%  \if!\ifnum9<1#1!\else\fi
%    \global\ischarfalse A#1\else\global\ischartrue B#1\fi}
    
\newcount\foo
\gdef\thealphctra{1}
\gdef\thealphctrb{2}
\gdef\thealphctrc{3}
\gdef\thealphctrd{4}
\gdef\thealphctre{5}
\gdef\thealphctrf{6}
\gdef\thealphctrg{7}
\gdef\thealphctrh{8}
\gdef\thealphctri{9}
\gdef\thealphctrj{10}
\gdef\thealphctrk{11}
\gdef\thealphctrl{12}
\gdef\thealphctrm{13}
\gdef\thealphctrn{14}
\gdef\thealphctro{15}
\gdef\thealphctrp{16}
\gdef\thealphctrq{17}
\gdef\thealphctrr{18}
\gdef\thealphctrs{19}
\gdef\thealphctrt{20}
\gdef\thealphctru{21}
\gdef\thealphctrv{22}
\gdef\thealphctrw{23}
\gdef\thealphctrx{24}
\gdef\thealphctry{25}
\gdef\thealphctrz{26}

                                  
\newtoks\@eadauthor
\def\@@author[#1]#2{%
%   \expandafter\ifcat\@car#1\@nil a\relax
   \writemarks{address\theau@}{#1}%
    \g@addto@macro\cupauthors{%
      \def\baselinestretch{1}\stepcounter{author}%
      \ifnum\theauthor=\cuplastauthor%
      \ifnum\cuplastauthor=1%      
      \else%
      {\authorandsep}%
      \fi%
      \else%
      \authorsep\fi\uppercase{#2}%      
%        \unskip\textsuperscript{\process@marks}%
%       \gdef\authorsep{\unskip,\space}%
%       \global\let\sep\@empty\global\let\@corref\@empty
%    \global\let\@fnmark\@empty%
%%%%%%%%      
      \unskip\textsuperscript{%#1%
       \@for\@@affmark:=#1\do{%
       \expandafter\ifcat\@car\@@affmark\@nil a\relax%
       \@tempcnta=\csname thealphctr\@@affmark\endcsname
       \else
			 \@tempcnta=\@@affmark       
       \fi%
      \edef\affnum{\@ifundefined{X@\@@affmark}{\the\@tempcnta}{\elsRef{\@@affmark}}}%
      \unskip\sep\affnum\let\sep=,}%
      \ifx\@fnmark\@empty\else\unskip\sep\@fnmark\let\sep=,\fi%
      \ifx\@corref\@empty\else\unskip\sep\@corref\let\sep=,\fi%
      \@ifundefined{mark@corau\theauthor}{\ignorespaces}%
        {\edef\@tmp{\csname mark@corau\theauthor\endcsname}%Cormark
%          \unskip\ifcase\@tmp\or\sep$^\dag$\or
%           \sep$\ast\ast$\or\sep$\ast\ast\ast$\fi
          \unskip\ifcase\@tmp\or\,$^\dag$\or
           \,$\ast\ast$\or\,$\ast\ast\ast$\fi 
           \def\sep{\unskip,}}%
      \@ifundefined{mark@fnau\theauthor}{\ignorespaces}%
        {\unskip\let\comma\@empty
          \edef\@@tmp{\csname mark@fnau\theauthor\endcsname}%Aufnmark
          \sep\@for\p@mark:=\@@tmp\do{%
           \comma{\p@mark}\let\comma=,}%
         \def\sep{\unskip,}}%      
      \gdef\authorsep{\unskip,\space}%
      \global\let\sep\@empty\global\let\@corref\@empty
      \global\let\@fnmark\@empty}%
      \immediate\write\@auxout{\string\expandafter\gdef\string\csname\space cuplastauthor\string\endcsname{\theauthor}}%
       }%
%   \else
%     \writemarks{address\theau@}{#1}
%     \g@addto@macro\cupauthors{%
%       \def\baselinestretch{1}\stepcounter{author}%
%      \ifnum\theauthor=\cuplastauthor%
%      \textsc{\authorandsep}
%      \else%       
%       \authorsep\fi{\uppercase #2}%
%        \unskip\textsuperscript{\process@marks}%
%       \gdef\authorsep{\unskip,\space}%
%       \global\let\sep\@empty\global\let\@corref\@empty
%    \global\let\@fnmark\@empty%
%     }%
%   \fi
    \@eadauthor={#2}%
    \g@addto@macro\useauthors{#2; }%
}


\newcounter{aublock}
\setcounter{aublock}{1}


\def\@author#1{\stepcounter{author}%
% \cupauthors will print author and address at
% end of document.
     \@ifundefined{cupauthors\theaublock}%
      {\expandafter\let\csname cupauthors\theaublock\endcsname\@empty}{}%
     \expandafter\g@addto@macro\csname cupauthors\theaublock\endcsname
      {\normalsize
        \def\baselinestretch{1}\stepcounter{author}%
        \authorsep#1%
      }%
%
% \cuptitlepageauthors will print authors alone
% at title page.
% 
    \stepcounter{title@au}
    \g@addto@macro\cuptitlepageauthors{%
     \stepcounter{title@au}\ausep#1%
     \upshape\textsuperscript{%
      \ifx\@fnmark\@empty\else\unskip\sep\@fnmark\let\sep=,\fi
      \ifx\@corref\@empty\else\unskip\sep\@corref\let\sep=,\fi
      \process@marks
    }
    \global\let\@fnmark\@empty
    \global\let\@corref\@empty
    \global\let\sep\@empty}%
}

%\def\printauthors@titlepage{\@tempcnta=0\relax
%       \edef\total@au{\thetitle@au}%
%       \def\ausep{\global\advance\@tempcnta1
%         \ifnum\@tempcnta=1\relax\else
%         \ifnum\@tempcnta=\total@au\relax and 
%          \else\unskip,\space\fi\fi}%
%          \setcounter{title@au}{0}%
%          \cuptitlepageauthors
%          }


\AtBeginDocument{%
  \@ifpackageloaded{hyperref}{%
    \expandafter\gdef\csname Hy@title\endcsname{\useelstitle}%
    \expandafter\gdef\csname Hy@author\endcsname{\useauthors}%
   }{}
}

\def\elsaddress{}
\def\addsep{\unskip,\space}
\def\address{\@ifnextchar[{\@@address}{\@address}}


\def\@alph#1{%
  \ifcase#1\or a\or b\or c\or d\or e\or f\or g\or h\or i\or j\or k\or
  l\or m\or n\or o\or p\or q\or r\or s\or t\or u\or v\or w\or x\or
  y\or z%
  \or aa\or ab\or ac\or ad\or ae\or af\or ag\or ah\or ai\or aj\or
  ak\or al\or am\or an\or ao\or ap\or aq\or ar\or as\or at\or au\or
  av\or aw\or ax\or ay\or az%
  \or ba\or bb\or bc\or bd\or be\or bf\or bg\or bh\or bi\or bj\or
  bk\or bl\or bm\or bn\or bo\or bp\or bq\or br\or bs\or bt\or bu\or
  bv\or bw\or bx\or by\or bz%
  \or ca\or cb\or cc\or cd\or ce\or cf\or cg\or ch\or ci\or cj\or
  ck\or cl\or cm\or cn\or co\or cp\or cq\or cr\or cs\or ct\or cu\or
  cv\or cw\or cx\or cy\or cz%
  \or da\or db\or dc\or dd\or de\or df\or dg\or dh\or di\or dj\or
  dk\or dl\or dm\or dn\or do\or dp\or dq\or dr\or ds\or dt\or du\or
  dv\or dw\or dx\or dy\or dz%
  \or ea\or eb\or ec\or ed\or ee\or ef\or eg\or eh\or ei\or ej\or
  ek\or el\or em\or en\or eo\or ep\or eq\or er\or es\or et\or eu\or
  ev\or ew\or ex\or ey\or ez%
  \or fa\or fb\or fc\or fd\or fe\or ff\or fg\or fh\or fi\or fj\or
  fk\or fl\or fm\or fn\or fo\or fp\or fq\or fr\or fs\or ft\or fu\or
  fv\or fw\or fx\or fy\or fz%
  \or ga\or gb\or gc\or gd\or ge\or gf\or gg\or gh\or gi\or gj\or
  gk\or gl\or gm\or gn\or go\or gp\or gq\or gr\or gs\or gt\or gu\or
  gv\or gw\or gx\or gy\or gz%
  \else\@ctrerr\fi}

\newcounter{affn}
%\renewcommand\theaffn{\alph{affn}}

\let\cupeads\@empty
\let\cupaddress\@empty
\newcounter{address}

\long\def\@@address[#1]#2{%
   \def\ead##1{\unskip; ##1}%
   \expandafter\ifcat\@car#1\@nil a\relax
    \g@addto@macro\cupaddress{%
     \def\baselinestretch{1}%
     \refstepcounter{affn}
     \xdef\@currentlabel{\theaffn}
     \elsLabel{#1}%
     \textsuperscript{\theaffn}#2\par}
   \else
    \g@addto@macro\cupaddress{%
     \def\baselinestretch{1}%
     \setcounter{affn}{#1}%
     \textsuperscript{\theaffn}#2\par}%
   \fi
} 

\long\def\@address#1{%
   \def\ead##1{\unskip; ##1}%
%    \expandafter\xdef\csname aucount\theaublock\endcsname{\theauthor}%
%    \expandafter\gdef\csname
%      cupaddress\theaublock\endcsname{\unskip, #1}%
%    \stepcounter{aublock}%
%    \setcounter{author}{0}%
    \g@addto@macro\cupaddress{%
     \def\baselinestretch{1}%
%     \setcounter{affn}{#1}%
     #1\par}%
}

\newcounter{EadCtr}
\def\Ead#1{\stepcounter{EadCtr}%
  \expandafter\gdef\csname#1\theEadCtr\endcsname{#1}
  \g@addto@macro\EmailAddresses{#1}}
  %

\newbox\absbox
\let\@cuparticleabstitle\@empty %*%
\def\abstracttitle#1{\gdef\@cuparticleabstitle{#1}} %*%
\abstracttitle{Abstract} %*%
\renewenvironment{abstract}{\global\setbox\absbox=\vbox\bgroup
  \hsize=\textwidth
  \noindent\abstitlealignment{%
  \abstitleattrib{\@cuparticleabstitle}%
  \abstextfontattrib}
 \par\medskip\noindent\unskip\ignorespaces}
 {\egroup}

\newbox\overviewbox
\let\@cuparticleoverviewtitle\@empty %*%
\def\overviewtitle#1{\gdef\@cuparticleoverviewtitle{#1}} %*%
\overviewtitle{Overview} %*%
\newenvironment{overview}{\global\setbox\overviewbox=\vbox\bgroup
  \hsize=\textwidth
  \noindent\abstitlealignment{%
  \abstitleattrib{\@cuparticleoverviewtitle}%
  \abstextfontattrib}
 \par\medskip\noindent\unskip\ignorespaces}
 {\egroup}

\def\PACS{\par\leavevmode\hbox {\it PACS:\space}}%
\def\JEL{\par\leavevmode\hbox {\it JEL:\space}}%

\newbox\keybox
\let\@cuparticlekwdtitle\@empty %*%
\def\keywordtitle#1{\gdef\@cuparticlekwdtitle{#1}} %*%
\def\keywordtitlesep#1{\gdef\@cuparticlekeywordtitlesep{#1}} %*%
\keywordtitle{\kwdtitlefontattrib{Keywords and phrases}} %*%
\keywordtitlesep{:\ }

\def\MSC{\@ifnextchar[{\@MSC}{\@MSC[2010]}}
\def\@MSC[#1]#2{\gdef\@@MSC{%\leavevmode%
   \def\sep{\unskip;\xspace}%
   \leavevmode\par%
   \vspace*{-1\baselineskip}
   \def\primary{\def\sep{,\xspace}primary\xspace}%
   \def\secondary{\unskip;\space\def\sep{,\xspace}secondary\xspace}%
   \iftimesfont
%   \hskip-5.1pc
   \else
%   \hskip-3pc
   \fi
   %\hbox
   \unskip\ignorespaces{\mscyearfontattrib{#1}~%
   \@msctitle:~\msckwdfontattrib{#2}\space}%
}}

\gdef\keyword{%
  \global\setbox\keybox=\vbox\bgroup\hsize=\textwidth%
  \parskip\z@%
  \raggedright%                         % Keywords are not justified.
  \ignorespaces%
  \def\sep{\unskip, }%
  \@cuparticlekwdtitle\@cuparticlekeywordtitlesep%
  }
\def\endkeyword{\par \egroup}

\newdimen\Columnwidth
\Columnwidth=\columnwidth

\def\printFirstPageNotes{%
  \iflongmktitle
   \let\columnwidth=\textwidth\fi
  \ifx\@tnotes\@empty\else\@tnotes\fi
  \ifx\@nonumnotes\@empty\else\@nonumnotes\fi
  \ifx\@cornotes\@empty\else\@cornotes\fi
  \ifx\@fnotes\@empty\else\@fnotes\fi
  \OpenAccessNotice%\vskip12pt%  
  \iflongmktitle\if@twocolumn
   \let\columnwidth=\Columnwidth\fi\fi
}

%% Pushing text to begin on newpage %*%
\def\newpage@after@title{title}
\def\newpage@after@author{author}
\def\newpage@after@abstract{abstract}
\def\newpageafter#1%
    {\gdef\@cuparticlenewpageafter{#1}}

\long\def\pprintMaketitle{\clearpage
  \resetTitleCounters
  \def\baselinestretch{1}%
  \printFirstPageNotes
  \begin{\cuparticletitlealign}%
  \thispagestyle{pprintTitle}%
   \def\baselinestretch{1}%
    \Large\@title\par\vskip18pt%
    \ifx\@cuparticlenewpageafter\newpage@after@title% %*%
      \newpage
    \fi%
    \normalsize\cupauthors\par\vskip10pt
    \footnotesize\itshape\elsaddress\par\vskip36pt
    \ifx\@cuparticlenewpageafter\newpage@after@author% %*%
      \newpage
    \fi%
    \hrule
    \vskip12pt
    \ifvoid\absbox\else\unvbox\absbox\par\vskip10pt\fi
    \vskip12pt
    \ifvoid\overviewbox\else\unvbox\overviewbox\par\vskip10pt\fi
%    \ifvoid\keybox\else\unvbox\keybox\par\vskip10pt\fi
    \hrule\vskip12pt
    \ifx\@cuparticlenewpageafter\newpage@after@abstract% %*%
      \newpage
    \fi%
    \end{\cuparticletitlealign}%
    \gdef\thefootnote{\arabic{footnote}}%
}


\def\printWarning{%
     \mbox{}\par\vfill\par\bgroup
     \fboxsep12pt\fboxrule1pt
     \hspace*{.18\textwidth}
     \fcolorbox{gray50}{gray10}{\box\warnbox}
     \egroup\par\vfill\thispagestyle{empty}
     \setcounter{page}{0}
     \clearpage}

\long\def\finalMaketitle{%
  \resetTitleCounters
  \def\baselinestretch{1}%
   \MaketitleBox
   \thispagestyle{pprintTitle}%
  \gdef\thefootnote{\arabic{footnote}}%
  }

\long\def\MaketitleBox{%cup
%  \cup@title@banner%
  \resetTitleCounters%
  \begin{\cuparticletitlealign}%
    \vspace*{\@abovetitleskip}%
    \parbox{.9\textwidth}
     {\centering{\color{cupblue}%
       \bfseries\nfontsize{11.5}{13.8}%
       \mathversion{bold}%
       \@title%
     }  
     \par% 
    \vspace*{\@belowtitleskip}%
    \normalsize\cupauthors\par\vskip10pt
    \footnotesize\itshape\cupaddress\par\vskip18pt
    }
    \vspace*{\@abovehistoryskip}
    \par
    \historyattrib{%
     \ifx\@received\@empty\relax\else
       {\color{cupblue}Received} \@received%
     \ifx\@accepted\@empty\relax\else%  
        {\color{cupblue}; accepted} \@accepted\fi%
     \fi}
    \vspace*{\@belowhistoryskip}
    \vskip12pt
    \ifvoid\absbox\else\unvbox\absbox\par\vskip10pt\fi%
%    \vskip12pt
    \ifx\@@MSC\@emptyrelax\else%
      \@parboxrestore
      \hsize=\textwidth
      \@@MSC%
      \vspace*{\@mscbelowskip}%
    \fi%
    \ifvoid\keybox\else%
      \color{cupgreen}%
      \unvbox\keybox\par\vskip10pt%
    \fi
    \vskip12pt
    \ifvoid\overviewbox\else\unvbox\overviewbox\par\vskip10pt\fi
    \end{\cuparticletitlealign}%
}

\@typesetRunningHeads
\pagestyle{austms}

% CUP
\newcounter{aub@@}

%\def\authorsep{%
%      \global\advance\@tempcnta1
%         \ifnum\@tempcnta=1\relax\else
%         \ifnum\@tempcnta=\@@@tmp\relax and 
%          \else\unskip,\space\fi\fi
%    \typeout{.....[\the\@tempcnta] = [\@@@tmp].........}% 
%}

\let\eadsep\@empty

%\long\def\EndMaketitleBox{%
%  \resetTitleCounters
%  \def\baselinestretch{1}%
%  \begin{flushleft}%
%   \def\baselinestretch{1}%
%    \vskip18pt
%    \normalsize
%    \@tempcntb=\theaublock
%    \advance\@tempcntb1
%    \color{cupgreen}
%    \loop
%      \ifnum\c@aub@@ < \@tempcntb
%       \expandafter\ifx\csname aucount\theaub@@\endcsname\relax%
%         \edef\@@@tmp{0}\else%
%         \edef\@@@tmp{\@nameuse{aucount\theaub@@}}\fi% 
%        \@tempcnta=0
%        \@nameuse{cupauthors\theaub@@}
%        \@nameuse{cupaddress\theaub@@}\par\vskip10pt
%        \expandafter\ifx\csname
%           cupeads\theaub@@\endcsname\relax\relax\else
%           \let\eadsep\@empty           
%           Email: \@nameuse{cupeads\theaub@@}\par\vskip10pt
%        \fi
%      \stepcounter{aub@@}%
%    \repeat 
%\end{flushleft}%
%}

%\AtEndDocument{\EndMaketitleBox}
\AtEndDocument{\label{journal@Last@page}}

\def\FNtext#1{\par\bgroup\footnotesize#1\egroup}
\newdimen\space@left
\def\alarm#1{\typeout{******************************}%
             \typeout{#1}%
             \typeout{******************************}%
}
\long\def\getSpaceLeft{%\global\@twocolumnfalse%
   \global\setbox0=\vbox{\hsize=\textwidth\MaketitleBox}%
   \global\setbox1=\vbox{\hsize=\textwidth
    \let\footnotetext\FNtext
    \printFirstPageNotes}%
    \xdef\noteheight{\the\ht1}%
    \xdef\titleheight{\the\ht0}%
    \@tempdima=\vsize
    \advance\@tempdima-\noteheight
    \advance\@tempdima-1\baselineskip
}

\skip\footins=24pt

\newbox\els@boxa
\newbox\els@boxb

\def\cup@title@banner{\smash{\lower10pt\hbox{\hskip-1in%
  \hskip-\oddsidemargin 
  %\includegraphics[width=\paperwidth]%
  %{\@jid-banner-title.pdf}
  }}}

\def\cup@pages@banner{{\smash{\lower-.4pt\hbox{%
  \ifodd\thepage\relax\dimen0 1in \advance 
  \dimen0 \oddsidemargin \hskip-\dimen0
  \else \dimen0 1in \advance \dimen0 \evensidemargin 
  \hskip-\dimen0 \fi%
  %\includegraphics[width=\paperwidth]{\@jid-banner-pages.pdf}
  }}}}

\ifpreprint
 \def\maketitle{\pprintMaketitle}
  \else
   \ifnum\jtype=1
    \def\maketitle{\cup@title@banner%
      \iflongmktitle\getSpaceLeft
       \global\setbox\els@boxa=\vsplit0 to \@tempdima
       \box\els@boxa\par\resetTitleCounters
       \thispagestyle{pprintTitle}%
       \printFirstPageNotes
       \box0%
      \else
       \finalMaketitle\printFirstPageNotes
      \fi
    \gdef\thefootnote{\arabic{footnote}}}%
  \else
 \ifnum\jtype=5
    \def\maketitle{\cup@title@banner%
      \iflongmktitle\getSpaceLeft
       \global\setbox\els@boxa=\vsplit0 to \@tempdima
       \box\els@boxa\par\resetTitleCounters
       \thispagestyle{pprintTitle}%
       \printFirstPageNotes
       \twocolumn[\box0]%\printFirstPageNotes
      \else
       \twocolumn[\finalMaketitle]\printFirstPageNotes
     \fi
     \gdef\thefootnote{\arabic{footnote}}}
  \else
  \if@twocolumn
    \def\maketitle{\cup@title@banner%
      \iflongmktitle\getSpaceLeft
       \global\setbox\els@boxa=\vsplit0 to \@tempdima
       \box\els@boxa\par\resetTitleCounters
       \thispagestyle{pprintTitle}%
       \printFirstPageNotes
       \twocolumn[\box0]%
      \else
       \twocolumn[\finalMaketitle]\printFirstPageNotes
      \fi
     \gdef\thefootnote{\arabic{footnote}}}%
   \else
    \def\maketitle{\cup@title@banner%
      \iflongmktitle\getSpaceLeft
       \global\setbox\els@boxa=\vsplit0 to \@tempdima
       \box\els@boxa\par\resetTitleCounters
       \thispagestyle{pprintTitle}%
       \printFirstPageNotes
       \box0%
     \else
       \finalMaketitle\printFirstPageNotes
      \fi
    \gdef\thefootnote{\arabic{footnote}}}%
   \fi
  \fi
 \fi
\fi

\let\@cuparticlemyfooter\@empty
\let\@cuparticlemyfooteralign\@empty
\def\@cuparticlemyfooteralignleft{L}
\def\@cuparticlemyfooteralignright{R}
\def\@cuparticlemyfooteraligncenter{C}

\def\myfooter[#1]#2 %*%
      {\gdef\@cuparticlemyfooteralign{#1}
       \gdef\@cuparticlemyfooter{#2}}


\def\myfooterfont#1{\gdef\@myfooterfont{#1}}
\myfooterfont{\footnotesize\itshape}
\def\ps@xpprintTitle{%
     \let\@oddhead\@empty
     \let\@evenhead\@empty
     \def\@oddfoot
       {\hbox to \textwidth%
        {\ifnopreprintline\relax\else
        \@myfooterfont%
         \ifx\@cuparticlemyfooteralign\@cuparticlemyfooteraligncenter%
           \hfil\@cuparticlemyfooter\hfil%
         \else%
         \ifx\@cuparticlemyfooteralign\@cuparticlemyfooteralignleft%
           \@cuparticlemyfooter\hfill{}%
         \else%
         \ifx\@cuparticlemyfooteralign\@cuparticlemyfooteralignright%
           {}\hfill\@cuparticlemyfooter%
         \else%
               Preprint submitted to \ifx\@journal\@empty%
                 CUP%
            \else\@journal\fi\hfill\@date\fi%
         \fi%
         \fi%
         \fi%
         }
       }%
     \let\@evenfoot\@oddfoot}
\def\@seccntDot{.}
\def\@seccntformat#1{\csname the#1\endcsname\@seccntDot\hskip 0.5em}

\def\section{\@startsection
    {section}{1}{\z@}{-12\p@ \@plus6\p@ \@minus6\p@}
    {6\p@ \@plus2\p@ \@minus2\p@}{\reset@font\centering
    \nfontsize{10.56}{12.67}\bfseries
    \color{cupblue}\mathversion{bold}\aftergroup\resetsection}}
\def\resetsection{%
   \def\section{\@startsection
    {section}{1}{\z@}{15\p@ \@plus6\p@ \@minus6\p@}
    {6\p@ \@plus2\p@ \@minus2\p@}{\reset@font\centering
    \nfontsize{10.56}{12.67}\bfseries
    \color{cupblue}\mathversion{bold}}}}
\def\subsection{\@startsection
    {subsection}{2}{\z@}{6\p@ \@plus2\p@ \@minus2\p@}
    {-9\p@}{\reset@font\bfseries\mathversion{bold}\aftergroup\sec@bdot}}%
\def\sec@bdot{\textbf{.}}
\def\subsubsection{\@startsection
    {subsubsection}{3}{\z@}{6\p@ \@plus2\p@ \@minus2\p@}
    {-9\p@}{\reset@font\normalsize\itshape\aftergroup.}}%

\def\ack{\section*{Acknowledgement}}
\def\acks{\section*{Acknowledgements}}

\def\suppmat{\section*{Suppelmentary Material}}


\newdimen\leftMargin
\leftMargin=2em
\newtoks\@enLab  %\newtoks\@enfont
\def\@enQmark{?}
\def\@enLabel#1#2{%
  \edef\@enThe{\noexpand#1{\@enumctr}}%
  \@enLab\expandafter{\the\@enLab\csname the\@enumctr\endcsname}%
  \@enloop}
\def\@enSpace{\afterassignment\@enSp@ce\let\@tempa= }
\def\@enSp@ce{\@enLab\expandafter{\the\@enLab\space}\@enloop}
\def\@enGroup#1{\@enLab\expandafter{\the\@enLab{#1}}\@enloop}
\def\@enOther#1{\@enLab\expandafter{\the\@enLab#1}\@enloop}
\def\@enloop{\futurelet\@entemp\@enloop@}
\def\@enloop@{%
  \ifx A\@entemp         \def\@tempa{\@enLabel\Alph  }\else
  \ifx a\@entemp         \def\@tempa{\@enLabel\alph  }\else
  \ifx i\@entemp         \def\@tempa{\@enLabel\roman }\else
  \ifx I\@entemp         \def\@tempa{\@enLabel\Roman }\else
  \ifx 1\@entemp         \def\@tempa{\@enLabel\arabic}\else
  \ifx \@sptoken\@entemp \let\@tempa\@enSpace         \else
  \ifx \bgroup\@entemp   \let\@tempa\@enGroup         \else
  \ifx \@enum@\@entemp   \let\@tempa\@gobble          \else
                         \let\@tempa\@enOther
             \fi\fi\fi\fi\fi\fi\fi\fi
  \@tempa}
\newlength{\@sep} \newlength{\@@sep}
\setlength{\@sep}{.5\baselineskip plus.2\baselineskip
            minus.2\baselineskip}
\setlength{\@@sep}{.1\baselineskip plus.01\baselineskip
            minus.05\baselineskip}
\providecommand{\sfbc}{\rmfamily\upshape}
\providecommand{\sfn}{\rmfamily\upshape}
\def\@enfont{\ifnum \@enumdepth >1\let\@nxt\sfn \else\let\@nxt\sfbc \fi\@nxt}

%% Input from enumerate.sty
\def\enumerate{%
  \ifnum \@enumdepth >3 \@toodeep\else
      \advance\@enumdepth \@ne
      \edef\@enumctr{enum\romannumeral\the\@enumdepth}\fi
  \@ifnextchar[{\@@enum@}{\@enum@}}
\def\@@enum@[#1]{%
  \@enLab{}\let\@enThe\@enQmark
  \@enloop#1\@enum@
  \ifx\@enThe\@enQmark\@warning{The counter will not be printed.%
   ^^J\space\@spaces\@spaces\@spaces The label is: \the\@enLab}\fi
  \expandafter\edef\csname label\@enumctr\endcsname{\the\@enLab}%
  \expandafter\let\csname the\@enumctr\endcsname\@enThe
  \csname c@\@enumctr\endcsname7
  \expandafter\settowidth
            \csname leftmargin\romannumeral\@enumdepth\endcsname
            {\the\@enLab\hspace{\labelsep}}%
  \@enum@}
\def\@enum@{\list{\csname label\@enumctr\endcsname}%
           {\usecounter{\@enumctr}\def\makelabel##1{\hss\llap{##1}}}}
%% end of input from enumerate.sty
\def\sitem{\@noitemargtrue\@item[\@itemlabel *]}

\def\itemize{\@ifnextchar[{\@Itemize}{\@Itemize[]}}

\def\@Itemize[#1]{\def\next{#1}%
  \ifnum \@itemdepth >\thr@@\@toodeep\else
   \advance\@itemdepth\@ne
  \ifx\next\@empty\else\expandafter\def\csname
   labelitem\romannumeral\the\@itemdepth\endcsname{#1}\fi%
  \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
  \expandafter\list\csname\@itemitem\endcsname
  {\def\makelabel##1{\hss\llap{##1}}}%
 \fi}

%\def\enunheadstyle{\color{cupmagenta}\scshape}
\def\enunheadstyle{\color{cupblue}\scshape}

\def\newdefinition#1{%
  \@ifnextchar[{\@odfn{#1}}{\@ndfn{#1}}}%]
\def\@ndfn#1#2{%
  \@ifnextchar[{\@xndfn{#1}{#2}}{\@yndfn{#1}{#2}}}
\def\@xndfn#1#2[#3]{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}\@newctr{#1}[#3]%
     \expandafter\xdef\csname the#1\endcsname{%
       \expandafter\noexpand\csname the#3\endcsname \@dfncountersep
          \@dfncounter{#1}}%
     \global\@namedef{#1}{\@dfn{#1}{#2}}%
     \global\@namedef{end#1}{\@enddefinition}}}
\def\@yndfn#1#2{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}%
     \expandafter\xdef\csname the#1\endcsname{\@dfncounter{#1}}%
     \global\@namedef{#1}{\@dfn{#1}{#2}}%
     \global\@namedef{end#1}{\@enddefinition}}}
\def\@odfn#1[#2]#3{%
  \@ifundefined{c@#2}{\@nocounterr{#2}}%
    {\expandafter\@ifdefinable\csname #1\endcsname
    {\global\@namedef{the#1}{\@nameuse{the#2}}
  \global\@namedef{#1}{\@dfn{#2}{#3}}%
  \global\@namedef{end#1}{\@enddefinition}}}}
\def\@dfn#1#2{%
  \refstepcounter{#1}%
  \@ifnextchar[{\@ydfn{#1}{#2}}{\@xdfn{#1}{#2}}}
\def\@xdfn#1#2{%
  \@begindefinition{#2}{\csname the#1\endcsname}\ignorespaces}
\def\@ydfn#1#2[#3]{%
  \@opargbegindefinition{#2}{\csname the#1\endcsname}{#3}\ignorespaces}
\def\@dfncounter#1{\noexpand\arabic{#1}}
\def\@dfncountersep{.}
\def\@begindefinition#1#2{\trivlist
   \item[\hskip\labelsep{\enunheadstyle #1\ #2.}]\upshape}
\def\@opargbegindefinition#1#2#3{\trivlist
      \item[\hskip\labelsep{\enunheadstyle #1\ #2\ \normalfont(#3).}]\upshape}
\def\@enddefinition{\endtrivlist}

\def\@begintheorem#1#2{\trivlist
  \let\baselinestretch\@blstr
   \item[\hskip \labelsep{\enunheadstyle #1\ #2.}]\itshape}
\def\@opargbegintheorem#1#2#3{\trivlist
  \let\baselinestretch\@blstr
      \item[\hskip \labelsep{\enunheadstyle #1\ #2\ \normalfont(#3).}]\itshape}

\def\newproof#1{%
  \@ifnextchar[{\@oprf{#1}}{\@nprf{#1}}}
\def\@nprf#1#2{%
  \@ifnextchar[{\@xnprf{#1}{#2}}{\@ynprf{#1}{#2}}}
\def\@xnprf#1#2[#3]{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}\@newctr{#1}[#3]%
     \expandafter\xdef\csname the#1\endcsname{%
       \expandafter\noexpand\csname the#3\endcsname \@prfcountersep
          \@prfcounter{#1}}%
     \global\@namedef{#1}{\@prf{#1}{#2}}%
     \global\@namedef{end#1}{\@endproof}}}
\def\@ynprf#1#2{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}%
     \expandafter\xdef\csname the#1\endcsname{\@prfcounter{#1}}%
     \global\@namedef{#1}{\@prf{#1}{#2}}%
     \global\@namedef{end#1}{\@endproof}}}
\def\@oprf#1[#2]#3{%
  \@ifundefined{c@#2}{\@nocounterr{#2}}%
    {\expandafter\@ifdefinable\csname #1\endcsname
    {\global\@namedef{the#1}{\@nameuse{the#2}}%
  \global\@namedef{#1}{\@prf{#2}{#3}}%
  \global\@namedef{end#1}{\@endproof}}}}
\def\@prf#1#2{%
  \refstepcounter{#1}%
  \@ifnextchar[{\@yprf{#1}{#2}}{\@xprf{#1}{#2}}}
\def\@xprf#1#2{%
  \@beginproof{#2}{\csname the#1\endcsname}\ignorespaces}
\def\@yprf#1#2[#3]{%
  \@opargbeginproof{#2}{\csname the#1\endcsname}{#3}\ignorespaces}
\def\@prfcounter#1{\noexpand\arabic{#1}}
\def\@prfcountersep{.}
\def\@beginproof#1#2{\trivlist\let\baselinestretch\@blstr
   \item[\hskip \labelsep{\enunheadstyle #1.}]\rmfamily}
\def\@opargbeginproof#1#2#3{\trivlist\let\baselinestretch\@blstr
      \item[\hskip \labelsep{\enunheadstyle #1\ \normalfont(#3).}]\rmfamily}
\def\@endproof{\endtrivlist}
\newcommand*{\qed}{\hbox{}\hfill$\Box$}

\@ifundefined{@biboptions}{\xdef\@biboptions{numbers}}{}
\InputIfFileExists{\jobname.spl}{}{}
\ifnonatbib\relax\else
  \RequirePackage[\@biboptions]{natbib}
\fi
\newwrite\splwrite
\immediate\openout\splwrite=\jobname.spl
\def\biboptions#1{\def\next{#1}\immediate\write\splwrite{%
   \string\g@addto@macro\string\@biboptions{%
    ,\expandafter\strip@prefix\meaning\next}}}

\let\baselinestretch=\@blstr

\RequirePackage{geometry}

\ifnum\jtype=1

\geometry{%
  twoside,
%  textwidth=30pc,textheight=45pc,
  textwidth=28pc,%
  textheight=42pc,
%  top=37mm,
%  top=15mm,
  top=16.5mm,
  headsep=15pt,
  headheight=74pt,
  footskip=40pt,
%  paperheight=247mm,paperwidth=174mm,
  paperheight=210mm,paperwidth=148mm,
  centering,
  hoffset=0pt}

%\topmargin -30mm
%\oddsidemargin 1.3mm
%\evensidemargin -5mm

 \global\let\bibfont=\footnotesize
 \global\bibsep=0pt
\else
\geometry{%
  twoside,
  textwidth=30pc,
  textheight=45pc,
  top=37mm,
  headsep=15pt,
  headheight=74pt,
  footskip=22pt,
  paperheight=247mm,
  paperwidth=174mm,
  hoffset=0pt}

\topmargin -30mm
%\oddsidemargin 1.3mm
%\evensidemargin -5mm

 \global\let\bibfont=\footnotesize
 \global\bibsep=0pt

\fi
\def\journal#1{\gdef\@journal{#1}}

\def\@bsl@glue{\global\baselineskip=\the \baselineskip 
 plus 1pt minus 1pt  \flushbottom
}

\newenvironment{frontmatter}{}{\maketitle
\aftergroup\@bsl@glue }

\long\def\@makecaption#1#2{\vskip\abovecaptionskip{%
        \setbox0=\vbox{\footnotesize\baselineskip=9\p@
        {\color{cupbrown}\rm #1.\ #2}}%
        \setbox0=\vbox{\unvbox0 \setbox1=\lastbox
        \setbox1=\hbox to \textwidth
            {\hfill\unhbox1\hfill}\box1}\box0}\par
        \vspace*{3\p@}}

\ifc@loured
   \RequirePackage[bookmarks=false,
                 colorlinks=true,urlcolor=black,
                 citecolor=black,linkcolor=black,
                 pdfstartview={FitH 897},
                 pdfpagescrop={0 0 595.276 782.362}]{hyperref}
\else
  \def\t@driver{hdvips}
  \RequirePackage[bookmarks=false,
                 colorlinks=true,urlcolor=black,
                 citecolor=black,linkcolor=black,
                 pdfpagelayout=Continuous,
                 breaklinks=true,
                 pdfstartview={FitH 897},
                 pdfpagescrop={0 0 595.276 782.362}]{hyperref}
  \ifx\Hy@driver\t@driver\else \hypersetup{draft}\fi
  \Hy@Info{Bookmarks OFF}%
\fi

\ifc@loured
  \definecolor{cupgreen}{rgb}{0.247,0.498,0.208}
%  \definecolor{cupblue}{rgb}{0,0,1}
  \definecolor{cupblue}{cmyk}{.79,0,.26,0}
  \definecolor{cupred}{rgb}{1,0.04,0}
  \definecolor{cuppink}{rgb}{0.925,0,0.545}
  \definecolor{cupmagenta}{rgb}{0.624,0.161,0.424}
  \definecolor{cupbrown}{rgb}{0.71,0.212,0.133}
\else
  \definecolor{cupgreen}{rgb}{0,0,0}
  \definecolor{cupblue}{rgb}{0,0,0}
  \definecolor{cupred}{rgb}{0,0,0}
  \definecolor{cuppink}{rgb}{0,0,0}
  \definecolor{cupmagenta}{rgb}{0,0,0}
  \definecolor{cupbrown}{rgb}{0,0,0}
\fi

\gdef\@linkcolor{cupred}
\gdef\@citecolor{cupred}

\AtBeginDocument{\@ifpackageloaded{hyperref}
  {%
\begingroup
  \@makeother\`%
  \@makeother\=%
  \edef\x{%
    \edef\noexpand\x{%
      \endgroup
      \noexpand\toks@{%
        \catcode 96=\noexpand\the\catcode`\noexpand\`\relax
        \catcode 61=\noexpand\the\catcode`\noexpand\=\relax
      }%
    }%
    \noexpand\x
  }%
\x
\@makeother\`
\@makeother\=
}{}}
%
% Consider using \RequirePackage[title]{appendix}
% 
\def\appendixname{Appendix }
\renewcommand\appendix{\par
  \setcounter{section}{0}%
  \setcounter{subsection}{0}%
  \setcounter{equation}{0}
  \gdef\thefigure{\@Alph\c@section.\arabic{figure}}%
  \gdef\thetable{\@Alph\c@section.\arabic{table}}%
  \gdef\thesection{\appendixname~\@Alph\c@section}%
  \@addtoreset{equation}{section}%
  \gdef\theequation{\@Alph\c@section.\arabic{equation}}%
  \addtocontents{toc}{\string\let\string\numberline\string\tmptocnumberline}{}{}
}

%%%% \numberline width calculation for appendix.
\newdimen\appnamewidth
\def\tmptocnumberline#1{%
   \setbox0=\hbox{\appendixname}%
   \appnamewidth=\wd0
   \addtolength\appnamewidth{2.5pc}%
   \hb@xt@\appnamewidth{#1\hfill}%
}

%% Added for work with amsrefs.sty

\@ifpackageloaded{amsrefs}%
  {}
  {%\let\bibsection\relax%
  \AtBeginDocument{\def\cites@b#1#2,#3{%
    \begingroup[%
        \toks@{\InnerCite{#2}#1}%
        \ifx\@empty#3\@xp\@gobble\fi
        \cites@c#3%
      }%
    }%
  }

\def\textmarker#1#2{\textcolor{#1}{#2}}%*%

\ifNAT@numbers%
\let\therefsection\@empty
\long\def\refsection#1{\def\therefsection{#1}}
\AtBeginDocument{%
\def\makelabel#1{\hbox to\labelwidth{#1\hss}}
\def\thebibliography#1{%
  \section*{\refname}%
  \ifx\therefsection\@empty\else{\footnotesize\therefsection}\fi
  \list{[{\arabic{enumi}}]}%
  {\def\makelabel##1{{\hfill##1}\unskip\hss}%
   \topsep=\z@\parsep=\z@
   \partopsep=\z@\itemsep=\z@
   \labelsep=10\p@\itemindent=\z@
   \settowidth\labelwidth{\footnotesize[#1]}%
   \leftmargin\labelwidth
   \advance\leftmargin\labelsep
   \advance\leftmargin -\itemindent
   \usecounter{enumi}}%
  \footnotesize
  \def\newblock{\ }%
  \sloppy\clubpenalty4000\widowpenalty4000%
  \sfcode`\.=1000\relax
}
\def\endthebibliography{\let\therefsection\@empty
      \endlist}
%      \endlist\aftergroup\putAffiliation}
}  % end of AtBeginDocument
\fi

\ifnofootmarks
 \def\fnmark[#1]{}
\fi

\DeclareSymbolFont{CMRi}{OT1}{cmr}{m}{it}
\SetSymbolFont{CMRi}{bold}{OT1}{cmr}{bx}{it}
\DeclareMathSymbol{v}{\mathalpha}{CMRi}{`v}

\endinput
%%
%% End of file `cuparticle.cls'.
