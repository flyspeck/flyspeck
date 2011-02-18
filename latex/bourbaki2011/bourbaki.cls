
%%
%% This is file `bourbaki.cls',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% smfclass.dtx  (with options: `asterki')
%% 
%%
%%  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  %% Classes, paquetages pour les publications de la SMF %%
%%  %% (c) 1999-2001 Societe mathematique de France        %%
%%  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
\ProvidesClass{bourbaki}
     [2003/02/21 v2.1c
     Classe LaTeX pour les seminaires Bourbaki
     (Asterisque ou Brochure)]
\def\filename{bourbaki.cls}
\def\fileversion{2.1c}       \def\filedate{2003-02-21}
\immediate\write16{%
LaTeX document class `BOURBAKI' (\fileversion, \filedate)}
\DeclareOption{11pt}{\typeout{Desole --- le volume est en 10 points}}
\DeclareOption{12pt}{\typeout{Desole --- le volume est en 10 points}}
\newif\if@brochure
\DeclareOption{brochure}{\typeout{Brochure Bourbaki : 12 points, etc.}%
     \PassOptionsToClass{12pt}{smfart}%
     \@brochuretrue}
\DeclareOption{twocolumn}{\typeout{Desole ---
      une seule colonne dans le style BOURBAKI.}}
\DeclareOption{openbib}{\typeout{Desole ---
      pas d'option openbib dans le style BOURBAKI.}}
\DeclareOption{fleqn}{\typeout{Desole ---
      pas d'equations a gauche dans le style BOURBAKI.}}
\DeclareOption{titlepage}{\typeout{Desole ---
      pas d'option titlepage dans le style BOURBAKI.}}
\def\@bbklanguage{2}
\DeclareOption{french}%
  {\typeout{Style BOURBAKI -- version francaise}\def\@bbklanguage{1}%
   \PassOptionsToClass{french}{smfart}}
\DeclareOption{francais}%
  {\typeout{Style BOURBAKI -- version francaise}\def\@bbklanguage{1}%
   \PassOptionsToClass{french}{smfart}}
\DeclareOption{english}%
  {\typeout{Style BOURBAKI -- english version}\def\@bbklanguage{0}%
   \PassOptionsToClass{english}{smfart}}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{smfart}}

\newif\if@bbkswapnumbers
\DeclareOption{swapnumbers}
  {\typeout{Style BOURBAKI -- num\'eros avant les intitul\'es}%
   \@bbkswapnumberstrue}

\newif\if@bbkmaster
\DeclareOption{master}{\@bbkmastertrue}

\newif\if@draft


\ExecuteOptions{10pt,a4paper,twoside}
\ProcessOptions\relax

\def\smf@getfirstpage{\gdef\smf@firstpage{1}}
\def\smf@getlastpage{\clearpage
  {\advance\c@page-1 \xdef\smf@lastpage{\arabic{page}}}}
\def\smf@pages{\smf@firstpage-\smf@lastpage}

\if@bbkmaster
  \if@brochure
  \ClassWarning{bourbaki}{Options brochure et master incompatibles.
J'ignore l'option brochure.}%
  \@brochurefalse
  \fi
  \message{Fichier ma\^{\i}tre d'un Ast\'erisque Bourbaki...}
  \LoadClass{smfbook}
  \def\@classname{smfbook}
  \RequirePackage{smfenum}
  \RequirePackage[noxy]{asterisque}
  \RequirePackage[master]{smfmulti}
  \addto\do@paperrefs{\do\smf@subtitle\smf@subtitle
                      \do\smf@altsubtitle\smf@altsubtitle
                      \do\smf@bbknumero\smf@bbknumero
                      \do\smf@keywords\smf@keywords
                      \do\smf@subjclass\smf@subjclass}
  \addto\do@volumerefs{\do\smf@bbkannee\@bbkannee}
  \def\@pnumwidth{3em}

\else
  \LoadClass{smfart}
  \def\@classname{smfart}
  \if@brochure
    \textwidth 13cm
    \textheight 21.5cm
    \headheight=12pt
    \headsep 12mm
    \footskip 12mm
    \textwidth  1.2\textwidth
    \textheight 1.2\textheight
    \calclayout
    \RequirePackage{amsmath,amsfonts,amssymb}
  \else
    \RequirePackage{smfenum}
    \RequirePackage[noxy]{asterisque}
    \RequirePackage{smfmulti}
    \addto\do@paperrefs{\do\smf@subtitle\@subtitle
                        \do\smf@altsubtitle\@altsubtitle
                        \do\smf@bbknumero\@bbknumero
                        \do\smf@keywords\@keywords
                        \do\smf@subjclass\@subjclass}
    \addto\do@volumerefs{\do\smf@bbkannee\smf@bbkannee}
  \fi
\fi


\def\altsubtitle#1{\def\@altsubtitle{#1}}
\def\@altsubtitle{}
\def\subtitle#1{\def\@subtitle{#1}}
\def\@subtitle{}

\def\@setaltabstracthead{\abstractheadfont \altabstractname
  \ifx\@alttitle\@empty\else\ \textup(\emph{\@alttitle}%
       \ifx\@altsubtitle\@empty\else
            \ \textup[\emph{\@altsubtitle}\textup]\fi\textup)\fi}

\def\@bbknumero{}\def\smf@bbknumero{}
\def\@bbkannee{}\def\smf@bbkannee{}
\def\bbknumero#1{\gdef\@bbknumero{#1}\gdef\smf@bbknumero{#1}}
\def\bbkannee#1{\gdef\@bbkannee{#1}}

\if@bbkmaster

\def\smf@titleii{\clearpage
  \thispagestyle{empty}
  \ifx\@empty\addresses\else \@setaddresses\fi
  \vfill
  \hrule
  \bigskip
  \@setkeyclass
  \bigskip
  \hrule
  \vfilneg
}

\def\@setkeyclass{%
  \bgroup
  \def\baselinestretch{1}
  \abstractfont\smaller[2]
  {\abstractheadfont
   Mots clefs et classification math\'ematique par sujets \textup{(2000)}\par
   \medskip}
   \def\donot##1{}
   \let\do\do@setkeyclass
   \smf@files
  \egroup
}

\def\do@setkeyclass #1{\bgroup
   \smf@read{#1}%
   \noindent
   {\bfseries Expos\'e n\textsuperscript o \smf@bbknumero\MakePointrait}%
   \enspace\ignorespaces
   \smf@keywords\MakePointrait\enspace\ignorespaces
   \smf@subjclass\@addpunct. \par\egroup}

\def\smf@titleiii{%
  \clearpage\thispagestyle{copyright}
  \markboth{\@nx\shorttitle}{\@nx\shorttitle}
  %% INSERER UNE IMAGE
  \null
  \vskip 12\medskipamount plus 8\medskipamount
  \begin{center}\Large\bfseries\smf@boldmath
  {\MakeUppercase\@title\par}
  \end{center}
  \vskip 8\medskipamount plus 4 \medskipamount
  \@setabstract\par
  \vskip 1\bigskipamount plus 1\bigskipamount
     \penalty-100
  \@setaltabstract\par
}


%% Modifications smfmulti

\def\smfmulti@protect{%
  \let\do\relax
  \let\donot\relax
  \let\bourbakisession\relax}

\def\smf@addfile#1{\bgroup
     \smfmulti@protect
     \smf@toks=\expandafter{\smf@newfiles}%
     \xdef\smf@newfiles{\the\smf@toks\do{#1}}%
   \egroup}

\def\bbksession#1{\addtocontents{toc}{\protect\bourbakisession{#1}}%
   \bgroup
     \smfmulti@protect
     \smf@toks=\expandafter{\smf@newfiles}%
     \xdef\smf@newfiles{\the\smf@toks\donot{\bourbakisession{#1}}}
  \egroup
}

\DeclareRobustCommand{\bourbakisession}[1]{\bigskip
      \noindent
      {\itshape\MakeUppercase{#1}}\par\medskip}


%%% Table des matieres

\def\ps@contents{
  \def\@oddfoot{\normalfont\Tiny\hfil
     {\smf@LOGO\ \@setyear}}%
  \def\@evenfoot{\normalfont\tiny
     {\MakeUppercase\smf@titrecourt
      \ifx\smf@volume\@empty\else{\unskip\ \smf@volume}\fi\hfil}}%
  \def\@evenhead{\normalfont\scriptsize
     \rlap{\bfseries\thepage}\hfil {\itshape TABLE DES MATI\`ERES}\hfil}%
  \def\@oddhead{\normalfont\scriptsize
     \def\\{\unskip\space\ignorespaces}%
     \hfil {\itshape TABLE DES MATI\`ERES}\hfil
           \llap{\bfseries\thepage}}%
  \let\@mkboth\org@markboth
    }

\def\l@chapter{\@tocline{0}{0pt}{0pt}{}{}}

\def\tableofcontents{\begingroup
  \cleardoublepage
  \pagestyle{contents}\thispagestyle{contents}
  \hbox{}\vfil
  \typeout{Table des matieres}%
  \makeatletter
  \@input{\jobname.toc}%
  \global\@nobreakfalse \endgroup
  \newpage }

\def\do@smftoc #1{%
  \smf@read {#1}
  \makeatletter
  \@tocline{-2}{4pt plus 2pt}{0pt}{4em}{}{%
  {\def\smfandname{\&}\andify\smf@authors
   \hbox to 3em{\smf@bbknumero\hss}\smf@authors}
   ---
   {\itshape\let\\\relax\ignorespaces\smf@title\unskip\space
    \ifx\smf@subtitle\@empty\else
         \textup[\smf@subtitle\unskip\textup]\space\fi }}%
   {\smf@firstpage}
}

%% Resumes

\newskip \resumepreskipamount
\resumepreskipamount 18pt plus 6pt minus 6pt  % 1.5 \bigskipamount
\def\smftableofresumes{%%
  \bgroup
  \cleardoublepage
  \def\baselinestretch{1}\small
  \let\@secnumber\@empty
  \addcontentsline{toc}{chapter}{R\'esum\'es des expos\'es}
  \pagestyle{resumes}
%% IL FAUDRAIT SE DEBROUILLER POUR QU'IL Y EN AIT EXACTEMENT 5 PAR PAGE !
   \def\donot##1{##1}
   \def\bourbakisession##1{\clearpage}
  \def\do##1{\vskip\resumepreskipamount
             \do@smfresume{##1}}
  \smf@files\clearpage
  \egroup}

\def\do@smfresume #1{\bgroup
   \smf@read{#1}%
   \edef\@tempa{\noexpand\smf@silentselectlanguage{\smf@langue}}\@tempa
   \vbox{%
   \noindent
   {\def\smfandname{\&}\andify \smf@authors
     \normalfont
     \smf@authors } --
    {\itshape\let\\\relax\ignorespaces\smf@title\unskip
     \ifx\smf@subtitle\@empty\else
            \space\ignorespaces\textup[\smf@subtitle\textup]\fi}}
    \par\nobreak
    \def\smf@tempa{english}\ifx\smf@langue\smf@tempa
       \smf@abstract\else\smf@resume\fi\par
    \egroup
}

\def\ps@resumes{
  \def\@oddfoot{\normalfont\Tiny\hfil
     {\smf@LOGO\ \@setyear}}%
  \def\@evenfoot{\normalfont\tiny
     {\MakeUppercase\smf@titrecourt
      \ifx\smf@volume\@empty\else{\unskip\ \smf@volume}\fi\hfil}}%
  \def\@evenhead{\normalfont\scriptsize
     \rlap{\bfseries\thepage}\hfil {\itshape R\'ESUM\'ES DES EXPOS\'ES}\hfil}%
  \def\@oddhead{\normalfont\scriptsize
     \def\\{\unskip\space\ignorespaces}%
     \hfil {\itshape R\'ESUM\'ES DES EXPOS\'ES}\hfil
           \llap{\bfseries\thepage}}%
  \let\@mkboth\org@markboth
    }

%% Derniere de couv.

\else
  \let\@mkboth\@gobbletwo
  \let\partmark\@gobble\let\sectionmark\@gobble
  \let\subsectionmark\@gobble

  \def\@setthanks{\def\thanks##1{##1\@addpunct{{\upshape.}}}\thankses}
  \if@brochure

    \def\ps@copyright{\ps@empty}
    \def\ps@expose{\ps@empty
    \def\@evenhead{\normalfont
           \hfil \@bbknumero--\ifnum\c@page<10 0\fi\the\c@page\hfil}
    \let\@oddhead\@evenhead }
    \ps@expose

  \else

  \def\ps@copyright{\ps@empty
    \def\@oddfoot{\normalfont\Tiny\hfil {\smf@LOGO\ \@setyear}}%
    \def\@evenfoot{\normalfont\tiny
        {\MakeUppercase\smf@titrecourt
        \ifx\smf@volume\@empty\else{\unskip\ \smf@volume}\fi\hfil}}}
  \def\ps@expose{%
    \def\@oddfoot{\normalfont\Tiny\hfil {\smf@LOGO\ \@setyear}}%
    \def\@evenfoot{\normalfont\tiny
       {\MakeUppercase\smf@titrecourt
        \ifx\smf@volume\@empty\else{\unskip\ \smf@volume}\fi\hfil}}%
    \def\@evenhead{\normalfont\scriptsize
       \rlap{\bfseries\thepage}\hfil {\itshape \leftmark{}{}}\hfil}%
    \def\@oddhead{\normalfont\scriptsize
       \def\\{\unskip\space\ignorespaces}%
       \hfil {\itshape (\@bbknumero)\quad \rightmark{}{}}\hfil
             \llap{\bfseries\thepage}}%
    \let\@mkboth\org@markboth }
  \ps@expose

  \fi

  \def\@maketitle{%
  \cleardoublepage
    \thispagestyle{copyright}
  \parindent=0pt \normalfont\normalsize
  \let\@makefnmark\relax  \let\@thefnmark\relax
%% REMERCIEMENTS
  \ifx\@empty\thankses\else\@footnotetext{\@setthanks}\fi
  \topskip0\p@ %% on commence tout en haut.
%% L'ENTETE
  {\let\\\relax
   \uppercasenonmath\shorttitle
   \ifx\@empty\shortauthors \let\shortauthors\shorttitle
     \else \uppercasenonmath\shortauthors \andify\shortauthors \fi
     \toks@\@xp{\shortauthors}\@temptokena\@xp{\shorttitle}%
     \edef\@tempa{\@nx\markboth{\the\toks@}{\the\@temptokena}}%
   \@tempa}
  \vtop to 55 true mm{%
  \hbox to\textwidth{S\'eminaire BOURBAKI\hfil \@date}
  \hbox to\textwidth{\if@brochure
     \@bbkannee, n\raise4pt\hbox{\small o} \@bbknumero\else
     \smf@bbkannee, n\raise4pt\hbox{\small o} \@bbknumero,
        p.~\smf@firstpage\ \`a \smf@lastpage
    \fi
    \hss}
    \vfil
    {\centering\bf
     \MakeUppercase\@title \@@par
     \ifx\@empty\@subtitle\else\textup[\@subtitle\textup]\@@par\fi
     \bigskip
     {\normalfont \smfbyname\ }\authors\@@par
    \vfil
    \ifx\@empty\@dedicatory
         \else{\raggedleft\it\@dedicatory\@@par}\vfil\fi}\par}%
  }


\renewcommand{\author}[2][]{%
  \ifx\@empty\authors
    \gdef\shortauthors{#1}\gdef\authors{#2}%
  \else
    \g@addto@macro\shortauthors{\and#1}%
    \g@addto@macro\authors{\and#2}%
  \fi
  \g@addto@macro\addresses{\author{#2}}%
}

\def\@setaddresses{\par
  \nobreak \begingroup
  \parindent \addressindent\normalfont
  \def\author##1{\begingroup
    \addvspace\bigskipamount \indent ##1\par\endgroup}%
  \def\\{\par\nobreak\ignorespaces}%
  \interlinepenalty\@M
  \def\address##1##2{\begingroup
    \par\nobreak\addvspace\medskipamount\indent
    \@ifnotempty{##1}{(\ignorespaces##1\unskip) }%
    {\normalfont\ignorespaces##2}\par\endgroup}%
  \def\curraddr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent{\itshape Addresse courante}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}~:\space
      ##2\par\endgroup}}%
  \def\email##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent{\itshape \emailname}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}~:\space
      \ttfamily##2\par\endgroup}}%
  \def\urladdr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent{\itshape \urlname}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}~:\space
      \ttfamily##2\par\endgroup}}%
  \addresses
  \endgroup
}
\def\emailname{E-mail}
\def\urlname{Web}

\def\baselinestretch{1.1}
\parskip 0pt plus 4pt

\binoppenalty 2500 % normalement 700
\relpenalty 1500   % normalement 500

\newdimen\addressindent
\addressindent .5\textwidth

\fi

\def\part{\@startsection{part}{1}%
  \z@{3\linespacing\@plus\linespacing}{2\linespacing}%
  {\raggedright\normalfont\bfseries\smf@boldmath\MakeUppercase}}
\def\section{\@startsection{section}{1}%
  \z@{2\linespacing\@plus\linespacing}{\linespacing}%
  {\raggedright\normalfont\bfseries\smf@boldmath\MakeUppercase}}
\def\specialsection{\@startsection{section}{1}%
  \z@{2\linespacing\@plus\linespacing}{\linespacing}%
  {\centering\normalfont\bfseries\smf@boldmath\MakeUppercase}}
\let\sectionname\@empty
\def\subsection{\@startsection{subsection}{2}%
  \z@{.7\linespacing\@plus.7\linespacing}{.3\linespacing}
  {\normalfont\bfseries\smf@boldmath}}
\let\Subsection\subsection

\let\bibliosection\specialsection
\def\bibliofont{\normalfont}
  % {\def\baselinestretch{1.2}\normalfont}
  % \let\specialsection\section

\def\th@plain{%
  \let\thm@indent\noindent
  \thm@headfont{\normalfont\scshape}%
  \thm@notefont{\normalfont}%
  \thm@preskip.5\linespacing \@plus .5\linespacing
  \thm@postskip\thm@preskip
  \thm@headpunct{\pointrait}
  \itshape }
\def\th@definition{\th@plain }  %  was \upshape
\def\th@remark{\th@definition \thm@headfont{\itshape} \upshape}

%%%% THEOREMES, DEFINITIONS
\if@bbkswapnumbers\swapnumbers\fi

\theoremstyle{plain}
\newtheorem{defi}{\definame}[section]
\newtheorem{prop}[defi]{\propname}
\newtheorem{theo}[defi]{\theoname}
\newtheorem{conj}[defi]{\conjname}
\newtheorem{coro}[defi]{\coroname}
\newtheorem{fait}[defi]{\faitname}
\theoremstyle{definition}
\newtheorem{lemm}[defi]{\lemmname}
\theoremstyle{remark}
\newtheorem{rema}[defi]{\remaname}
\newtheorem{exem}[defi]{\exemname}
\theoremstyle{plain}

\newenvironment{enonce}[2][plain]%
  {\let\smfenonce\relax \theoremstyle{#1}%
   \newtheorem{smfenonce}[\smf@thm]{#2}%
    \begin{smfenonce}}%
    {\end{smfenonce}}%
\newenvironment{enonce*}[2][plain]%
    {\let\smfenonce\relax \theoremstyle{#1}%
     \newtheorem*{smfenonce}{#2}%
     \begin{smfenonce}}%
    {\end{smfenonce}}%

%%%% CITATIONS

\def\@cite#1#2{{%
 \m@th\upshape\mdseries[{#1}{\if@tempswa, #2\fi}]}}

%%%% FIN DU DOCUMENT

\g@addto@macro\smf@captionsenglish{\def\faitname{Fact}}
\g@addto@macro\smf@captionsfrench{\def\faitname{Fait}}



\def\smf@enddoc{%
  \par\vskip 2\bigskipamount
  \bgroup
  \def\baselinestretch{1}\normalfont
  \raggedright
  \ifx\@empty\@translators\else \@settranslators\medskip \fi
  \ifx\@empty\addresses   \else \@setaddresses             \fi
  \par\egroup}
\endinput
%%
%% End of file `bourbaki.cls'.

