%%
%% This is file `smfart.cls',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% smfclass.dtx  (with options: `article')
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
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{smfart}[2003/10/28 v1.3f
  Classe LaTeX pour les articles publies par la SMF]
\def\@classname{smfart}
\RequirePackage{amsgen}
\newcommand{\uppercasenonmath}[1]{\toks@\@emptytoks
  \@xp\@skipmath\@xp\@empty#1$$%
  \edef#1{\@nx\@upprep\the\toks@}%
}
\newcommand{\@upprep}{%
  \spaceskip1.3\fontdimen2\font plus1.3\fontdimen3\font
  \upchars@}
\newcommand{\upchars@}{%
  \def\ss{SS}\def\i{I}\def\j{J}\def\ae{\AE}\def\oe{\OE}%
  \def\o{\O}\def\aa{\AA}\def\l{\L}\def\Mc{M{\scshape c}}}
\newcommand{\@skipmath}{}
\long\def\@skipmath#1$#2${%
  \@xskipmath#1\(\)%
  \@ifnotempty{#2}{\toks@\@xp{\the\toks@$#2$}\@skipmath\@empty}}%
\newcommand{\@xskipmath}{}
\long\def\@xskipmath#1\(#2\){%
  \uppercase{\toks@\@xp\@xp\@xp{\@xp\the\@xp\toks@#1}}%
  \@ifnotempty{#2}{\toks@\@xp{\the\toks@\(#2\)}\@xskipmath\@empty}}%
\def\@smfprotect{\let\smfcr\\\def\\{\protect\smfcr}}
\DeclareRobustCommand{\MakeUppercase}[1]{{%
    \@smfprotect\upchars@
    \protected@edef\reserved@a{#1}\uppercasenonmath\reserved@a\reserved@a}}
\protected@edef\MakeUppercase#1{\MakeUppercase{#1}}
\newcommand{\today}{%
  \relax\ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \space\number\day, \number\year}
\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\newcommand{\larger}[1][1]{%
  \count@\@currsizeindex \advance\count@#1\relax
  \ifnum\count@<\z@ \count@\z@
    \else\ifnum\count@>12 \count@12 \fi\fi
  \ifcase\count@
    \Tiny\or\Tiny\or\tiny\or\SMALL\or\Small\or\small
    \or\normalsize
    \or\large\or\Large\or\LARGE\or\huge\or\Huge\else\Huge
  \fi
}
\newcommand{\smaller}[1][1]{\larger[-#1]}
\def\@adjustvertspacing{%
  \bigskipamount.7\baselineskip plus.7\baselineskip
  \medskipamount\bigskipamount \divide\medskipamount\tw@
  \smallskipamount\medskipamount \divide\smallskipamount\tw@
  \abovedisplayskip\medskipamount
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip\abovedisplayskip
  \advance\abovedisplayshortskip-1\abovedisplayskip
  \belowdisplayshortskip\abovedisplayshortskip
  \advance\belowdisplayshortskip 1\smallskipamount
  \jot\baselineskip \divide\jot 4 \relax
}
\renewcommand\normalsize{\@xsetfontsize\normalsize 6%
  \@adjustvertspacing \let\@listi\@listI}
\newcommand\Tiny{\@xsetfontsize\Tiny 1}
\newcommand\tiny{\@xsetfontsize\tiny 2}
\newcommand\SMALL{\@xsetfontsize\SMALL 3}
\newcommand\Small{\@xsetfontsize\Small 4%
  \@adjustvertspacing
  \def\@listi{\topsep\smallskipamount \parsep\z@skip
     \itemsep\z@skip}}
\newcommand\small{\@xsetfontsize\small 5\@adjustvertspacing}
\def\footnotesize{\Small}
\def\scriptsize{\SMALL}
\newcommand\large{\@xsetfontsize\large 7\@adjustvertspacing}
\newcommand\Large{\@xsetfontsize\Large 8\@adjustvertspacing}
\newcommand\LARGE{\@xsetfontsize\LARGE 9}
\newcommand\huge{\@xsetfontsize\huge{10}}
\newcommand\Huge{\@xsetfontsize\Huge{11}}
\def\@xsetfontsize#1#2{%
  \chardef\@currsizeindex#2\relax
  \edef\@tempa{\@nx\@setfontsize\@nx#1%
    \@xp\ifcase\@xp\@currsizeindex\@typesizes
      \else{99}{99}\fi}%
  \@tempa
}
\chardef\@currsizeindex=6
\widowpenalty=10000
\clubpenalty=10000
\brokenpenalty=10000
\newdimen\linespacing
\lineskip=1pt      \normallineskip=1pt
\lineskiplimit=1pt \normallineskiplimit=1pt
\def\baselinestretch{1}  %% 1.1 is better
\textheight 21.5cm
\textwidth 13cm
\headheight=10pt
\headsep 10mm
\footskip 10mm       % was .7
\columnsep=10pt \columnseprule=0pt
\marginparsep=10pt
\marginparpush=5pt
\marginparwidth=90pt
\newskip\normaltopskip
\skip\footins=12pt plus12pt
\skip\@mpfootins=\skip\footins

\fboxsep=3pt \fboxrule=.4pt

\arrayrulewidth=.4pt    \doublerulesep=2pt
\labelsep=5pt           \arraycolsep=\labelsep
\tabcolsep=\labelsep    \tabbingsep=\labelsep

\floatsep=15pt plus 12pt    \dblfloatsep=15pt plus 12pt
\textfloatsep=\floatsep  \dbltextfloatsep=15pt plus 12pt
\intextsep=\floatsep

\@fptop=0pt plus1fil     \@dblfptop=0pt plus1fil
\@fpbot=0pt plus1fil     \@dblfpbot=0pt plus1fil
\@fpsep=10pt plus2fil     \@dblfpsep=10pt plus2fil\relax
\parskip=0pt

\newdimen\normalparindent
\normalparindent=12pt
\parindent=\normalparindent

\parsep 0pt
\partopsep=0pt \relax \parsep=0pt \relax \itemsep=0pt \relax

\@lowpenalty=51         \@medpenalty=151        \@highpenalty=301
\@beginparpenalty=-\@lowpenalty
\@endparpenalty=-\@lowpenalty
\@itempenalty=-\@lowpenalty
\def\calclayout{\normalsize
  \topskip\normaltopskip
  \settoheight{\footnotesep}{\normalfont\footnotesize M$^1$}%
  \@tempdima=\textheight
  \advance\textheight -\headheight
  \advance\textheight -\headsep
  \advance\textheight -\footskip
  \advance\textheight -\topskip
    \divide\textheight\baselineskip\@tempcnta\textheight
  \textheight\@tempcnta\baselineskip
    \advance\textheight \topskip
  \headsep\@tempdima
    \advance\headsep -\textheight   \advance\headsep -\headheight
  \footskip=.5\headsep\advance\footskip .5\baselineskip
  \advance\headsep by -\footskip

  \oddsidemargin\paperwidth
  \advance\oddsidemargin -\textwidth
  \divide\oddsidemargin\tw@
  \ifdim\oddsidemargin<.5truein \oddsidemargin.5truein \fi
  \advance\oddsidemargin -1truein

  \evensidemargin\oddsidemargin

  \topmargin\paperheight \advance\topmargin -\textheight
   \advance\topmargin -\headheight \advance\topmargin -\headsep
   \advance\topmargin -\footskip
   \divide\topmargin\tw@
  \ifdim\topmargin<.5truein \topmargin.5truein \fi
  \advance\topmargin -1truein\relax
}
\def\ps@empty{\let\@mkboth\@gobbletwo
  \let\@oddhead\@empty \let\@evenhead\@empty
  \let\@oddfoot\@empty \let\@evenfoot\@empty
  \global\topskip\normaltopskip}
\def\ps@plain{\ps@empty
  \def\@oddfoot{\normalfont\scriptsize \hfil\thepage\hfil}%
  \let\@evenfoot\@oddfoot}
\def\ps@headings{\ps@empty
  \def\@oddfoot{}%
  \def\@evenfoot{}%
  \def\@evenhead{\normalfont\scriptsize
     \rlap{\bfseries\thepage}\hfil \leftmark{}{}\hfil}%
  \def\@oddhead{\normalfont\scriptsize
     \hfil \rightmark{}{}\hfil \llap{\bfseries\thepage}}%
  \let\@mkboth\@gobbletwo}
\let\ps@copyright\ps@empty
\def\ps@myheadings{\ps@headings \let\@mkboth\@gobbletwo}
\def\leftmark{\expandafter\@firstoftwo\topmark{}{}}
\def\rightmark{\expandafter\@secondoftwo\botmark{}{}}
\long\def\@nilgobble#1\@nil{}
\def\@secmark#1#2#3#4{%
  \begingroup \let\protect\@unexpandable@protect
  \edef\@tempa{\endgroup \toks@{\protect#2{#3}{\@secnumber}}}%
  \@tempa
  \toks@\@xp{\the\toks@{#4}}%
  \afterassignment\@nilgobble\@temptokena\@themark{}\@nil
  \edef\@tempa{\@nx\@mkboth{%
    \ifx\markright#1\the\@temptokena\else\the\toks@\fi}{\the\toks@}}%
  \@tempa}
\let\@secnumber\@empty
\def\markboth#1#2{%
  \begingroup
    \@temptokena{{#1}{#2}}\xdef\@themark{\the\@temptokena}%
    \mark{\the\@temptokena}%
  \endgroup
  \if@nobreak\ifvmode\nobreak\fi\fi}
\let\org@markboth\markboth
\let\partmark\@gobble
\let\tocmark\@gobble
\let\sectionmark\@gobble
\let\subsectionmark\@gobble
\let\subsubsectionmark\@gobble
\let\paragraphmark\@gobble
\def\cleardoublepage{\clearpage\if@twoside \ifodd\c@page\else
    \thispagestyle{empty}\hbox{}\newpage
    \if@twocolumn\hbox{}\newpage\fi\fi\fi}
\DeclareOption{a4paper}{\paperheight 297mm\paperwidth 210mm}
\DeclareOption{letterpaper}{\paperheight 11in\paperwidth 8.5in }
\DeclareOption{oneside}{\@twosidefalse \@mparswitchfalse}
\DeclareOption{twoside}{\@twosidetrue  \@mparswitchtrue}
\newif\if@draft
\DeclareOption{draft}{\@drafttrue\overfullrule5\p@ }
\DeclareOption{final}{\@draftfalse\overfullrule\z@ }
\DeclareOption{onecolumn}{\@twocolumnfalse}
\DeclareOption{twocolumn}{\@twocolumntrue}
\newif\iftagsleft@
\DeclareOption{leqno}{%
  \tagsleft@true \PassOptionsToPackage{leqno}{amsmath}}
\DeclareOption{reqno}{%
  \tagsleft@false \PassOptionsToPackage{reqno}{amsmath}}
\DeclareOption{fleqn}{%
  \def\[{\relax
    \ifmmode\@badmath
    \else
      \begin{trivlist}%
      \@beginparpenalty\predisplaypenalty
      \@endparpenalty\postdisplaypenalty
      \item[]\leavevmode
      \hbox to\linewidth\bgroup$\displaystyle
      \hskip\mathindent\bgroup
    \fi}%
  \def\]{\relax
    \ifmmode
      \egroup \m@th$\hfil \egroup
      \end{trivlist}%
    \else \@badmath
    \fi}%
  \renewenvironment{equation}{%
    \@beginparpenalty\predisplaypenalty
    \@endparpenalty\postdisplaypenalty
    \refstepcounter{equation}%
    \@topsep\abovedisplayskip \trivlist
    \item[]\leavevmode
    \hbox to\linewidth\bgroup\hskip\mathindent$\displaystyle
  }{%
    \m@th$\hfil \displaywidth\linewidth \hbox{\@eqnnum}\egroup
    \endtrivlist
  }%
  \renewenvironment{eqnarray}{%
    \stepcounter{equation}\let\@currentlabel\theequation
    \global\@eqnswtrue \global\@eqcnt\z@ \tabskip\mathindent
    \let\\=\@eqncr \abovedisplayskip\topsep
    \ifvmode \advance\abovedisplayskip\partopsep \fi
    \belowdisplayskip\abovedisplayskip
    \belowdisplayshortskip\abovedisplayskip
    \abovedisplayshortskip\abovedisplayskip
    $$\everycr{}\halign to\linewidth\bgroup
      \hskip\@centering
      $\displaystyle\tabskip\z@skip####\m@th$&%
      \@eqnsel \global\@eqcnt\@ne
      \hfil${}####{}\m@th$\hfil&%
      \global\@eqcnt\tw@
      $\displaystyle ####\m@th$\hfil\tabskip\@centering&%
      \global\@eqcnt\thr@@
      \hbox to \z@\bgroup\hss####\egroup\tabskip\z@skip\cr
    }{%
      \@@eqncr \egroup \global\advance\c@equation\m@ne$$%
      \global\@ignoretrue
    }%
  \newdimen\mathindent \mathindent\leftmargini
}
\let\smf@boldmath\relax
\DeclareOption{boldmath}{%
  \def\smf@boldmath{\mathversion{bold}}}
\DeclareOption{french}{%
  \global\def\smf@language{french}}
\DeclareOption{francais}{%
  \global\def\smf@language{french}}
\DeclareOption{english}{%
  \global\def\smf@language{english}}
\DeclareOption{10pt}{\def\@mainsize{10}\def\@ptsize{0}%
  \normaltopskip=10pt \relax
  \def\@typesizes{%
    \or{5}{6}\or{6}{7}\or{7}{8}\or{8}{10}\or{9}{11}%
    \or{10}{12}% normalsize
    \or{\@xipt}{13}\or{\@xiipt}{14}\or{\@xivpt}{17}%
    \or{\@xviipt}{20}\or{\@xxpt}{24}}%
  \normalsize \linespacing=\baselineskip }

\DeclareOption{11pt}{\def\@mainsize{11}\def\@ptsize{1}%
  \normaltopskip=11pt \relax
  \def\@typesizes{%
    \or{6}{7}\or{7}{8}\or{8}{10}\or{9}{11}\or{10}{12}%
    \or{\@xipt}{13}% normalsize
    \or{\@xiipt}{14}\or{\@xivpt}{17}\or{\@xviipt}{20}%
    \or{\@xxpt}{24}\or{\@xxvpt}{30}}%
  \normalsize \linespacing=\baselineskip }

\DeclareOption{12pt}{\def\@mainsize{12}\def\@ptsize{2}%
  \normaltopskip=12pt \relax
  \def\@typesizes{%
    \or{7}{8}\or{8}{10}\or{9}{11}\or{10}{12}\or{\@xipt}{13}%
    \or{\@xiipt}{14}% normalsize
    \or{\@xivpt}{17}\or{\@xviipt}{20}\or{\@xxpt}{24}%
    \or{\@xxvpt}{30}\or{\@xxvpt}{30}}%
  \normalsize \linespacing=\baselineskip }

\DeclareOption{8pt}{\def\@mainsize{8}\def\@ptsize{8}%
  \normaltopskip=8pt \relax
  \def\@typesizes{%
    \or{5}{6}\or{5}{6}\or{5}{6}\or{6}{7}\or{7}{8}%
    \or{8}{10}% normalsize
    \or{9}{11}\or{10}{12}\or{\@xipt}{13}%
    \or{\@xiipt}{14}\or{\@xivpt}{17}}%
  \normalsize \linespacing=\baselineskip }

\DeclareOption{9pt}{\def\@mainsize{9}\def\@ptsize{9}%
  \normaltopskip=9pt \relax
  \def\@typesizes{%
    \or{5}{6}\or{5}{6}\or{6}{7}\or{7}{8}\or{8}{10}%
    \or{9}{11}% normalsize
    \or{10}{12}\or{\@xipt}{13}\or{\@xiipt}{14}%
    \or{\@xivpt}{17}\or{\@xviipt}{20}}%
  \normalsize \linespacing=\baselineskip }
\ExecuteOptions{leqno,centertags,%
  a4paper,portrait,%
  10pt,twoside,onecolumn,%
  final,french}
\ProcessOptions\relax
\@ifundefined{numberwithin}%
  {\let\@tempa\relax}%
  {\let\@tempa\@gobbletwo}
\@tempa
\ifx\relax\mathfrak \@xp\@gobbletwo
  \else \let\mathfrak\relax \fi
\RequirePackage{amsfonts}\relax
\RequirePackage{amsmath}\relax
\def\tdots@{$\m@th\ldots$}
\renewcommand{\title}[2][]{\gdef\shorttitle{#1}\gdef\@title{#2}}
\edef\title{\@nx\@dblarg
  \@xp\@nx\csname\string\title\endcsname}
\let\@title\@empty \let\shorttitle\@empty
\def\alttitle#1{\gdef\@alttitle{#1}}
\let\@alttitle\@empty
\renewcommand{\author}[2][]{%
  \ifx\@empty\authors
    \gdef\shortauthors{#1}\gdef\authors{#2}%
  \else
    \g@addto@macro\shortauthors{\and#1}%
    \g@addto@macro\authors{\and#2}%
  \fi
  \g@addto@macro\addresses{\author{#1}}%
}
\edef\author{\@nx\@dblarg
  \@xp\@nx\csname\string\author\endcsname}
\let\shortauthors\@empty   \let\authors\@empty
\newcommand{\xandlist}[4]{\@andlista{{#1}{#2}{#3}}#4\and\and}
\def\@andlista#1#2\and#3\and{\@andlistc{#2}\@ifnotempty{#3}{%
  \@andlistb#1{#3}}}
\def\@andlistb#1#2#3#4#5\and{%
  \@ifempty{#5}{%
    \@andlistc{#2#4}%
  }{%
    \@andlistc{#1#4}\@andlistb{#1}{#3}{#3}{#5}%
  }}
\let\@andlistc\@iden
\newcommand{\nxandlist}[4]{%
  \def\@andlistc##1{\toks@\@xp{\the\toks@##1}}%
  \toks@{\toks@\@emptytoks \@andlista{{#1}{#2}{#3}}}%
  \the\@xp\toks@#4\and\and
  \edef#4{\the\toks@}%
  \let\@andlistc\@iden}
\newcommand{\andify}{%
  \nxandlist{\unskip, }{\unskip{} \smfandname~}{\unskip{} \smfandname~}}
\def\and{\unskip{} \smfandname\ \ignorespaces}
\let\addresses\@empty      \let\thankses\@empty
\newcommand{\address}[2][]{\g@addto@macro\addresses{\address{#1}{#2}}}
\newcommand{\curraddr}[2][]{\g@addto@macro\addresses{\curraddr{#1}{#2}}}
\newcommand{\email}[2][]{\g@addto@macro\addresses{\email{#1}{#2}}}
\newcommand{\urladdr}{\bgroup\catcode`\:=12\catcode`\~=12\@urladdr}
\newcommand{\@urladdr}[2][]{\g@addto@macro\addresses{\urladdr{#1}{#2}}\egroup}
\def\@setaddresses{\par\nobreak
  \begingroup
  \parindent-2em\leftskip2em
  \rightskip=0pt plus 20pt
  \emergencystretch .5\textwidth
  \exhyphenpenalty=-100
  \interlinepenalty\@M
  \def\baselinestretch{1}\normalfont\footnotesize
  \def\\{\unskip, \penalty-10\ignorespaces}%
  \def\cond@bullet {{\setbox0\hbox{\quad$\bullet$\quad}%
         \hskip 0pt plus 3cm\penalty -30\hskip 0pt plus -3cm
         \cleaders \copy0 \hskip\wd0 }}%
  \def\author##1{\ifhmode\par\nobreak \vskip\smallskipamount\fi
      {\scshape ##1}\let\address\firstaddress}%
  \def\firstaddress##1##2{\unskip, \let\address\otheraddress
         \penalty-20\ignorespaces##2}%
  \def\otheraddress##1##2{\cond@bullet \ignorespaces##2}%
  \def\curraddr{\address}%
  \let\address\firstaddress
  \def\email##1##2{\@ifnotempty{##2}%
        {\cond@bullet
         \hbox{\itshape E-mail~:}~{\ttfamily\ignorespaces ##2}}}%
  \def\urladdr##1##2{\@ifnotempty{##2}%
        {\cond@bullet
         {\itshape Url~:}~{\ttfamily\ignorespaces ##2}\par}}%
  \addresses
  \par\endgroup
}
\renewcommand{\thanks}[1]{\g@addto@macro\thankses{\thanks{#1}}}
\def\@setthanks{\def\thanks##1{\par##1\@addpunct{{\upshape.}}}\thankses}
\let\@date\@empty
\def\@setdate{{\itshape\@date\@@par}} %% enleve le \@addpunct. avant \@@par
\def\dedicatory#1{\def\@dedicatory{#1}}
\let\@dedicatory\@empty
\def\dedicatoryfont{\normalfont\footnotesize\itshape}
\def\@setdedicatory{%
    \begingroup
      \def\signature##1{\nobreak\hskip 2em plus 1fil
        \penalty-5\hbox{}\nobreak\hfil\parfillskip=0pt
        \mbox{\upshape ##1}\par}
      \raggedleft
      \dedicatoryfont
      \@dedicatory\par
    \endgroup}
\def\keywords#1{\def\@keywords{#1}}
\let\@keywords=\@empty
\def\@setkeywords{%
  \abstractfont
  {\abstractheadfont\keywordsname\MakePointrait}\enspace\ignorespaces
  \@keywords\@addpunct{{\upshape.}}}
\def\altkeywords#1{\def\@altkeywords{#1}}
\let\@altkeywords=\@empty
\def\@setaltkeywords{%
  \abstractfont
  {\abstractheadfont\altkeywordsname\MakePointrait}\enspace\ignorespaces
  \@altkeywords\@addpunct{{\upshape.}}}
\def\subjclass#1{\def\@subjclass{#1}}
\let\@subjclass=\@empty
\def\@setsubjclass{%
  \abstractfont
  {\abstractheadfont\subjclassname\MakePointrait}\enspace\ignorespaces
  \@subjclass\@addpunct{{\upshape.}}}
\def\translator#1{%
  \ifx\@empty\@translators
     \gdef\@translators{#1}\else
     \g@addto@macro\@translators{\and#1}\fi}
\let\@translators\@empty
\def\@settranslators{\par
  \begingroup
  \translatedby\ \andify\@translators
  {\itshape \ignorespaces\@translators} \@@par
  \endgroup}
\def\ISBN#1{\def\@isbn{#1}}
\def\ISSN#1{\def\@issn{#1}}
\let\@isbn\@empty
\let\@issn\@empty
\def\abstractheadfont{\bfseries\smf@boldmath\itshape}
\def\abstractfont{\def\baselinestretch{1}\footnotesize}
\newdimen\abstractmargin
\abstractmargin1cm
\newtoks\@genabs\newtoks\@genabstokb
\newenvironment{@genabstract}[1]{%
   \gdef\@genabstext{}\def\smf@tempb{#1}\@getgenabstext
}{%
  \@xp\@xp\global\@xp\let\csname @\smf@tempb\endcsname \@genabstext}

\long\def\@getgenabstext#1\end #2{%
  \@genabs=\expandafter{\@genabstext}
  \def\@tempa{#2}\ifx\@tempa\smf@tempb
     \@genabstokb={#1}%
     \edef\@next{\noexpand\end{@genabstract}\noexpand\end{\smf@tempb}}%
  \else
     \@genabstokb={#1\end{#2}}%
     \let\@next\@getgenabstext
  \fi
  \global\edef\@genabstext {\the\@genabs \the\@genabstokb}%
  \@next}

\def\@setgenabstract#1{%
\@xp\ifx\csname @#1\endcsname\@empty\else
  \vbox\bgroup
  \abstractfont
  \list{}{\labelwidth\z@
    \leftmargin\abstractmargin \rightmargin\leftmargin
    \listparindent\normalparindent
    \itemindent\z@
  %    \itemindent\normalparindent %  \advance\itemindent\labelsep
    \parsep\z@ \@plus\p@
    \let\fullwidthdisplay\relax}%
  \sbox\@tempboxa{\csname @set#1head\endcsname}%
  \ifdim\wd\@tempboxa>.7\textwidth \smf@skippttrue\fi
  \item\relax
  {\csname @set#1head\endcsname
  \ifsmf@skippt
      \global\smf@skipptfalse
      \@@par\nobreak
  \else
      \pointrait\nobreak
  \fi}
  \ignorespaces
  \csname @#1language\endcsname\csname @#1\endcsname
  \endlist
  \egroup
\fi}
\def\@abstract{}
\def\@abstractlanguage{\@smflanguage}
\newenvironment{abstract}{%
  \ifx\maketitle\relax
    \ClassWarning{\@classname}{Abstracts should precede
      \protect\maketitle\space in SMF documentclasses; reported}%
  \fi
  \begin{@genabstract}{abstract}%
}{%
  \ifx\@setabstract\relax \@setabstracta\par\bigskip \fi
}
\def\@setabstracthead{\abstractheadfont\abstractname}
\newif\ifsmfabstracta\smfabstractatrue
\def\@setabstract{\ifsmfabstracta
    \@setabstracta
    \global\let\@setabstract\relax
    \fi}
\def\@setabstracta{\@setgenabstract{abstract}}
\def\@altabstract{}
\def\@altabstractlanguage{\@smfaltlanguage}
\newenvironment{altabstract}{%
  \ifx\maketitle\relax
    \ClassWarning{\@classname}{Abstracts should precede
      \protect\maketitle\space in SMF documentclasses; reported}%
  \fi
  \begin{@genabstract}{altabstract}%
}{%
  \ifx\@setaltabstract\relax \@setaltabstracta\par\bigskip \fi
}
\def\@setaltabstracthead{\abstractheadfont \altabstractname
  \ifx\@alttitle\@empty\else\ \textup(\emph{\@alttitle}\textup)\fi}
\newif\ifsmfaltabstracta\smfaltabstractatrue
\def\@setaltabstract{\ifsmfaltabstracta
   \@setaltabstracta
   \global\let\@setaltabstract\relax
   \fi}
\def\@setaltabstracta{\@setgenabstract{altabstract}}
\def\titlepage{%
  \cleardoublepage
  \thispagestyle{empty}\setcounter{page}{0}}
\def\endtitlepage{\newpage}
\def\maketitle{\par \@topnum\z@
    % this prevents figures from falling at the top of page 1
  \begingroup
  \let\@makefnmark\relax  \let\@thefnmark\relax
  \@maketitle
  \@endmaketitlehook
  \endgroup
  \c@footnote\z@
  \let\maketitle\relax \let\@maketitle\relax }
\def\@endmaketitlehook{}
\def\smf@journalhead{}
\def\smf@authorfont{}
\def\@maketitle{\cleardoublepage\thispagestyle{copyright}
 \begingroup
 \uppercasenonmath\shorttitle
 \ifx\@empty\shortauthors \let\shortauthors\shorttitle
  \else \uppercasenonmath\shortauthors \andify\shortauthors \fi
  \toks@\@xp{\shortauthors}\@temptokena\@xp{\shorttitle}%
  \edef\@tempa{\@nx\markboth{\the\toks@}{\the\@temptokena}}\@tempa
 \topskip\z@skip
 \vtop to 55 mm{%
 \parindent=0pt
 \hrule
 \medskip
 {\abstractfont\smf@journalhead\par}\vfil
 \begin{center}
 \def\baselinestretch{1.2}\large\vfil
   {\bfseries\smf@boldmath\MakeUppercase\@title\par}
 \vfil
   \ifx\@empty\smfbyname\else
     {\smf@byfont\smfbyname\ifsmf@byauthor\par\vfil\else\ \fi}%
   \fi
   {\smf@authorfont
    \edef\smfandname{{\noexpand\normalfont \smfandname}}
    \andify\authors\authors\par}
 \vfil \vrule height .4pt width .3\textwidth \vfil
 \end{center}}
 \@maketitlehook
 \par\bigskip
 \ifx\@empty\@dedicatory\else\@setdedicatory\medskip\fi
 \@setabstract\par\smallskip\@setaltabstract\par
 \bigskip\bigskip
 \endgroup}
\newif\ifsmf@byauthor\smf@byauthortrue
\def\smf@byfont{\normalfont\itshape}
\def\@maketitlehook{%
 \ifx\@empty\@subjclass\else\@footnotetext{\@setsubjclass}\fi
 \ifx\@empty\@keywords\else\@footnotetext{\@setkeywords}\fi
 \ifx\@empty\thankses\else\def\par{\let\par\@par}\@footnotetext{\@setthanks}\fi
}
\def\smf@enddoc{%
  \par\vskip 2\bigskipamount
  \bgroup
  \def\baselinestretch{1}\normalfont\footnotesize
  \raggedright
  \hrule width .2\textwidth\par\bigskip
  \ifx\@empty\@date       \else \@setdate\medskip        \fi
  \ifx\@empty\@translators\else \@settranslators\medskip \fi
  \ifx\@empty\addresses   \else \@setaddresses             \fi
  \par\egroup}
\AtEndDocument{\smf@enddoc}
\def\trivlist{\parsep\parskip\@nmbrlistfalse
  \@trivlist \labelwidth\z@ \leftmargin\z@
  \itemindent\z@
  \let\@itemlabel\@empty
  \def\makelabel##1{\upshape##1}}
\newskip\listisep \listisep\smallskipamount
\def\@listi{\leftmargin\leftmargini \parsep\z@skip
  \topsep\listisep \itemsep\z@skip
  \listparindent\normalparindent}
\def\@listii{\leftmargin\leftmarginii
  \labelwidth\leftmarginii \advance\labelwidth-\labelsep
  \topsep\z@skip \parsep\z@skip \partopsep\z@skip \itemsep\z@skip}
\def\@listiii{\leftmargin\leftmarginiii
  \labelwidth\leftmarginiii \advance\labelwidth-\labelsep}
\def\@listiv{\leftmargin\leftmarginiv
  \labelwidth\leftmarginiv \advance\labelwidth-\labelsep}
\def\@listv{\leftmargin\leftmarginv
  \labelwidth\leftmarginv \advance\labelwidth-\labelsep}
\def\@listvi{\leftmargin\leftmarginvi
  \labelwidth\leftmarginvi \advance\labelwidth-\labelsep}
\let\@listI\@listi
\def\enumerate{\ifnum \@enumdepth >3 \@toodeep\else
      \advance\@enumdepth \@ne
      \edef\@enumctr{enum\romannumeral\the\@enumdepth}\list
      {\csname label\@enumctr\endcsname}{\usecounter
        {\@enumctr}\def\makelabel##1{\hss\llap{\upshape##1}}}\fi}
\def\labelenumi{\theenumi.}
\def\theenumi{\@arabic\c@enumi}
\def\labelenumii{(\theenumii)}
\def\theenumii{\@alph\c@enumii}
\def\p@enumii{\theenumi}
\def\labelenumiii{(\theenumiii)}
\def\theenumiii{\@roman\c@enumiii}
\def\p@enumiii{\theenumi(\theenumii)}
\def\labelenumiv{(\theenumiv)}
\def\theenumiv{\@Alph\c@enumiv}
\def\p@enumiv{\p@enumiii\theenumiii}
\def\itemize{%
  \ifnum\@itemdepth>3 \@toodeep
  \else \advance\@itemdepth\@ne
    \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
    \list{\csname\@itemitem\endcsname}%
      {\def\makelabel##1{\hss\llap{\upshape##1}}}%
  \fi}
\def\labelitemi{\bfseries --}% \upshape already done by \itemize
\def\labelitemii{$\m@th\bullet$}
\def\labelitemiii{$\m@th\ast$}
\def\labelitemiv{$\m@th\cdot$}
\def\verse{\let\\\@centercr
  \list{}{\itemsep\z@ \itemindent -1.5em\listparindent\itemindent
  \rightmargin\leftmargin \advance\leftmargin 1.5em}\item[]}
\let\endverse=\endlist
\def\quotation{\list{}{%
    \leftmargin3pc \listparindent\normalparindent
    \itemindent\z@
    \rightmargin\leftmargin \parsep\z@ \@plus\p@}%
  \item[]}
\let\endquotation=\endlist
\def\quote{\list{}{\rightmargin\leftmargin}\item[]}
\let\endquote=\endlist
\newcommand{\descriptionlabel}[1]{\hspace\labelsep
    \upshape\bfseries\smf@boldmath #1\unskip\ :}
\newcommand{\description}{\list{}{%
  \advance\leftmargini6\p@ \itemindent-12\p@
  \labelwidth\z@ \let\makelabel\descriptionlabel}}
\let\enddescription=\endlist
\AtBeginDocument{%
  \labelsep=5pt
  \settowidth\leftmargini{\labelenumi\hskip\labelsep}%
  \advance\leftmargini by \normalparindent
  \settowidth\leftmarginii{\labelenumii\hskip\labelsep}%
  \advance\leftmarginii by 15pt
  \settowidth\leftmarginiii{\labelenumiii\hskip\labelsep}%
  \advance\leftmarginiii by 12pt
  \settowidth\leftmarginiv{\labelenumiv\hskip\labelsep}%
  \advance\leftmarginiv by 10pt
  \leftmarginv=10pt
  \leftmarginvi=10pt
  \leftmargin=\leftmargini
  \labelwidth=\leftmargini \advance\labelwidth-\labelsep
  \@listi}
\def\@startsection#1#2#3#4#5#6{%
 \if@noskipsec \leavevmode \fi
 \par \@tempskipa #4\relax
 \@afterindenttrue
 \ifdim \@tempskipa <\z@
    \@tempskipa -\@tempskipa \@afterindentfalse\fi
 \if@nobreak \everypar{}\else
     \addpenalty\@secpenalty\addvspace\@tempskipa\fi
 \@ifstar{\@dblarg{\@sect{#1}{\@m}{#3}{#4}{#5}{#6}}}%
         {\@dblarg{\@sect{#1}{#2}{#3}{#4}{#5}{#6}}}%
}
\def\@sect#1#2#3#4#5#6[#7]#8{%
 \edef\@toclevel{\ifnum#2=\@m 0\else\number#2\fi}%
 \ifnum #2>\c@secnumdepth
    \let\@secnumber\@empty
    \let\@svsec\@empty
    \let\@svnl\@empty
    \let\@svspace\@empty
 \else
   \@xp\let\@xp\@secnumber\csname the#1\endcsname
    \refstepcounter{#1}%
    \@xp\ifx\csname #1name\endcsname\@empty
        \let\@svnl\@empty
        \def\@svspace{.\enspace}\def\@svsec{\csname the#1\endcsname}%
    \else
         \def\@svsec{\ignorespaces\csname #1name\endcsname\space
                  \protect\textup{\csname the#1\endcsname}}%
         \let\@svspace\@empty
         \def\@svnl{\@@par\nobreak\smallskip\nobreak}%
    \fi
  \fi
  \@tempskipa #5\relax
  \ifsmf@skippt\@tempskipa 1sp\smf@skipptfalse\fi
  \ifdim \@tempskipa>\z@
    \begingroup
       #6{\@hangfrom{\hskip #3\relax\@svsec\@svspace}%
          \@svnl
          \interlinepenalty\@M #8\@@par}%
    \endgroup
    \csname #1mark\endcsname{#7}%
    \ifnum#2>\@m \else \@tocwrite{#1}{#8}\fi
    \par \nobreak
    \vskip \@tempskipa
    \global\@nobreaktrue
    \@afterheading
  \else
    \@ifempty{#8}%
      {\def\@svsechd{#6{\hskip #3\relax\@svsec\@svspace}%
                     \ifnum#2>\@m \else \@tocwrite{#1}{#8}\fi }}%
      {\def\@svsechd{#6{\hskip #3\relax\@svsec\@svspace
             {\ignorespaces #8\pointrait\nobreak\ignorespaces}
              \ifnum#2>\@m \else \@tocwrite{#1}{#8}\fi }}}%
    \global\@nobreakfalse \global\@noskipsectrue
    \everypar{%
      \if@noskipsec
        \global\@noskipsecfalse
        \clubpenalty\@M \hskip -\parindent
        \begingroup \@svsechd \endgroup
        \unskip
        \@tempskipa#5\relax\hskip -\@tempskipa
      \else
        \clubpenalty \@clubpenalty
        \everypar{}%
      \fi}%
  \fi
}
\let\@xsect\relax
\let\@ssect\relax
\setcounter{secnumdepth}{5}
\newcounter{part}
\newcounter{section}
\newcounter{subsection}[section]
\newcounter{subsubsection}[subsection]
\newcounter{paragraph}[subsubsection]
\renewcommand\thepart      {\Roman{part}}
\renewcommand\thesection {\arabic{section}}
\renewcommand\thesubsection{\thesection.\arabic{subsection}}
\renewcommand\thesubsubsection
                {\thesubsection.\arabic{subsubsection}}
\renewcommand\theparagraph {\thesubsubsection.\arabic{paragraph}}
\def\part{\@startsection{part}{1}%
  \z@{3\linespacing\@plus\linespacing}{2\linespacing}%
  {\centering\normalfont\bfseries\smf@boldmath\MakeUppercase}}
\def\appendix{\par
  \begingroup
    \def\@elt##1{\global\csname c@##1\endcsname\z@\relax
      \csname cl@##1\endcsname}
    \global\c@section\z@
    \cl@section
  \endgroup
 \let\sectionname\appendixname
 \def\thesection{\@Alph\c@section}}
\def\specialsection{\@startsection{section}{1}%
  \z@{2\linespacing\@plus\linespacing}{.5\linespacing}%
  {\centering\normalfont\bfseries\smf@boldmath\MakeUppercase}}
\def\section{\@startsection{section}{1}%
  \z@{1.5\linespacing\@plus\linespacing}{.5\linespacing}%
  {\normalfont\bfseries\smf@boldmath\centering}}
\let\sectionname\@empty
\def\subsection{\@startsection{subsection}{2}%
  \z@{.7\linespacing\@plus.7\linespacing}{-.5ex}%
  {\normalfont\bfseries\smf@boldmath}}
\def\Subsection{\@startsection{subsection}{2}%
  \z@{.7\linespacing\@plus.7\linespacing}{.3\linespacing}
  {\normalfont\bfseries\smf@boldmath}}
\let\subsectionname\@empty
\def\subsubsection{\@startsection{subsubsection}{3}%
  \z@{.4\linespacing}{-.5ex}%
  {\normalfont\itshape}}
\def\Subsubsection{\@startsection{subsubsection}{3}%
  \z@{.4\linespacing}{.2\linespacing}%
  {\normalfont\itshape}}
\let\subsubsectionname\@empty
\def\paragraph{\@startsection{paragraph}{4}%
  \z@{.4\linespacing}{-\fontdimen2\font}%
  {\normalfont\itshape}}
\let\paragraphname\@empty % ACL
\def\subparagraph{\@startsection{subparagraph}{5}%
  \z@{.3\linespacing}{-\fontdimen2\font}%
  \normalfont}
 \def\partrunhead#1#2#3{%
   \@ifnotempty{#2}
      {\MakeUppercase{#1 #2}\@ifnotempty{#3}{.\ }}%
   \@ifnotempty{#3}{\MakeUppercase{#3}}}
\let\sectionrunhead\partrunhead
\def\@Roman#1{\@xp\@slowromancap \romannumeral#1@}
\def\@slowromancap#1{\ifx @#1% then terminate
  \else
    \if i#1I\else\if v#1V\else\if x#1X\else\if l#1L\else\if
    c#1C\else\if m#1M\else#1\fi\fi\fi\fi\fi\fi
    \@xp\@slowromancap
  \fi }
\def\frontmatter{}
\def\mainmatter{\def\baselinestretch{1.1}\normalfont}
\def\backmatter{\def\baselinestretch{1}\normalfont}
\newcommand{\@pnumwidth}{1.6em}
\newcommand{\@tocrmarg}{2.6em}
\setcounter{tocdepth}{1}
\def\@starttoc#1#2{\begingroup
  \par\removelastskip\vskip\z@skip
  \@startsection{toc}\@M\z@{\linespacing\@plus\linespacing}%
    {.5\linespacing}{\centering\normalfont\bfseries}{#2}%
  \ifx\contentsname#2%
  \else \addcontentsline{toc}{section}{#2}\fi
  \list{}{\labelwidth\z@
    \leftmargin\abstractmargin \rightmargin\leftmargin
    \listparindent\z@
    \itemindent\z@
    \parsep\z@ \@plus\p@
    \def\baselinestretch{1}\normalfont
    \let\fullwidthdisplay\relax}%
  \item\relax
  \makeatletter
  \@input{\jobname.#1}%
  \def\@tempa{toc}\def\@tempb{#1}\ifx\@tempa\@tempb\else
  \if@filesw
    \@xp\newwrite\csname tf@#1\endcsname
    \immediate\@xp\openout\csname tf@#1\endcsname \jobname.#1\relax
  \fi\fi\par
  \endlist
  \global\@nobreakfalse \endgroup
  \addvspace{32\p@\@plus14\p@}%
}
\def\tableofcontents{\@starttoc{toc}\contentsname
  \let\tableofcontents\relax}
\def\listoffigures{\@starttoc{lof}\listfigurename}
\def\listoftables{\@starttoc{lot}\listtablename}
\AtBeginDocument{%
  \@for\@tempa:=-1,0,1,2,3\do{%
    \@ifundefined{r@tocindent\@tempa}{%
      \@xp\gdef\csname r@tocindent\@tempa\endcsname{0pt}}{}%
  }%
}
\def\@writetocindents{%
  \begingroup
  \@for\@tempa:=-1,0,1,2,3\do{%
    \immediate\write\@auxout{%
      \string\newlabel{tocindent\@tempa}{%
        \csname r@tocindent\@tempa\endcsname}}%
  }%
  \endgroup}
\AtEndDocument{\@writetocindents}
\AtEndDocument{%
  \if@filesw
    \@xp\newwrite\csname tf@toc\endcsname
    \immediate\@xp\openout\csname tf@toc\endcsname \jobname.toc\relax
  \fi
}
\let\indentlabel\@empty
\def\@tochangmeasure#1{\sbox\z@{#1}%
  \ifdim\wd\z@>\csname r@tocindent\@toclevel\endcsname\relax
    \@xp\xdef\csname r@tocindent\@toclevel\endcsname{\the\wd\z@}%
  \fi
}
\newcount\tochyphenpenalty
\tochyphenpenalty\@M
\def\@tocline#1#2#3#4#5#6#7{\relax
  \ifnum #1>\c@tocdepth % then omit
  \else
    \par \addpenalty\@secpenalty\addvspace{#2}%
    \begingroup \hyphenpenalty\tochyphenpenalty
    \@ifempty{#4}{%
      \@tempdima\csname r@tocindent\number#1\endcsname\relax
    }{%
      \@tempdima#4\relax
    }%
    \parindent\z@ \leftskip#3\relax
      \advance\leftskip\@tempdima\relax
    \advance\rightskip\@pnumwidth % plus1em
    \parfillskip-\@pnumwidth
    {#5{\leavevmode\hskip-\@tempdima #6}}%
    \nobreak
    \xleaders\hbox to1ex{\normalfont\hss.\hss}\hfil\nobreak
    \hbox to\@pnumwidth{\@tocpagenum{#7}}\par
    \nobreak
    \endgroup
  \fi}
\def\@tocpagenum#1{\hss{\mdseries #1}}
\def\@tocwrite#1{\@xp\@tocwriteb\csname toc#1\endcsname{#1}}
\def\@tocwriteb#1#2#3{\begingroup
  \def\@tocline##1##2##3##4##5##6{\ifnum##1>\c@tocdepth
    \else \sbox\z@{##5\let\indentlabel\@tochangmeasure##6}\fi}%
   \csname l@#2\endcsname
     {#1{\csname#2name\endcsname}{\@secnumber}{}}%
 \endgroup
 \addcontentsline{toc}{#2}%
   {\protect#1{\csname#2name\endcsname}{\@secnumber}{#3}}}
\newcommand{\tocpart}[3]{%
  \indentlabel{\@ifnotempty{#2}{\ignorespaces#1 #2.\kern1ex}}#3}
\let\tocsection\tocpart
\let\tocsubsection\tocsection
\let\tocsubsubsection\tocsection
\let\tocparagraph\tocsection

\def\l@part{\@tocline{-1}{12pt plus2pt}{0pt}{}{\bfseries\smf@boldmath}}
\def\l@section{\@tocline{1}{0pt}{0pc}{}{}}
\def\l@subsection{\@tocline{2}{0pt}{1pc}{}{}}
\def\l@subsubsection{\@tocline{3}{0pt}{2pc}{}{}}
\def\l@paragraph{\@tocline{5}{0pt}{3pc}{}{}}
\def\l@figure{\@tocline{0}{3pt plus2pt}{0pt}{}{}}
\let\l@table\l@figure
\newcount\smf@nthebib
\newdimen\smf@tempwidtha
\newdimen\smf@tempwidthb
\let\bibliosection\section
\def\bibliofont{\def\baselinestretch{1}\small}
\newenvironment{thebibliography}[1]{%
  \global\advance\smf@nthebib1
  \bibliosection*{\refname}%
  \normalfont\labelsep .5em\relax
  \renewcommand\theenumiv{\arabic{enumiv}}\let\p@enumiv\@empty
  \list{\@biblabel{\theenumiv}}{%
    \global\smf@tempwidtha 0pt
    \expandafter\ifx
        \csname r@maxlabelwd\the\smf@nthebib\endcsname
        \relax
        \settowidth\labelwidth{\@biblabel{#1}}%
    \else
         \expandafter\expandafter\expandafter\labelwidth
         \csname r@maxlabelwd\the\smf@nthebib\endcsname
    \fi
    \leftmargin\labelwidth \advance\leftmargin\labelsep
    \usecounter{enumiv}%
    \itemindent 0pt
   \itemsep 0.1\baselineskip plus0.1\baselineskip
       minus0.1\baselineskip
    }
    \bibliofont
    \sloppy \clubpenalty\@M \widowpenalty\clubpenalty
    \sfcode`\.=\@m
}{%
  \def\@noitemerr{%
     \@latex@warning{Empty `thebibliography' environment}}% ' (hack)
  \endlist
  \immediate\write\@auxout
     {\string\newlabel{maxlabelwd\the\smf@nthebib}{\the\smf@tempwidtha}}
}
\def\bysame{\leavevmode\hbox to3em{\hrulefill}\thinspace}
\def\newblock{}
\def\@biblabel#1{\@ifnotempty{#1}{[#1]}}
\def\@cite#1#2{{%
 \m@th\upshape\mdseries[{\bfseries #1}{\if@tempswa, #2\fi}]}}
\@ifundefined{cite }{%
  \expandafter\let\csname cite \endcsname\cite
  \edef\cite{\@nx\protect\@xp\@nx\csname cite \endcsname}%
}{}
\def\bibitem{\@ifnextchar[\@lbibitem\@bibitem}
\def\@lbibitem[#1]#2{\item[\@biblabel{#1}\hfill]%
       \settowidth\smf@tempwidthb{\@biblabel{#1}}%
       \ifdim\smf@tempwidthb>\smf@tempwidtha
          \global\smf@tempwidtha=\smf@tempwidthb
       \fi
       \if@filesw
      {\let\protect\noexpand
       \immediate
       \write\@auxout{\string\bibcite{#2}{#1}}}\fi\ignorespaces}
\def\@bibitem#1{\item\if@filesw \immediate\write\@auxout
       {\string\bibcite{#1}{\the\value{\@listctr}}}\fi
        \settowidth\smf@tempwidthb{\@biblabel{\theenumiv}}%
        \ifdim\smf@tempwidthb>\smf@tempwidtha
           \global\smf@tempwidtha=\smf@tempwidthb
        \fi\ignorespaces}
\newif\ifhave@multicol
\IfFileExists{multicol.sty}%
  {\ClassInfo{\@classname}{Loading multicol.sty}%
   \RequirePackage{multicol}\have@multicoltrue}%
  {\ClassInfo{\@classname}%
    {multicol.sty is unavailable, using LaTeX's twocolumn}}
\newcommand\printindex{\@input{\jobname.ind}}%
\newif\if@restonecol
\def\theindex{\@restonecoltrue\if@twocolumn\@restonecolfalse\fi
  \columnseprule0pt \columnsep 35\p@
  \ifhave@multicol
    \begin{multicols}{2}[\section*{\indexname}]%
  \else
    \twocolumn[\section*{\indexname}]%
  \fi
  \let\item\@idxitem
  \parindent\z@  \parskip\z@\@plus.3\p@\relax
  \footnotesize}
\def\@idxitem{\par\hangindent 2em}
\def\subitem{\par\hangindent 2em\hspace*{1em}}
\def\subsubitem{\par\hangindent 3em\hspace*{2em}}
\def\endtheindex{\ifhave@multicol
    \end{multicols}%
  \else
    \if@restonecol\onecolumn\fi
  \fi}
\def\indexspace{\par}
\def\footnoterule{\kern-.4\p@
        \hrule\@width 5pc\kern10\p@\kern-\footnotesep}
\def\@makefnmark{\hbox{$\m@th^{(\@thefnmark)}$}}
\def\@makefntext{\parindent0pt\sloppy\indent\@makefnmark}
\hfuzz=1pt \vfuzz=\hfuzz
\def\sloppy{\tolerance9999 \emergencystretch 3em\relax}
\setcounter{topnumber}{4}
\setcounter{bottomnumber}{4}
\setcounter{totalnumber}{4}
\setcounter{dbltopnumber}{4}
\renewcommand{\topfraction}{.97}
\renewcommand{\bottomfraction}{.97}
\renewcommand{\textfraction}{.03}
\renewcommand{\floatpagefraction}{.9}
\renewcommand{\dbltopfraction}{.97}
\renewcommand{\dblfloatpagefraction}{.9}
\setlength{\floatsep}{12pt plus 6pt minus 4pt}
\setlength{\textfloatsep}{15pt plus 8pt minus 5pt}
\setlength{\intextsep}{12pt plus 6pt minus 4pt}
\setlength{\dblfloatsep}{12pt plus 6pt minus 4pt}
\setlength{\dbltextfloatsep}{15pt plus 8pt minus 5pt}
\setlength{\@fptop}{0pt}% removed ``plus 1fil''
\setlength{\@fpsep}{8pt}% removed ``plus 2fil''
\setlength{\@fpbot}{0pt plus 1fil}
\setlength{\@dblfptop}{0pt}% removed ``plus 1fil''
\setlength{\@dblfpsep}{8pt}% removed ``plus 2fil''
\setlength{\@dblfpbot}{0pt plus 1fil}
\newcommand{\fps@figure}{tbp}
\newcommand{\fps@table}{tbp}
\newcounter{figure}
\newcounter{table}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename\ \thefigure}
\newenvironment{figure}{\@float{figure}}{\end@float}
\newenvironment{figure*}{\@dblfloat{figure}}{\end@dblfloat}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{\tablename\ \thetable}
\newenvironment{table}{\@float{table}}{\end@float}
\newenvironment{table*}{\@dblfloat{table}}{\end@dblfloat}
\newskip\abovecaptionskip \abovecaptionskip=12pt \relax
\newskip\belowcaptionskip \belowcaptionskip=12pt \relax
\newdimen\captionindent \captionindent=3pc
%% \def\captionheadfont@{\scshape}
%% \def\captionfont@{\normalfont}
\def\@captionheadfont{\normalfont\scshape\small}
\def\@captionfont{\normalfont\small}
\long\def\smf@makecaption#1#2{%
  \ifdim\captionindent>.1\hsize \captionindent.1\hsize \fi
  \setbox\@tempboxa\vbox{\color@setgroup
    \advance\hsize-2\captionindent\noindent
    \@captionfont\@captionheadfont#1\@xp\@ifnotempty\@xp
        {\@cdr#2\@nil}{\@addpunct{.}\@captionfont\rmfamily\upshape\enspace#2}%
    \unskip\kern-2\captionindent\par
    \global\setbox\@ne\lastbox\color@endgroup}%
  \ifhbox\@ne % the normal case
    \setbox\@ne\hbox{\unhbox\@ne\unskip\unskip\unpenalty\unkern}%
  \fi
  \ifdim\wd\@tempboxa=\z@ % this means caption will fit on one line
    \setbox\@ne\hbox to\columnwidth{\hss\kern-2\captionindent\box\@ne\hss}%
    \@tempdima\wd\@ne\advance\@tempdima-\captionindent
    \wd\@ne\@tempdima
  \else % tempboxa contained more than one line
    \setbox\@ne\vbox{\rightskip=0pt plus\captionindent\relax
        \unvbox\@tempboxa\parskip\z@skip
        \noindent\unhbox\@ne\advance\hsize-2\captionindent\par}%
  \fi
  \ifnum\@tempcnta<64 % if the float IS a figure...
    \addvspace\abovecaptionskip
    \noindent\kern\captionindent\box\@ne
  \else % if the float IS NOT a figure...
    \noindent\kern\captionindent\box\@ne
    \nobreak
    \vskip\belowcaptionskip
  \fi
\relax
}
\let\@makecaption\smf@makecaption
\def\@upn{}
\RequirePackage{amsthm}
\@ifundefined{@restorelabelsep}{\let\@restorelabelsep\relax}{}
\@ifundefined{thm@headfont}{%
  \let\thm@indent\theoremindent
  \let\thm@headfont\theoremheadfont
  \let\thm@notefont\theoremnotefont
  \let\thm@preskip\theorempreskipamount
  \let\thm@postskip\theorempostskipamount
  \let\thm@headpunct\theoremheadpunct}{}
\def\@swapped#1#2{#2\@ifnotempty{#1}{\@addpunct{{\upshape.}}\quad#1\unskip}}
\def\swappedhead#1#2#3{%
  \thmnumber{#2.}%
  \thmname{\@ifnotempty{#2}{~}#1}%
  \thmnote{ {\the\thm@notefont(#3)}}}
\def\@thmheadnl{%
  \@noskipsectrue
  \everypar{\global\@minipagefalse \global\@newlistfalse
  \global\@inlabelfalse \global\@nobreakfalse
  {\setbox\z@\lastbox}\box\@labels
  {\parskip0pt\par}\global\@nobreaktrue
   \everypar{}\indent}}%
\def\@begintheorem#1#2[#3]{%
  \def\@theoremhead{\normalfont\the\thm@headfont
    \@ifempty{#1}{\let\thmname\@gobble}{\let\thmname\@iden}%
    \@ifempty{#2}{\let\thmnumber\@gobble}{\let\thmnumber\@iden}%
    \@ifempty{#3}{\let\thmnote\@gobble}{\let\thmnote\@iden}%
    \thm@swap\swappedhead\thmhead{#1}{#2}{#3}}%
  \sbox\@tempboxa{\@theoremhead}%
  \ifdim\wd\@tempboxa>0.7\linewidth \smf@skippttrue\fi
  \ifsmf@skippt
    \global\smf@skipptfalse
    \item [\thm@indent]%
          {\sloppy\@theoremhead\parskip\z@\@@par}%
    \nobreak\everypar{}%
    \let\thmheadnl\relax
  \else
    \item[\hskip\labelsep\thm@indent\unhbox\@tempboxa\the\thm@headpunct]%
%%    \hskip\z@\ignorespaces
  \fi
  \@restorelabelsep
  \thmheadnl % possibly a newline.
  \ignorespaces}
\newif\ifx@pushQED
\@ifundefined{pushQED}{\x@pushQEDfalse}{\x@pushQEDtrue}
\renewenvironment{proof}[1][\proofname]{\par
  \ifx@pushQED \pushQED{\qed}\fi
  \normalfont
  \topsep6\p@\@plus6\p@ \trivlist \itemindent\z@ %% \normalparindent
  \def\@proofhead{\normalfont\itshape #1}%
  \sbox\@tempboxa{\@proofhead}%
  \ifdim\wd\@tempboxa>0.7\linewidth \smf@skippttrue\fi
  \ifsmf@skippt
    \global\smf@skipptfalse
    \item[]{\@proofhead\@@par}
    \nobreak
  \else
    \item[\hskip\labelsep
          \unhbox\@tempboxa\pointrait]%
  \fi
  \ignorespaces
}{%
  \MakeQed
  \endtrivlist
  \@endpefalse
}
\def\MakeQed{\ifsmf@qed
     \ifx@pushQED\popQED\else\qed\fi
     \fi\global\smf@qedtrue}
\newif\ifsmf@qed\smf@qedtrue
\def\skipqed{\global\smf@qedfalse}
\def\th@plain{%
  \let\thm@indent\noindent
  \thm@headfont{\bfseries\smf@boldmath\itshape}%
  \thm@notefont{\bfseries\smf@boldmath\upshape}%
  \thm@preskip.5\linespacing \@plus .5\linespacing
  \thm@postskip\thm@preskip
  \thm@headpunct{\pointrait}
  \itshape }
\def\th@definition{\th@plain \upshape }
\def\th@remark{\th@definition }
\def\smf@captionsenglish{%
 \def\abstractname{Abstract}%
 \def\contentsname{Contents}%
 \def\partname{Part}%
 \def\chaptername{Chapter}%
 \def\refname{References}%
 \def\bibname{Bibliography}%
 \def\indexname{Index}%
 \def\altabstractname{R\'esum\'e}%
 \def\tablename{Table}%
 \def\listtableename{List of tables}%
 \def\figurename{Figure}%
 \def\listfigurename{List of figures}%
 \def\seename{see also}%
 \def\keywordsname{Key words and phrases}%
 \def\altkeywordsname{Mots clefs}%
 \def\translatedby {Translated by}%
 \def\subjclassname
    {\textup{2000} Mathematics Subject Classification}%
 \def\proofname{Proof}%
 \def\definame{Definition}%
 \def\propname{Proposition}%
 \def\theoname{Theorem}%
 \def\conjname{Conjecture}%
 \def\coroname{Corollary}%
 \def\exemname{Example}%
 \def\lemmname{Lemma}%
 \def\remaname{Remark}%
 \def\smfbyname{by}\def\smfandname{\&}%
 \def\smfedbyname{edited by}%
 \def\smfedname{ed.}\def\smfedsname{eds.}%
 \def\smfphdthesisname{Ph.D. Thesis}%
 \def\smfmastersthesisname{Master's Thesis}%
 \let\@makecaption\smf@makecaption
}
\def\smf@captionsfrench{%
 \def\abstractname{R\'esum\'e}%
 \def\contentsname{Table des mati\`eres}%
 \def\partname{Partie}%
 \def\chaptername{Chapitre}%
 \def\bibname{Bibliographie}%
 \def\indexname{Index}%
 \def\refname{R\'ef\'erences}%
 \def\altabstractname{Abstract}%
 \def\appendixname{Appendice}%
 \def\figurename{Figure}%
 \def\listfigurename{Liste des figures}%
 \def\tablename{Table}%
 \def\listtablename{Liste des tables}%
 \def\seename{voir}%
 \def\keywordsname{Mots clefs}%
 \def\altkeywordsname{Key words and phrases}%
 \def\subjclassname
    {Classification math\'ematique par sujets \textup{(2000)}}%
 \def\translatedby {Traduit par}
 \def\proofname{D\'emonstration}%
 \def\definame{D\'efinition}%
 \def\propname{Proposition}%
 \def\theoname{Th\'eor\`eme}%
 \def\conjname{Conjecture}%
 \def\coroname{Corollaire}%
 \def\exemname{Exemple}%
 \def\lemmname{Lemme}%
 \def\remaname{Remarque}%
 \def\smfbyname{par}\def\smfandname{\&}%
 \def\smfedbyname{\'edit\'e par}%
 \def\smfedname{\'ed.}\def\smfedsname{\'eds.}%
 \def\smfphdthesisname{Th\`ese}%
 \def\smfmastersthesisname{M\'emoire}%
 \csname bbl@nonfrenchlistspacing\endcsname
 \let\@makecaption\smf@makecaption
}
\AtBeginDocument{%
  \expandafter\csname smf@captions\smf@language\endcsname
  \ifx\ldf@quit\@undefined  % babel n'est pas charge
    \let\@smflanguage\relax
    \let\@smfaltlanguage\relax
  \else
    \expandafter\main@language\expandafter{\smf@language}
    \ifx\captionsfrenchb\@undefined\else
       \addto\captionsfrenchb{\smf@captionsfrench}\fi
    \ifx\captionsfrench\@undefined\else
       \addto\captionsfrench{\smf@captionsfrench}\fi
    \ifx\captionsfrancais\@undefined\else
       \addto\captionsfrancais{\smf@captionsfrench}\fi
    \ifx\captionsenglish\@undefined\else
       \addto\captionsenglish{\smf@captionsenglish}%
    \fi
    \def\@temp{french}%
    \ifx\smf@language\@temp
            \def\@smflanguage{\smf@silentselectlanguage{french}}%
            \def\@smfaltlanguage{\smf@silentselectlanguage{english}}%
    \else
            \def\@smflanguage{\smf@silentselectlanguage{english}}%
            \def\@smfaltlanguage{\smf@silentselectlanguage{french}}%
    \fi
 \fi }
\def\smf@silentselectlanguage#1{%
  \def\smf@tmp{}%
  \expandafter\ifx\csname date#1\endcsname\relax\else
   \def\smf@tmp{\selectlanguage{#1}}\fi\smf@tmp}
\ProvideTextCommandDefault{\guillemotleft}%
  {\leavevmode\hbox{\fontencoding{U}\fontfamily{lasy}%
                    \fontseries{m}\fontshape{n}\selectfont
    (\kern-0.20em(\kern+0.20em}\nobreak}
\ProvideTextCommandDefault{\guillemotright}%
  {\nobreak\leavevmode
   \hbox{\fontencoding{U}\fontfamily{lasy}
         \fontseries{m}\fontshape{n}\selectfont
   \kern+0.20em)\kern-0.20em)}}
\def\nonbreakingspace{\unskip\nobreak\ \ignorespaces}
\def~{\protect\nonbreakingspace}
\newif\ifsmf@skippt \smf@skipptfalse
\def\skippointrait{\global\smf@skippttrue}
\DeclareRobustCommand{\pointrait}{%
   \unskip
   \ifnum\spacefactor>\@m \hbox{---}\else{\upshape.\hskip 1ex\hbox{---}}\fi}
\DeclareRobustCommand{\MakePointrait}{%
    \ifsmf@skippt\global\smf@skipptfalse \else\nobreak\pointrait\fi}
\def\fullwidthdisplay{\displayindent\z@ \displaywidth\columnwidth}
\edef\@tempa{\noexpand\fullwidthdisplay\the\everydisplay}
\everydisplay\expandafter{\@tempa}
\newcommand\see[2]{{\em \seename\/} #1}%
\calclayout % initialize
\pagenumbering{arabic}
\pagestyle{headings}
\thispagestyle{plain}
\emergencystretch 2em
\endinput
%%
%% End of file `smfart.cls'.
