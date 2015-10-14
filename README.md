# The Flyspeck Project

Welcome to the Flyspeck project, which gives a formal proof of the Kepler conjecture
in the HOL Light proof assistant.

The project was completed August 10, 2014.

## Introduction

The purpose of the flyspeck project was to produce a formal proof of the Kepler Conjecture. The name `flyspeck` comes from matching the pattern `/f.*p.*k/` against an English dictionary. FPK in turn is an acronym for "The Formal Proof of Kepler."

## Resources

There is an [installation guide](https://github.com/flyspeck/flyspeck/wiki/Installation%20Guide) for the project and other [Wiki pages](https://github.com/flyspeck/flyspeck/wiki/).

The formalization project is based on the book [Dense Sphere Packings](downloads/DenseSpherePackings.pdf), which is available from Cambridge University Press.

## License

This project is distributed under the [MIT Licence](http://opensource.org/licenses/mit-license.php).

## Thanks

This project was supported by NSF through grant 0503447 on the "Formal Foundations of Discrete Geometry" and grant 0804189 on the "Formal Proof of the Kepler Conjecture", the Benter Foundation, Microsoft Azure Research, the University of Pittsburgh, Radboud Research Facilities, Institute of Math (VAST), and VIASM.

## Directory structure 

The main proof scripts are in the subdirectory 
[`text_formalization`](text_formalization).
The primary files used to build the project are in 
[text_formalization/build](text_formalization/build).
See especially [`text_formalization/build/ocamlinit_hol_light.ml`](text_formalization/build/ocamlinit_hol_light.ml)

The directory structure for the flyspeck project is as follows.

[`azure`](azure)
 Files related to the formal verification of nonlinear inequalities.
 These inequalities were first formally verified by a computation on the Microsoft Azure Cloud.

[`emacs`](emacs)
  Files related to the HOL Light mode for emacs.
  These files are not part of the flyspeck project, but they may be useful for those who run HOL Light inside emacs.

[`formal_graph`](formal_graph)
  Files related to the formal verification of the classification of tame graphs in
  the Isabelle proof assistant.  Most of these files are a backup of files are part of the
  Isabelle Archive of Formal Proofs 
  afp.sf.net ([afp.sourceforge.net/entries/Flyspeck-Tame.shtml](http://afp.sourceforge.net/entries/Flyspeck-Tame.shtml)).  
  That archive should be used to download
  the code for the formal verification of the classification  of tame graphs.  
  The files here are solely to aid in 
  the translation of the statement of the theorem into HOL Light.

[`formal_ineqs`](formal_ineqs)
  Files related to the formal verification of nonlinear inequalities.

[`formal_lp`](formal_lp)
  Files related to the formal verification on linear programs.

[`glpk`](glpk)
  Files related to the informal verification of linear programs.  

[`informal_code`](informal_code)
  Code used for the informal computer programs used in the proof of the Kepler conjecture.
  These files are not required for the flyspeck project.
  
[`jHOLLight`](jHOLLight)
  Code for the java front end that is used for Solovyev's SSReflect mode for HOL Light.

[`kepler_tex`](kepler_tex)
  Latex source files for the book "Dense Sphere Packings"

[`legacy`](legacy)
  This directory contains dead code that is no longer of any use. Ignore this directory.

[`text_formalization`](text_formalization)
  This is the main directory of the project. It contains the files for the formalization of the
  text part of the flyspeck project, as described in the book "Dense Sphere Packings"
  See the README file in that directory 
  for more instructions on loading and auditing the project.

  [`text_formalization/build`](text_formalization/build) directory contains files related to building the project.

[`usr`](usr)
  These files are not part of the flyspeck project.
  It mostly contains an assortment of latex files for articles written by Hales.
  
