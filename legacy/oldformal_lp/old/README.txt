Formal verification of linear programs in HOL Light.

-----------------------------------------------------
I. Verification of bounds of general linear programs.
-----------------------------------------------------

See lp_example directory for an example.

Input:
example.mod - a linear program in the AMPL format
(should be a maximization problem.)

Steps for producing a formal verification procedure.

1. Run glpk with the following parameters
glpsol -m example.mod -w out.txt --wcpxlp out.lp

This command will solve the linear program and two files will be created:
out.txt - contains the solution of the linear program;
out.lp - the linear program in CPLEX LP format.

Note: both output files should have the same name.

2. Run LP-HL program with the following parameters
LP-HL out -0.6938

out - the name of the data files (out.txt and out.lp);
-0.6938 - the bound which we want to prove (can be any decimal number).

This command will create the file out_test.hl which contains HOL Light
code for a formal verification of the given bound.

Note: to run LP-HL on Linux or MacOS, use Mono:
http://www.mono-project.com/Main_Page

3. To use the file out_test.hl in HOL Light, you need to load prove_lp.hl:

needs "arith/prove_lp.hl";;

(it is assumed that the formal_lp in the HOL Light path.)

Then, you can load the file created in the previous step:

needs "out_test.hl";;

The main theorem can be accessed with the command:

Lp.result;;

This theorem has a list of assumptions which correspond to the constraints of
the linear program.


--------------------------------------------
II. Verification of Flyspeck linear programs
--------------------------------------------

1. Run LP-HL without argument in a directory containing the following files:
000.txt - internal description of sets of hypermap elements
          (this file can be found in the LP-HL directory);
tame_archive.txt - describes all tame hypermaps;
{id}.lp, {id}.txt - files containing the linear program and its solution for the hypermap named {id}.

Files {id}_out.hl will be created for each hypermap linear program.

2. Load ineqs/nobranching_lp.hl:

needs "ineqs/nobranching_lp.hl";;

After that, formal proofs can be produced:

needs "{id}_out.hl";;

The main theorem:
Test_case.result;;
