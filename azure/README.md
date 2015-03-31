Compiled HOL Light and FormalIneqs
==================================

##Build

Requirements: 

- [OCaml](http://ocaml.org/) with a native compiler (do
not forget `make opt` if you are building from source code)

- [Camlp5](http://camlp5.gforge.inria.fr/)

- [GNU parallel](http://www.gnu.org/software/parallel/) (for the parallel
verification of inequalities).

(Tested with OCaml 4.01 and Camlp5 6.11).

    make parser
    make hol-core
    make hol-lib
    make ineq
    make flyspeck
    make build

##Performance Test

    make test_flyspeck
    ./test_flyspeck

##Verification of Individual Inequalities

    ./verifier data_file a b > out.txt

`data_file` is a file with inequalities.
`a` is the first case (inequality) for the verification, 
`b` is the last case (inequality) for the verification. 

Example:

    ./verifier results/ineqs/ineqs2_trig.txt 0 13 > out.txt

##Parallel Verification of All Strict Inequalities

    ./run-parallel 120

Here, 120 is the number of parallel jobs. The script uses GNU parallel
to execute several independent copies of `verifier`
simultaneously. The data file with inequalities is `ineqs.txt`. Other
parameters are taken from the file `pars.txt`. All results are saved
in the directory `out`.

##Verification of Sharp Inequalities

    make sharp
    ./sharp_verifier > out_sharp.txt

##FormalIneqs Source Update

    cd scripts
    ocaml create_native_formal_ineqs.ml

##Verification of all Flyspeck Nonlinear Inequalities

    rm -rf out
    ./run-parallel 120
    make sharp
    ./sharp_verifier > out_sharp.txt
    find out -type f ! -regex ".*/\..*" -exec grep "Hash" '{}' \; | sort -V | sed -e 's/.*Hash  //' -e 's/^.*,(/(/' > hashes.txt
    grep "Hash" out_sharp.txt | sed -e 's/.*Hash  //' -e 's/^.*,(/(/' >> hashes.txt

The result of these commands is the file `hashes.txt` which contains
hashes of theorems for all Flyspeck nonlinear inequalities.


