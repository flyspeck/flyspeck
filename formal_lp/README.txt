Formal verification of Flyspeck linear programs.

It is assumed that a global variable "flyspeck_dir" contains
a path to the "text_formalization" directory of the Flyspeck
project.

-----------------------------------------------------
I. Construction of linear program certificates
-----------------------------------------------------

This step can be skipped. All linear program certificates
are in the repository at 
flyspeck_dir/../formal_lp/glpk/binary

All certificate files are binary files which contain serialized
OCaml data structures. These files were prepared with OCaml 4.01.

All certificates can be reconstructed manually in the following way.

0) Install glpk (http://www.gnu.org/software/glpk/) and
mono (http://www.mono-project.com/Main_Page).

1) Make sure that OCaml supports dynamic loading of compiled libraries or
create a custom toplevel with the command
ocamlmktop unix.cma nums.cma str.cma -o my_ocaml

2) Make sure that the environment has the FLYSPECK_DIR variable.
This variable must contain a path to the "text_formalization" directory
of the Flyspeck project.

3) Start OCaml and load HOL Light (#use "hol.ml"). No other HOL Light
libraries are required.

4) Load the file build_main.hl:
needs "flyspeck_dir/../formal_lp/glpk/build_main.hl";;

Here, replace flyspeck_dir with an absolute path to the "text_formalization"
directory of the Flyspeck project.

5) Build all linear program certificates with the command
Lp_build_main.build_all 1000;;

Here, 1000 is a parameter which specifies how many terminal cases will be
saved in each certificate file for easy linear program certificates.
All certificates will be saved in 
flyspeck_dir/../formal_lp/glpk/binary
Certificates of easy linear programs will be saved in files with the prefix "easy".
Certificates of hard linear programs will be saved in files with the prefix "hard".

It is also possible to build either easy linear program certificates or hard linear
program certificates. The corresponding commands are
Lp_build_main.build_all_easy 1000;;
Lp_build_main.build_all_hard 1;;

-----------------------------------------------------
II. Formal verification of Flyspeck linear programs
-----------------------------------------------------

0) Make sure that the directory flyspeck_dir/../formal_lp/glpk/binary
contains all certificate files.

1) Start OCaml and load the Flyspeck project.

2) needs "../formal_lp/hypermap/verify_all.hl";;

3) let result = Verify_all.verify_all [] None;;
It takes about 15 hours to verify all linear programs (on Mac mini 2GHz, 2GB).

Commands
let result_easy = Verify_all.verify_easy [] None;;
let result_hard = Verify_all.verify_hard [] None;;
will verify easy and hard linear programs separately.

result has the type ((string * thm) list * float) list. Each element of the list
contains a list of theorems for all certificates in one data file and
the verification time for this data file.

All theorems should be in the form
lp_ineqs, lp_main_estimate, 
  iso (hypermap_of_fan (V,ESTD V)) (hypermap_of_list L) |- contravening V ==> F
Here, L is an explicit list of lists of numbers which encodes a particular hypermap.
`lp_ineqs` is a constant which defines all nonlinear inequality required for
verification of linear programs.
`lp_main_estimate` is a constant which defines the main estimate conclusions.

The command
Verify_all.test_result result;;
will return the total verification time, 
a union of all conclusions (must be `contravening V ==> F`),
and a union of all assumptions without isomorphism assumptions 
(must be [`lp_ineqs`; `lp_main_estimate`]).
