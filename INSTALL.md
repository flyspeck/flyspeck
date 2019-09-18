# Step by Step Installation Guide

## Ocaml

1) Install [OPAM](https://opam.ocaml.org/doc/Install.html)

2) Install [OCaml](https://ocaml.org/docs/install.html#OPAM).
   The recommended and tested OCaml version is 4.04.2.

    ```
    opam init
    eval `opam env`
    opam switch create 4.04.2
    eval `opam env`
    ```

    Note: if your OPAM version is < 2 then the commands are different:

    ```
    opam init
    eval `opam config env`
    opam switch 4.04.2
    eval `opam config env`
    ```

4) Install Camlp5:

    ```
    opam install camlp5
    ```

5) Verify that OCaml and Camlp5 are successfully installed:

    ```
    which ocaml
    which camlp5
    ocaml -I `camlp5 -where`
    ```

6) If the installed OCaml version is >= 4.06 then it is necessary to install the OCaml Num library:

    ```
    opam install num
    ```

## HOL Light

1) Clone the HOL Light repository

    ```
    git clone https://github.com/jrh13/hol-light.git
    ```

2) The most recent version of HOL Light may be incompatible with Flyspeck. 
   The latest tested version of HOL Light is the commit `e701cb5292a4c6cf269ebb8490700de095e48a94`

   ```
   cd hol-light
   git checkout e701cb5292a4c6cf269ebb8490700de095e48a94
   ```

3) Initialize HOL Light

    ```
    cd hol-light
    make
    ```

    If you get any errors here then try different versions of OCaml and Camlp5. The tested OCaml version is 4.04.2 and the tested Camlp5 version is 7.06.

## Flyspeck

1) Clone the Flyspeck repository

    ```
    git clone https://github.com/flyspeck/flyspeck.git
    ```

2) Skip this step if you don't need to load serialized nonlinear inequalities.

   The current Flyspeck version is compatible with the commit
   `e701cb5292a4c6cf269ebb8490700de095e48a94` of HOL Light.
   This version of HOL Light is incompatible with serialized Flyspeck nonlinear inequalities.
   If you want to load serialized nonlinear inequalities, then use the following HOL Light commit

   ```
   cd hol-light
   git checkout 5f7cab746b06d10553d55041a3962e174da9881d
   ```

   It is also necessary to checkout the following version of Flyspeck
   
   ```
   cd flyspeck
   git checkout adfe470ad72372357a18843ad4b94377cb0790b9
   ```

## Loading Flyspeck

1) Copy `flyspeck/load_flyspeck.ml` to the HOL Light directory (alternatively,
   provide a full path to `load_flyspeck.ml` when it is loaded in HOL Light).
   Open the copy and edit the paths to Flyspeck and HOL Light directories.

2) Load HOL Light

    ```
    cd hol-light
    ocaml -I `camlp5 -where`
    #use "hol.ml";;
    ```

3) Wait until HOL Light is loaded and then initialize Flyspeck

    ```
    needs "load_flyspeck.ml";;
    ```

    This command will take a relatively long time since the full 
    HOL Light multivariate analysis library is loaded.

4) Now it is possible to load Flyspeck files with the function `build_to`.
   Examples:

   ```
   build_to "hypermap/hypermap.hl";  
   build_to "local/LFJCIXP.hl"
   ```

   The function `build_to` ignores files related to the verification of bounds of
   linear programs. To verify this bounds, use the function `build_to_full`.

5) To load the main statement, use the following command:

    ```
    build_to "general/the_main_statement.hl";;
    ```

   To load the main statement with linear program bounds, use the command:

    ```
    build_to_full "general/the_kepler_conjecture.hl";;
    ```

   Note: you can uncomment the corresponding lines in `load_flyspeck.ml`; then
   all Flyspeck files can be loaded with `needs "load_flyspeck.ml"`.

## [Optional] Checkpointing with DMTCP

1) Install [DMTCP](http://dmtcp.sourceforge.net/downloads.html)

2) Run `dmtcp_coordinator` in a terminal window.

3) In a new terminal window run 

    ```
    cd hol-light
    dmtcp_launch ocaml -I `camlp -where`
    #use "hol.ml";;
    ```

4) When HOL Light is loaded, type `c` and press `ENTER` in the `dmtcp_coordinator` window.

   A checkpointed session of HOL Light is saved in a file with the extension `.dmtcp`.
   This file is saved in the directory where `dmtcp_coordinator` have been started.
   Rename this file to `dmtcp_hol.dmtcp`.

5) Close the current HOL Light session with `#quit;;`. Restart the saved session:

    ```
    dmtcp_restart dmtcp_hol.dmtcp
    ```

6) It possible to create as many checkpointed HOL Light sessions as required. 
   I recommend to run `Gc.compact();;` every time before creating a new checkpoint.

## [Optional] Compiling Flyspeck with ocamlopt

HOL Light files compiled with ocamlopt are loaded approximately 5 times faster than with
the default OCaml toplevel.

1) Checkout the following HOL Light fork

    ```
    git clone https://github.com/monadius/hol-light.git hol-light-native
    cd hol-light-native
    git checkout native
    make
    ```

2) Compile the HOL Light Multivariate library

    ```
    cd _native
    make core
    make mult
    ```

3) Checkout the native branch of Flyspeck

    ```
    cd flyspeck
    git checkout native
    ```

4) Edit `flyspeck/Makefile`: change the path to the compiled HOL Light (the first line of `Makefile`).

5) Compile and run Flyspeck

    ```
    make flyspeck
    ./flyspeck
    ```