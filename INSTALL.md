# Step by Step Installation Guide

This guide was tested with [OCaml 4.14.2](#ocaml-4142) and [OCaml 4.07.1](#ocaml-4071) on Ubuntu 22.04.2.

## Ocaml 4.14.2

1) Install [opam](https://ocaml.org/docs/installing-ocaml#1-install-opam)

2) Install [OCaml](https://ocaml.org/docs/installing-ocaml#installing-ocaml)

    ```
    opam init -y
    eval $(opam env)
    opam switch create 4.14.2
    eval $(opam env)
    ```

3) Install additional HOL Light dependencies

    ```
    opam install zarith
    ```

4) Install Camlp5:

    ```
    opam pin -y add camlp5 8.02.01
    opam install camlp5
    ```

5) Verify that OCaml and Camlp5 are successfully installed:

    ```
    which ocaml
    which camlp5
    ocaml -I `camlp5 -where`
    #quit;;
    ```

## Ocaml 4.07.1

1) Install [opam](https://ocaml.org/docs/installing-ocaml#1-install-opam)

2) Install [OCaml](https://ocaml.org/docs/installing-ocaml#installing-ocaml)

    ```
    opam init -y
    eval $(opam env)
    opam switch create 4.07.1
    eval $(opam env)
    ```

3) Install additional HOL Light and Flyspeck dependencies

    ```
    opam install num stdlib-shims
    ```

4) Install Camlp5:

    ```
    opam pin -y add camlp5 7.10
    opam install camlp5
    ```

5) Verify that OCaml and Camlp5 are successfully installed:

    ```
    which ocaml
    which camlp5
    ocaml -I `camlp5 -where`
    #quit;;
    ```

## HOL Light

1) Clone the HOL Light repository

    ```
    git clone https://github.com/jrh13/hol-light.git
    ```

2) The most recent version of HOL Light may be incompatible with Flyspeck. 
   The latest tested version of HOL Light is the commit `d8366986e22555c4e4c8ff49667d646d15c35f14`

   ```
   cd hol-light
   git checkout d836698
   ```

3) Initialize HOL Light

    ```
    cd hol-light
    make
    ```

    If you get any errors here then make sure that a correct version of Camlp5 is used.

## Flyspeck

1) Clone the Flyspeck repository

    ```
    git clone https://github.com/flyspeck/flyspeck.git
    ```

2) Skip this step if you don't need to load serialized nonlinear inequalities.

   The current Flyspeck version is compatible with the commit
   `d8366986e22555c4e4c8ff49667d646d15c35f14` of HOL Light.
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

   (This step has not been tested yet so it may be necessary to get an older HOL Light version in case of errors.)

## Loading Flyspeck

1) Edit the paths to Flyspeck and HOL Light directories in `flyspeck/load_flyspeck.ml`.
   Change these lines:

    ```
    let flyspeck_dir = "/home/user/flyspeck/text_formalization";;
    let hollight_dir = "/home/user/hol-light";;
    ```

2) Run `{path to HOL Light}/hol.sh` from the Flyspeck directory.

    ```
    cd flyspeck
    {path to HOL Light}/hol.sh
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

   The function `build_to` does not verify bounds of linear programs. 
   To verify these bounds, use the function `build_to_full`.

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

1) Install [DMTCP](https://github.com/dmtcp/dmtcp/blob/master/INSTALL.md)

2) Run `dmtcp_coordinator` in a terminal window.

3) In a new terminal window run 

    ```
    cd hol-light
    dmtcp_launch ./hol.sh
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

HOL Light files compiled with ocamlopt are loaded approximately 5 times faster.

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

    If you get a stack overflow error, try `ulimit -S -s 131072` before running `make mult`.

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