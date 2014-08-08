Compiled HOL Light and FormalIneqs
==================================

##Build
```
make parser
make hol-core
make hol-lib
make ineq
make flyspeck
```

##Performance Test
```
make test_flyspeck
./test_flyspeck
```

##Verification
```
make build
./verifier data_file a b > out.txt
```
`data_file` is a file with inequalities.
`a` is the first case (inequality) for the verification, 
`b` is the last case (inequality) for the verification. 

Example:
```
./verifier results/ineqs/ineqs2_trig.txt 0 13 > out.txt
```

##Verification of Sharp Inequalities
```
make sharp
./sharp_verifier > out_sharp.txt
```

##FormalIneqs Source Update
```
cd scripts
ocaml create_native_formal_ineqs.ml
```
