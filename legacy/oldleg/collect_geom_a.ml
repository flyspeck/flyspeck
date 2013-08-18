let DOT_BASIS_BASIS_UNEQUAL = prove(`!i j. ~(i = j) ==> (basis i) dot (basis j) = &0`,
  SIMP_TAC[basis; dot; LAMBDA_BETA] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
   SIMP_TAC[SUM_0; REAL_MUL_RZERO; REAL_MUL_LZERO; COND_ID]);;



