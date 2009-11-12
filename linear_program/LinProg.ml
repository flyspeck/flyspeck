(*Define the notion of solution*)
let is_solution_DEF = define `( is_solution [] ([] , #0) = T ) /\
 ( is_solution (CONS x1 xs) ((CONS a1 teq) , b) = is_solution xs ( teq , (b - a1 * x1) ) )`;;

g `~ (is_solution [ #3 ] ( [ #2 ], #5 ))`;; (*still can't prove this because of the current incomplete definition of is_solution*)

(*Prove the most basic theorem of multiplying both side with the same non-zero integer*)
