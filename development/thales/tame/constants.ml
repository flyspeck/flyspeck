(* modified from
http://afp.sourceforge.net/browser_info/current/HOL/Flyspeck-Tame/Tame.html
*)
subsection {* Constants \label{sec:TameConstants}*}

constdefs squanderTarget :: "nat"
 "squanderTarget ≡ 1541" 

constdefs excessTCount :: "nat => nat" (*<*) ("\<a>")(*>*)

 "\<a> t ≡ if t < 5 then squanderTarget
     else 630"

constdefs squanderVertex :: "nat => nat => nat"  (*<*)("\<b>")(*>*)

 "\<b> p q ≡ if p = 0 ∧ q = 2 then 1296
     else if p = 0 ∧ q = 3 then 618
     else if p = 0 ∧ q = 4 then 1000
     else if p = 1 ∧ q = 2 then  660
     else if p = 1 ∧ q = 3 then  618
     else if p = 2 ∧ q = 1 then  800
     else if p = 2 ∧ q = 2 then  412
     else if p = 2 ∧ q = 3 then 1285
     else if p = 3 ∧ q = 1 then  315
     else if p = 3 ∧ q = 2 then  830
     else if p = 4 ∧ q = 0 then  350
     else if p = 4 ∧ q = 1 then  374
     else if p = 5 ∧ q = 0 then   40
     else if p = 5 ∧ q = 1 then 1144
     else if p = 6 ∧ q = 0 then  689
     else if p = 7 ∧ q = 0 then 1450
     else squanderTarget"

constdefs scoreFace :: "nat => int" (*<*)("\<c>")(*>*)

 "\<c> n ≡ 0"

constdefs squanderFace :: "nat => nat" (*<*)("\<d>")(*>*)

 "\<d> n ≡ if n = 3 then 0
     else if n = 4 then  206
     else if n = 5 then  483
     else if n = 6 then  760
     else if n = 7 then 1038
     else if n = 8 then 1315
     else squanderTarget" 
