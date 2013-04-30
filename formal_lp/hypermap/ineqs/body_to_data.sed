1 {
	i\
module Lp_body_ineqs_data = struct\
\
let data = [
}

$ {
	i\
];;\
\
end;;
}

/ineq[[:alnum:]]* '/ {
	s/\(ineq[[:alnum:]]*\)/"\1", /
	s/'ID\[\([[:alnum:][:space:]]*\)\]'/"\1", /
	N
	s/[{\n}:]//g
	s/(.*) in \([[:alnum:]_]*\)/"\1"/
	s/[[:space:]][[:space:]]*/ /g
	s/^/\t/
	s/$/;/
	s/ ;/;/
	P
}

