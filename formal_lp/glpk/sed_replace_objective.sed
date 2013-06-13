/obj.*:/ {
:repeat
	s/Subject To//
	t end
	N
	b repeat
:end
	s/\(obj.*:\).*/\1/
	r objective.txt
	a Subject To
}
