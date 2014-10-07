hashes:
#	grep -r "Hash" output | sort -V | \
#		sed -e 's/.*Hash  //' -e 's/^.*,(/(/' > hashes0.txt
	find output -type f ! -regex ".*/\..*" -exec grep "Hash" '{}' \; | sort -V | \
		sed -e 's/.*Hash  //' -e 's/^.*,(/(/' > hashes0.txt
	sed -e '/prep-5744538693/{d}' \
	    -e '/prep-6944699408 a reduced/{d}' \
	    -e '/prep-7043724150 a reduced v2/{d}' hashes0.txt > hashes.txt
	find out-extra -type f ! -regex ".*/\..*" -exec grep "Hash" '{}' \; | sort -V | \
		sed -e 's/.*Hash  //' -e 's/^.*,(/(/' >> hashes.txt
	rm hashes0.txt

hashes-urban:
	find urban/out -type f ! -regex ".*/\..*" -exec grep "Hash" '{}' \; | sort -V | \
		sed -e 's/.*Hash  //' -e 's/^.*,(/(/' > hashes2.txt
	grep "Hash" output/fail/sharp_out.txt | \
		sed -e 's/.*Hash  //' -e 's/^.*,(/(/' >> hashes2.txt

fails:
	grep -r "FAIL" output | sort -V > fails.txt
	grep -r "ERR" output | sort -V >> fails.txt
	sed -e '/TAC_PROOF/{d}' -e '/SDCCMGA/{d}' fails.txt > fails0.txt
	rm fails.txt
	mv fails0.txt fails.txt

time:
	find output -type f ! -regex ".*/\..*" -exec grep "Time" '{}' \; | \
		sed -e 's/.*Time.*://' -e 's/ //g' | \
		awk '{s += $$0} END {print s / 3600}'

time-urban:
	find urban/out -type f ! -regex ".*/\..*" -exec grep "Time" '{}' \; | \
		sed -e 's/.*Time.*://' -e 's/ //g' | \
		awk '{s += $$0} END {print s / 3600}'

max-time:
	find output -type f ! -regex ".*/\..*" -exec grep "Time" '{}' \; | \
		sed -e 's/.*Time.*://' -e 's/ //g' | \
		awk '{if ($$0 > s) {s = $$0}} END {print s}'

max-time-urban:
	find urban/out -type f ! -regex ".*/\..*" -exec grep "Time" '{}' \; | \
		sed -e 's/.*Time.*://' -e 's/ //g' | \
		awk '{if ($$0 > s) {s = $$0}} END {print s}'

filter-sharp:
	sed -e '/13158,(prep-TSKAJXY-RIBCYXU sharp,0)/{d}' \
	    -e '/13077,(prep-TSKAJXY-IYOUOBF sharp v2,0)/{d}' \
	    -e '/11966,(prep-OMKYNLT 3336871894,0)/{d}' \
	    -e '/11959,(prep-GRKIBMP B V2,0)/{d}' \
	    -e '/13075,(prep-QZECFIC wt0 corner,0)/{d}' \
	    ineqs/ineqs_all.txt > ../ineqs.txt