general: \
existsT.vo \
gen.vo \
genT.vo

gen.vo: gen.v
existsT.vo: existsT.v
genT.vo: genT.v existsT.vo gen.vo

%.vo : %.v
	#echo doing $*.v >>log
	#dirname $* >>log
	(cd `dirname $*` ; pwd >> log ; coqc `basename $*.v`) 
	#pwd >> log
	# coqc -Q general $*.v

clean_general : 
	rm -rf  *.vo *.glob
