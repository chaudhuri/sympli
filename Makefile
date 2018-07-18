SRCS := $(shell cat sym.mlb | grep -v Group | grep -v SML_LIB)

sym: ${SRCS} sym.mlb
	mlton sym.mlb

sym-time: ${SRCS} sym.mlb
	mlton -profile time -output sym-time sym.mlb

sym-alloc: ${SRCS} sym.mlb
	mlton -profile alloc -output sym-alloc sym.mlb

.PHONY : sym-nj
sym-nj: sources.cm
	echo 'CM.make(); SMLofNJ.exportFn ("sym", Top.export);' | sml

.PHONY : clean
clean:
	${RM} sym sym-time sym-alloc sym.x86-linux

frontend/prop.lex.sml: frontend/prop.lex
	mllex frontend/prop.lex

frontend/prop.grm.sig frontend/prop.grm.sml: frontend/prop.grm
	mlyacc frontend/prop.grm
