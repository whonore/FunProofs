PROOFS := $(wildcard *.v Lib/*.v)

.PHONY: all clean

all: CoqMakefile
	$(MAKE) -f $<

$(PROOFS:.v=.vo): CoqMakefile
	$(MAKE) -f $< $@

_CoqProject.files: _CoqProject $(PROOFS)
	echo $(PROOFS) | cat _CoqProject - > $@

CoqMakefile: _CoqProject.files
	coq_makefile -f $< -o $@

clean:
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf _CoqProject.files
