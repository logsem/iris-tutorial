COQMAKEFILE ?= Makefile.coq
COQDOCEXTRAFLAGS = -s
COQDOCJS_LN = true
COQ_PROJ ?= _CoqProject

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

$(COQMAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $^ -o $@

force $(COQ_PROJ) Makefile: ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f $< $@

.PHONY: clean all force
