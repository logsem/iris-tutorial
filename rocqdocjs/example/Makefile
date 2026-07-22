ROCQMAKEFILE ?= Makefile.rocq
ROCQDOCEXTRAFLAGS = -s
ROCQDOCJS_LN = true
ROCQ_PROJ ?= _RocqProject

all: $(ROCQMAKEFILE)
	$(MAKE) -f $^ $@

clean: $(ROCQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

$(ROCQMAKEFILE): $(ROCQ_PROJ)
	$(ROCQBIN)rocq_makefile -f $^ -o $@

force $(ROCQ_PROJ) Makefile: ;

%: $(ROCQMAKEFILE) force
	@+$(MAKE) -f $< $@

.PHONY: clean all force
