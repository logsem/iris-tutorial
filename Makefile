SOLUTIONS := $(wildcard theories/*.v)
EXERCISES := $(addprefix exercises/,$(notdir $(SOLUTIONS)))

EXTRA_DIR:=coqdocjs/extra
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

html: Makefile.coq _CoqProject
	rm -fr html
	+make -f Makefile.coq $@
	cp $(EXTRA_DIR)/resources/* html

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

exercises: $(EXERCISES)

.PHONY: exercises

$(EXERCISES): exercises/%.v: theories/%.v gen-exercises.awk
	@if test -f $@ && ! git diff --exit-code $@ >/dev/null; then \
	  echo "Exercise file $@ has been changed; skipping exercise generation"; \
	else \
	  echo "Generating exercise file $@ from $<"; \
	  gawk -f gen-exercises.awk < $< > $@; \
	fi

ci: all
	+@make -B exercises # force make (in case exercise files have been edited directly)
	if [ -n "$$(git status --porcelain)" ]; then echo 'ERROR: Exercise files are not up-to-date with solutions. `git diff` and `git status` after re-making them:'; git diff; git status; exit 1; fi

.PHONY: clean all
