SOLUTIONS := $(wildcard theories/*.v)
EXERCISES := $(addprefix exercises/,$(notdir $(SOLUTIONS)))

EXTRA_DIR:=rocqdocjs/extra
ROCQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export ROCQDOCFLAGS

all: Makefile.rocq
	+make -f Makefile.rocq all
.PHONY: all

clean: Makefile.rocq
	+make -f Makefile.rocq clean
	rm -f Makefile.rocq
.PHONY: clean

html: Makefile.rocq _RocqProject
	rm -fr html
	+make -f Makefile.rocq $@
	cp -R $(EXTRA_DIR)/resources html
.PHONY: html

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

exercises: $(EXERCISES)
.PHONY: exercises

$(EXERCISES): exercises/%.v: theories/%.v gen-exercises.awk
	@if test -f $@ && ! git diff --exit-code $@ >/dev/null; then \
	  echo "Exercise file $@ has been changed; skipping exercise generation"; \
	else \
	  echo "Generating exercise file $@ from $<"; \
	  awk -f gen-exercises.awk < $< > $@; \
	fi

ci: all
	+@make -B exercises # force make (in case exercise files have been edited directly)
	if [ -n "$$(git status --porcelain)" ]; then echo 'ERROR: Exercise files are not up-to-date with solutions. `git diff` and `git status` after re-making them:'; git diff; git status; exit 1; fi
.PHONY: ci
