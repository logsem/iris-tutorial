EXTRA_DIR:=coqdocjs/extra
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

# Default target
all: Makefile.coq
	+@$(MAKE) -f Makefile.coq all
.PHONY: all

html: Makefile.coq all
	rm -fr html
	@$(MAKE) -f Makefile.coq $@
	cp -R $(EXTRA_DIR)/resources html

.PHONY: coqdoc

# Permit local customization
-include Makefile.local

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f Makefile.coq $@
phony: ;
.PHONY: phony

clean: Makefile.coq
	+@$(MAKE) -f Makefile.coq clean
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq .lia.cache builddep/*
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq $(EXTRA_COQFILES)

# Some files that do *not* need to be forwarded to Makefile.coq.
# ("::" lets Makefile.local overwrite this.)
Makefile Makefile.local _CoqProject $(OPAMFILES):: ;
