SHELL=/bin/bash

MARK=../local_resources/mark.sh
PANDOC=pandoc --toc # -c md.css

SRC=.
DOC=../doc

# tags!
MLS= \
	@fs_spec.ml

MDS=$(MLS:.ml=.md) @dep.md
# FIXME why have a separate dep.md attribute? so that we can style it differently!

# ML target, comment documentation in md tags
MLTARGET=-pre $(MDS) "(*" \
	-post       $(MDS) "*)"

# HTML target, pretty print ocaml
HTMLTARGET=-pre $(MLS) "~~~{.ocaml}" \
    -post       $(MLS) "~~~" \
    -pre        @dep.md "<div style='background-color:\#FFFFCC'>" \
    -post       @dep.md "</div>" \

################################################################################
all: srcs docs fs_spec.native

# phony 
srcs: $(SRC)/fs_spec.ml $(SRC)/fs_spec.toplevel.ml

# phony 
docs: $(DOC)/fs_spec.html

# check that the spec is wellformed ocaml
fs_spec.native: fs_spec.ml
	ocamlbuild -libs unix,bigarray fs_spec.native

################################################################################
# ml targets

$(SRC)/fs_spec.toplevel.ml: $(SRC)/fs_spec.ml
	-chmod u+w $@
	echo "module Fs_spec = struct " >$@
	cat $< >>$@
	echo " end" >> $@
	echo ";;" >> $@
	chmod u-w $@

$(SRC)/fs_spec.ml: fs_spec.mng
	-chmod u+w $@
	$(MARK) $(MLTARGET) -tag @fs_spec.ml $(MDS) -in fs_spec.mng >$@
	chmod u-w $@


################################################################################
# doc targets

$(DOC)/fs_spec.md: fs_spec.mng
	$(MARK) $(HTMLTARGET) -tag $(MLS) $(MDS) @opsparser.g -in fs_spec.mng >$@

$(DOC)/%.html: $(DOC)/%.md
	$(PANDOC) -s $< >$@


################################################################################
#clean: FORCE
#	rm -f $(SRC)/core1.ml $(SRC)/corenotermnonterm.ml $(SRC)/main.ml $(SRC)/main_gen.ml 

clean: FORCE
	rm -f $(SRC)/fs_spec.ml $(SRC)/fs_spec.toplevel.ml
	rm -f $(DOC)/fs_spec.md $(DOC)/fs_spec.html
	ocamlbuild -clean

FORCE:

#.PRECIOUS: $(SRC)/%.md
