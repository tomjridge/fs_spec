SHELL=/bin/bash

MARK=../local_resources/mark.sh
PANDOC=pandoc --toc # -c md.css

SRC=.
DOC=../doc

# tags!
MLS= \
	@fs_prelude.ml \
	@fs_spec.ml \
	@dir_heap.ml \
	@dir_tree.ml \
	@unix_impl.ml


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

# ocamlbuild include dirs
IS=local_resources

################################################################################
all: srcs docs fs_spec.native dir_heap.native fs_spec_extras.native dir_tree.native unix_impl.native

# phony 
srcs: $(SRC)/fs_prelude.ml $(SRC)/fs_prelude.toplevel.ml \
	$(SRC)/fs_spec.ml $(SRC)/fs_spec.toplevel.ml \
	$(SRC)/dir_heap.ml $(SRC)/dir_heap.toplevel.ml \
	$(SRC)/dir_tree.ml $(SRC)/dir_tree.toplevel.ml \
	$(SRC)/unix_impl.ml $(SRC)/unix_impl.toplevel.ml \
	$(SRC)/fs_spec_extras.ml $(SRC)/fs_spec_extras.toplevel.ml

# phony 
docs: $(DOC)/fs_spec.html $(DOC)/dir_heap.html $(DOC)/dir_tree.html $(DOC)/unix_impl.html

# check that the spec is wellformed ocaml
fs_spec.native: fs_spec.ml
	ocamlbuild -libs unix,bigarray fs_spec.native

fs_spec_extras.native: fs_spec_extras.ml fs_spec.ml fs_prelude.ml
	ocamlbuild -libs unix,bigarray,str -pkg sha -Is $(IS) fs_spec_extras.native

dir_heap.native: dir_heap.ml fs_spec.ml fs_prelude.ml
	ocamlbuild -libs unix,bigarray dir_heap.native

dir_tree.native: dir_tree.ml fs_spec.ml fs_prelude.ml
	ocamlbuild -libs unix,bigarray dir_tree.native

unix_impl.native: unix_impl.ml fs_spec.ml fs_prelude.ml
	ocamlbuild -libs unix,bigarray $@


################################################################################
# ml targets

$(SRC)/fs_prelude.toplevel.ml: $(SRC)/fs_prelude.ml
	-chmod u+w $@
	echo "module Fs_prelude = struct " >$@
	cat $< >>$@
	echo " end" >> $@
	echo ";;" >> $@
	chmod u-w $@

$(SRC)/fs_prelude.ml: fs_spec.mng
	-chmod u+w $@
	$(MARK) $(MLTARGET) -tag @fs_prelude.ml @fs_prelude.md -in fs_spec.mng >$@
	chmod u-w $@


$(SRC)/fs_spec.toplevel.ml: $(SRC)/fs_spec.ml
	-chmod u+w $@
	echo "module Fs_spec = struct " >$@
	cat $< >>$@
	echo " end" >> $@
	echo ";;" >> $@
	chmod u-w $@

$(SRC)/fs_spec.ml: fs_spec.mng
	-chmod u+w $@
	$(MARK) $(MLTARGET) -tag @fs_spec.ml @fs_spec.md @dep.md -in fs_spec.mng >$@
	chmod u-w $@

$(SRC)/dir_heap.toplevel.ml: $(SRC)/dir_heap.ml
	-chmod u+w $@
	echo "module Dir_heap = struct " >$@
	cat $< >>$@
	echo " end" >> $@
	echo ";;" >> $@
	chmod u-w $@

$(SRC)/dir_heap.ml: dir_heap.mng
	-chmod u+w $@
	$(MARK) $(MLTARGET) -tag @dir_heap.ml @dir_heap.md -in dir_heap.mng >$@
	chmod u-w $@


$(SRC)/dir_tree.toplevel.ml: $(SRC)/dir_tree.ml
	-chmod u+w $@
	echo "module Dir_tree = struct " >$@
	cat $< >>$@
	echo " end" >> $@
	echo ";;" >> $@
	chmod u-w $@

$(SRC)/dir_tree.ml: dir_tree.mng
	-chmod u+w $@
	$(MARK) $(MLTARGET) -tag @dir_tree.ml @dir_tree.md -in dir_tree.mng >$@
	chmod u-w $@

$(SRC)/unix_impl.toplevel.ml: $(SRC)/unix_impl.ml
	-chmod u+w $@
	echo "module Unix_impl = struct " >$@
	cat $< >>$@
	echo " end" >> $@
	echo ";;" >> $@
	chmod u-w $@

$(SRC)/unix_impl.ml: unix_impl.mng
	-chmod u+w $@
	$(MARK) $(MLTARGET) -tag @unix_impl.ml @unix_impl.md -in unix_impl.mng >$@
	chmod u-w $@


$(SRC)/fs_spec_extras.ml: fs_spec.mng
	-chmod u+w $@
	$(MARK) -tag @fs_spec_extras.ml -in fs_spec.mng >$@
	chmod u-w $@

$(SRC)/fs_spec_extras.toplevel.ml: $(SRC)/fs_spec_extras.ml
	-chmod u+w $@
	echo "module Fs_spec_extras = struct " >$@
	cat $< >>$@
	echo " end" >> $@
	echo ";;" >> $@
	chmod u-w $@

################################################################################
# doc targets

$(DOC)/fs_spec.md: fs_spec.mng
	$(MARK) $(HTMLTARGET) -tag @fs_spec.ml @fs_spec.md @dep.md -in fs_spec.mng >$@

$(DOC)/dir_heap.md: dir_heap.mng
	$(MARK) $(HTMLTARGET) -tag @dir_heap.ml @dir_heap.md -in dir_heap.mng >$@

$(DOC)/dir_tree.md: dir_tree.mng
	$(MARK) $(HTMLTARGET) -tag @dir_tree.ml @dir_tree.md -in dir_tree.mng >$@

$(DOC)/unix_impl.md: unix_impl.mng
	$(MARK) $(HTMLTARGET) -tag @unix_impl.ml @unix_impl.md -in unix_impl.mng >$@


$(DOC)/%.html: $(DOC)/%.md
	$(PANDOC) -s $< >$@


################################################################################
#clean: FORCE
#	rm -f $(SRC)/core1.ml $(SRC)/corenotermnonterm.ml $(SRC)/main.ml $(SRC)/main_gen.ml 

clean: FORCE
	ocamlbuild -clean

#	rm -f $(SRC)/fs_spec.ml $(SRC)/fs_spec.toplevel.ml
#	rm -f $(DOC)/fs_spec.md $(DOC)/fs_spec.html

# deletes generated .ml files
realclean: clean
	rm -f $(SRC)/{dir_heap,dir_tree,unix_impl,fs_prelude,fs_spec,fs_spec_extras}.{ml,toplevel.ml}

FORCE:

#.PRECIOUS: $(SRC)/%.md
