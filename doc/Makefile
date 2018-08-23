FILES:=ornaments/prelude.lagda ornaments/fam.lagda ornaments/pow.lagda \
	ornaments/iir.lagda ornaments/orn.lagda ornaments/induction.lagda \
	ornaments/graph.lagda ornaments.lagda

OUT:=$(patsubst %.lagda,latex/%.tex,$(FILES))

all: latex/ornaments.pdf

latex/ornaments.pdf: latex/agda.sty latex/agda.fmt latex/ornaments.bib $(OUT)
	cd latex; latexmk -pdf -xelatex -use-make ornaments.tex

latex/agda.sty latex/agda.fmt latex/ornaments.fmt latex/ornaments.bib: latex/%: %
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.tex: latex/%.hide.lagda latex/agda.fmt latex/ornaments.fmt
	lhs2TeX --agda --poly $< > $@

latex/%.hide.lagda: %.lagda hide
	@mkdir -p $(dir $@)
	./hide < $< > $@

hide: Hide.hs
	stack ghc -- --make -dynamic -o hide Hide

clean:
	rm -rf latex
	rm -rf agda
	rm hide Hide.hi Hide.o

#############
#AGDA_OUT:=$(patsubst %.lagda,agda/%.tex,$(FILES))

#agda/ornaments.pdf: agda/agda.sty $(AGDA_OUT)
#	cd agda; latexmk -pdf -use-make -xelatex ornaments.tex

#agda/%.tex: %.lagda
#	@mkdir -p $(dir $@)
#	agda -i . --latex --latex-dir=agda $<

#agda/agda.sty: agda_agda.sty
#	@mkdir -p $(dir $@)
#	cp $< $@
