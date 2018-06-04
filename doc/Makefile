FILES:=ornaments.lagda ornaments/prelude.lagda ornaments/fam.lagda ornaments/iir.lagda
OUT:=$(patsubst %.lagda,latex/%.tex,$(FILES))
AGDA_OUT:=$(patsubst %.lagda,agda/%.tex,$(FILES))

all: latex/ornaments.pdf

latex/ornaments.pdf: latex/agda.sty latex/agda.fmt $(OUT)
	cd latex; latexmk -pdf -xelatex -use-make ornaments.tex

latex/agda.sty latex/agda.fmt: agda.sty agda.fmt
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.tex: latex/%.hide.lagda latex/agda.fmt
	lhs2TeX --agda --poly $< > $@

latex/%.hide.lagda: %.lagda hide
	@mkdir -p $(dir $@)
	./hide < $< > $@

hide: Hide.hs
	ghc --make -dynamic -o hide Hide

agda/%.tex: %.lagda
	@mkdir -p $(dir $@)
	agda -i . --latex --latex-dir=agda $<

agda/agda.sty: agda_agda.sty
	@mkdir -p $(dir $@)
	cp $< $@

agda/ornaments.pdf: agda/agda.sty $(AGDA_OUT)
	cd agda; latexmk -pdf -use-make -xelatex ornaments.tex


clean:
	rm -rf latex
	rm -rf agda
	rm hide Hide.hi Hide.o
