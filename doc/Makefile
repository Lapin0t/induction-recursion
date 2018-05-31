PAPER=ornaments

FILES:=ornaments/prelude.lagda
HIDDEN:=$(patsubst %.lagda,latex/%.hide.lagda,$(FILES))
FINAL:=$(patsubst %.lagda,latex/%.tex,$(FILES))

all: latex/$(PAPER).pdf

latex/$(PAPER).pdf: latex/$(PAPER).tex latex/agda.sty latex/agda.fmt $(FINAL)
	cd latex; latexmk -pdf -use-make -xelatex $(PAPER).tex

latex/agda.sty latex/agda.fmt: agda.sty agda.fmt
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.tex: latex/%.hide.lagda
	lhs2TeX --agda --poly $< > $@

latex/%.hide.lagda: %.lagda hide
	@mkdir -p $(dir $@)
	./hide < $< > $@

hide: Hide.hs
	ghc --make -dynamic -o hide Hide

clean:
	rm -rf latex
	rm hide Hide.hi Hide.o
