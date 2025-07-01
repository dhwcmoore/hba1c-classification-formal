COQC ?= coqc
COQDIR = coq
OCAMLDIR = ocaml

COQFILES = $(wildcard $(COQDIR)/*.v)
VOFILES = $(COQFILES:.v=.vo)

all: $(VOFILES)

%.vo: %.v
	$(COQC) -R $(COQDIR) Rocq $<

extract: $(OCAMLDIR)/hba1c_classifier.ml

$(OCAMLDIR)/hba1c_classifier.ml: $(COQDIR)/do_extract.v $(COQDIR)/coq_hba1c.v $(COQDIR)/Rocq/IntervalClassifier.v
	@mkdir -p $(OCAMLDIR)
	$(COQC) -R $(COQDIR) Rocq $(COQDIR)/do_extract.v

clean:
	rm -f $(COQDIR)/*.vo
	rm -f $(OCAMLDIR)/*.ml
