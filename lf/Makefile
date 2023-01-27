COQMFFLAGS := -Q . LF

ALLVFILES := \
	Basics.v BasicsTest.v \
	Induction.v InductionTest.v \
	Lists.v ListsTest.v \
	Poly.v PolyTest.v \
	Tactics.v TacticsTest.v

# Logic.v IndProp.v Maps.v ProofObjects.v IndPrinciples.v Rel.v Imp.v ImpParser.v ImpCEvalFun.v Extraction.v Auto.v AltAuto.v Postscript.v Bib.v
# LogicTest.v  IndPropTest.v  MapsTest.v  ProofObjectsTest.v  IndPrinciplesTest.v  RelTest.v  ImpTest.v  ImpParserTest.v  ImpCEvalFunTest.v  ExtractionTest.v  AutoTest.v  AltAutoTest.v  PostscriptTest.v  BibTest.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
