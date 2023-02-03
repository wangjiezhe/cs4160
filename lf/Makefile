COQMFFLAGS := -Q . LF

ALLVFILES := \
	Basics.v BasicsTest.v \
	Induction.v InductionTest.v \
	Lists.v ListsTest.v \
	Poly.v PolyTest.v \
	Tactics.v TacticsTest.v \
	Logic.v LogicTest.v \
	IndProp.v IndPropTest.v \
	ProofObjects.v ProofObjectsTest.v \
	Rel.v RelTest.v \
	Maps.v MapsTest.v \
	Imp.v ImpTest.v

# IndPrinciples.v ImpParser.v ImpCEvalFun.v Extraction.v Auto.v AltAuto.v
# IndPrinciplesTest.v ImpParserTest.v ImpCEvalFunTest.v ExtractionTest.v AutoTest.v AltAutoTest.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
