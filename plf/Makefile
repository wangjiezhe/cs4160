COQMFFLAGS := -Q . PLF  

ALLVFILES := \
	Maps.v MapsTest.v \
	Imp.v ImpTest.v \
	Equiv.v EquivTest.v \
	Hoare.v HoareTest.v \
	Hoare2.v Hoare2Test.v

# HoareAsLogic.v Smallstep.v Types.v Stlc.v StlcProp.v MoreStlc.v Sub.v Typechecking.v Records.v References.v RecordSub.v
# HoareAsLogicTest.v  SmallstepTest.v  TypesTest.v  StlcTest.v  StlcPropTest.v  MoreStlcTest.v  SubTest.v  TypecheckingTest.v  RecordsTest.v  ReferencesTest.v  RecordSubTest.v

# Norm.v PE.v
# NormTest.v  PETest.v

# LibTactics.v UseTactics.v UseAuto.v
# LibTacticsTest.v  UseTacticsTest.v  UseAutoTest.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
