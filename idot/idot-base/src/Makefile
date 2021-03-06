FILES=Safety.v
OBJECTS=$(FILES:.v=.vo)

DOCDIR=html

COQINCLUDE=-R . DOT
COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq
PROOFMAKEFILECONF=$(PROOFMAKEFILE).conf
PROOFS=$(wildcard *.v)

##############
# Main Rules #
##############

.PHONY: all doc proofs clean cleanall
all: doc

proofs: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) all

clean: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) cleanall

cleanall:: clean
cleanall::
	-rm -f .*.aux
	-rm -f *.vo
	-rm -f *.glob
	-rm -f *.v.d
	-rm -f .coqdeps.d
	-find . -regex ".*\.\(aux\|vo\|vio\|glob\)" | xargs rm -f

doc: $(DOCDIR)/toc.html graph

%.vo: %.v $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) $@

all doc clean: $(PROOFMAKEFILE)

#############
# IDE Setup #
#############

.PHONY: ide
ide: _CoqProject

_CoqProject:
	{ echo $(COQINCLUDE); \
      echo "-arg -w"; \
      echo "-arg all"; \
	  find . -name "*.v"; } > _CoqProject

# We curate the _CoqProject file to have a nice TOC in the documentation
# cleanall::
# 	-rm -f _CoqProject

######################
# Generated Makefile #
######################

$(PROOFMAKEFILE): _CoqProject
	@$(COQMAKEFILE) -f _CoqProject -install none -o $(PROOFMAKEFILE)

cleanall::
	-rm -f $(PROOFMAKEFILE)
	-rm -f $(PROOFMAKEFILECONF)

#################
# Documentation #
#################

EXTRA_DIR:=../doc-assets/assets

.PHONY: $(DOCDIR)/toc.html

$(DOCDIR)/toc.html: $(PROOFMAKEFILE) proofs
	$(MAKE) -f $(PROOFMAKEFILE) html
	cp -r $(EXTRA_DIR) html/assets

$(DOCDIR):
	mkdir -p $@

COQDOCFLAGS:= \
  --no-externals \
  --toc --toc-depth 2 --html \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

##########
# Graphs #
##########

.PHONY: graph.dot graphbox.dot graph

graph.dot: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) graph.dot

graph.png: graph.dot
	dot -Tpng graph.dot -o graph.png

graphbox.dot: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) graphbox.dot

graph: graph.png

######################
# Lemma Dependencies #
######################

DPDMODALL=$(shell coqdep -sort Safety.v | sed "s|\(\./\)||g" | sed "s|\.vo||g")
DPDFILENAME=dpdraw.dpd
DPDDOT=$(DPDFILENAME:=.dot)

DPDEXCLUDE ?= LibExtra SyntaxClasses TransformCollect Vars Terms Types
DPDMODULES=$(filter-out $(DPDEXCLUDE), $(DPDMODALL))

DPDTEXT=Require dpdgraph.dpdgraph.
DPDTEXT+=Require $(DPDMODULES).
DPDTEXT+=Set DependGraph File \"$(DPDFILENAME)\".
DPDTEXT+=Print FileDependGraph $(DPDMODULES).

$(DPDFILENAME): $(shell coqdep -sort $(FILES)) all
	echo $(DPDTEXT) | coqtop

$(DPDDOT): $(DPDFILENAME)
	dpd2dot -without-defs $<
	dpdusage $<

.PHONY: dpdraw $(DPDOT) $(DPDFILENAME)
dpdraw: $(DPDDOT)

DPDFILTER=dpdgraph.dpd
DPDFILDOT=$(DPDFILTER:=.dot)
$(DPDFILDOT): $(DPDFILTER)
	dpd2dot -without-defs $<

$(DPDFILTER): $(DPDFILENAME)
	grep -P '(kind=construct|^N: [0-9]+ "[^"]*(_ind|mutind|_mut)")' $(DPDFILENAME) | sed -e "s|^N: \([0-9][0-9]*\) .*|\1|g" | paste -sd "|" | xargs -I {} grep -P -v "^((E: ({}) )|(E: [0-9]+ ({}) )|(N: ({}) ))" $(DPDFILENAME) > $(DPDFILTER)

.PHONY: dpdgraph $(DPDFILDOT) $(DPDFILTER)
dpdgraph: $(DPDFILDOT)

cleanall::
	-rm -f *.dot
	-rm -f *.dpd
