COQPROJECT = _CoqProject
MAKEFILE_COQ = Makefile.coq

$(MAKEFILE_COQ): $(COQPROJECT)
	coq_makefile -f $(COQPROJECT) -o $(MAKEFILE_COQ)

all: $(MAKEFILE_COQ)
	$(MAKE) -f $(MAKEFILE_COQ) all

clean:
	@if [ -f $(MAKEFILE_COQ) ]; then \
	  $(MAKE) -f $(MAKEFILE_COQ) clean; \
	  rm -f $(MAKEFILE_COQ); \
	fi

.PHONY: all clean
