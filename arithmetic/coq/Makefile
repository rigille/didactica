COQMFFLAGS := -Q . Didactica

ALLVFILES := Main.v Add.v sublist.v number.v arithmetic.v Verif_compare.v Verif_number_add_inner.v Verif_add_with_carry.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
