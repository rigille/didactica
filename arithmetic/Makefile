.PHONY: c coq/arithmetic.v coq all c_clean coq_clean clean

all: c coq

c:
	$(MAKE) -C c
coq/arithmetic.v: c/src/arithmetic.c
	clightgen -normalize c/src/arithmetic.c -o coq/arithmetic.v -Xpreprocessor -Wno-cpp

coq: coq/arithmetic.v
	$(MAKE) -C coq

c_clean:
	$(MAKE) -C c clean

coq_clean:
	rm coq/arithmetic.v
	$(MAKE) -C coq clean

clean: c_clean coq_clean
