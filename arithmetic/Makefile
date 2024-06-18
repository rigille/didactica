.PHONY: c coq all c_clean coq_clean clean

all: c coq

c:
	$(MAKE) -C c

coq:
	$(MAKE) -C coq

c_clean:
	$(MAKE) -C c clean

coq_clean:
	$(MAKE) -C coq clean

clean: c_clean coq_clean
