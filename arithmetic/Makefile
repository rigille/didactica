.PHONY: c coq all c_clean coq_clean clean

# Target to run make in both folders
all: c coq

# Target to run make in folder1
c:
	$(MAKE) -C c

# Target to run make in folder2
coq:
	$(MAKE) -C coq

# Target to run make in folder1
c_clean:
	$(MAKE) -C c clean

# Target to run make in folder2
coq_clean:
	$(MAKE) -C coq clean

clean: c_clean coq_clean
