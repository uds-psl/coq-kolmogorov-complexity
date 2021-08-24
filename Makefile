deps:
	+make -C external/synthetic-reducibility-coq all

all:
	+make -C kolmogorov all

clean:
	+make -C kolmogorov clean

realclean:
	+make -C external/synthetic-reducibility-coq clean
	+make -C kolmogorov clean

.PHONY: all clean realclean
