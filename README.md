# A Formalization of Kolmogorov Complexity in Synthetic Computability Theory

This repository contains the Coq source files to the Bachelor's thesis of Nils Lauermann.

Website: https://www.ps.uni-saarland.de/~lauermann/bachelor.php

CoqDoc: https://uds-psl.github.io/coq-kolmogorov-complexity/website/toc.html

The files in the folder `kolmogorov` are the results of this thesis.

## How to compile the code

You need `Coq 8.12`, the [`stdpp` library](https://gitlab.mpi-sws.org/iris/stdpp) and the [Equations](https://mattam82.github.io/Coq-Equations/) package

You need to initialize and update the submodule first:

``` sh
git submodule init
git submodule update
```

With `make deps` you can build the external project.

Afterwards, `make all` will build the project.

## Acknowledgments

The `synthetic-reducibility` library is part of an unpublished paper by Yannick Forster, Felix Jahn, and Gert Smolka.

Throughout the files there are occasionally proofs by others.
These proofs are always annotated accordingly.