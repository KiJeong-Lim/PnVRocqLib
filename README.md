# PnVRocqLib

A Coq library written by members of PnV Discord Server

## Quick Start

```
git clone https://github.com/PnVDiscord/PnVRocqLib.git
eval `opam env`
coq_makefile -f _CoqProject -o Makefile
make -j4 -k
```

## `coqc -v`

```
The Coq Proof Assistant, version 8.18.0
```

## Contents

### Data

- `Aczel.v` : Aczel's Type Theoretic Interpretation of Set Theory

### Prelude

- `Notations.v` : Reserves all notations to avoid the conflict.

- `SfLib.v` : The copy of `snu-sf/sflib.v`. See `References`.

- `Prelude.v` : The prelude code.

### Index

- `Index.v` : Accumulates all source files and check their consistency.

## References

1. [sflib](https://github.com/snu-sf/sflib)
