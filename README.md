# NTP4VC

## Benchmarks

The list of test set:
- `test_set.isabelle.lst`
- `test_set.lean.txt.lst`
- `test_set.lean.txt.lst`

All the cases are placed under
- `./data/why3/pearl` for the pearls of algorithms and data structures (from Why3's official example gallery)
- `./data/why3/frama_c` for VCs from real C verification projects.

For every Why3 `.mlw` file, (e.g., `./data/why3/pearl/add_list.mlw`), a `_vcg` folder (e.g., `./data/why3/pearl/add_list_vcg`) is placed under the same directory, which stores the VCs for each prover (e.g., `./data/why3/pearl/add_list_vcg/isabelle` for Isabelle VCs).

Additional to the above two folders, translations of Why3 system library are also required by these cases. These translations are placed under `./generation/<LANG>`.

In some languages (Lean, Rocq), a single VC is split into multiple statements due to the technique limitation. All statements placed in a single file are a single VC. This VC passes the test only when all the statements pass.

### Setup

All the benchmark cases are configured and organized into packages using the package manager of the corresponding provers. Some setup are required to register the packages into your system.

- for Isabelle, we use the standard session management. You should run the following command to register the pakcages into the system.
```
cd NTP4Verif
isabelle components -u.
```
- for Rocq, we use `dune` to manage packages. Nothing needs to configure but you should use `dune build` to build a `.v` file, e.g.,
```
dune build ./data/why3/pearl/add_list_vcg/rocq/add_list_AddListImp_mainqtvc.vo
```
- for Lean4, we use `lake` for such management. Nothing needs to configure but you should run `lake build` to build a `.lean` file, e.g.,
```
cd data/why3
lake build ./pearl/add_list_vcg/lean/add_list_AddListImp_mainqtvc.lean
```

Because the files can have complicated dependencies, running with a pakcage manager is highly recommended.

## VC Extraction

### Setup

#### Setup the modified Why3

```
cd why3-for-NTP
opam init
opam switch create default ocaml
eval $(opam env --switch=default)
opam install menhir zarith
./configure --prefix $(realpath ../why3)
make -j
make install
```

### Run the Extractor

#### Extracting Why3 VCs from ACSL, by Frama-C

You must use Frama-C 18.0 (a rather old version).

The commands used to extract VCs in this benchmark are different per Frama-C project. The exact extraction command is given in the `src/extraction.sh`, e.g., `data/why3/frama_c/contiki_memb/src/extraction.sh` (after you unzip `data/why3/frama_c/contiki_memb/src.tar.zst`). Nonetheless, most of the commands are based on the following one:
```
frama-c -wp -wp-rte -wp-no-warn-memory-model -wp-gen -wp-out wp_out -wp-prover why3 <the-target-C-file>
```

#### Translating Why3 VCs into Lean4/Rocq/Isabelle VCs

```
source envir.sh

# to extract pearl dataset for Lean4
./VCG.py lean data/why3/pearl --cache ./.lean.cache
# to extractpip install frama-c dataset for Lean4
./VCG.py lean data/why3/frama_c --cache ./.lean.cache -L ./lib/frama-c


# to extract pearl dataset for Rocq
./VCG.py rocq data/why3/pearl --cache ./.lean.cache
# to extract frama-c dataset for Rocq
./VCG.py rocq data/why3/frama_c --cache ./.lean.cache -L ./lib/frama-c

# to extract pearl dataset for Isabelle
ISA_REPL_ADDR=<IP-address-of-IsaREPL> ./VCG.py isabelle data/why3/pearl --cache ./.lean.cache
# to extract frama-c dataset for Isabelle
ISA_REPL_ADDR=<IP-address-of-IsaREPL> ./VCG.py isabelle data/why3/frama_c --cache ./.lean.cache -L ./lib/frama-c
```

### Run the Why3 Baseline Measurement

```
source envir.sh
./tools/why3_auto_3.py data/why3/pearl
# For frama-c cases, you must set the WHY3_LOAD=./lib/frama-c/ environment variable.
WHY3_LOAD=./lib/frama-c/ ./tools/why3_auto_3.py data/why3/frama_c/contiki_list
```


