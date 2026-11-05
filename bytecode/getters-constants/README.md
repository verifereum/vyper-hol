# Getters and module constants

This corpus checks public-getter classification and declaration-order constant
substitution against independently generated Vyper bytecode. It retains nineteen
source fixtures: twelve getter/constant/immutable witnesses, five nested or
transient getter witnesses, one SHA256 initializer witness, and one
nonreentrancy witness awaiting #564.

## Checks

Run the two focused theories:

```sh
holbuild -j4 build evalCompilerGettersConstantsRegressionTheory evalCompilerGettersConstantsParityTheory
```

`evalCompilerGettersConstantsParityTheory` checks both deployment and runtime
frontend acceptance, evaluates the HOL compiler, and proves equality with the
independent deployment/runtime bytes for all eighteen entries in
`parity-fixtures.txt`. The expected bytes come from pinned Python Vyper, never
from HOL. A differing result or `NONE` leaves the equality unproved.

The checked fixtures include public scalars, dynamic arrays, maps, explicit
functions and fallback dispatch, string/address/bytes32/decimal/array constants,
a public constant getter, and an immutable-address getter. The five additional
storage fixtures exercise nested maps, map-to-array values, transient maps,
two-dimensional arrays and map-to-dynamic-array values. They rely on the storage
lowering added by #558; no extra Public-only type exclusions are imposed.

The SHA256 initializer witness checks that a compile-time hash becomes a literal
without adding a runtime precompile call. It reproduces the constant replay and
bytecode discrepancy encountered during validation.

`evalCompilerGettersConstantsRegressionTheory` separately checks source syntax:
explicit entries precede getters, getter ordering and nonreentrancy flags survive,
and constants expand through defaults and bodies of every function category.
These syntax computations alone establish neither bytecode parity nor a general
compiler-correctness theorem. In particular, existing subscript simulation
admissions are outside these concrete bytecode checks.

## Pending nonreentrancy fixture

`g37_pub_nonreentrancy_pragma` remains in `sources/`, `all-fixtures.txt` and the
independent oracle receipt. It is deliberately absent from `parity-fixtures.txt`
until #564 supplies the global transient-lock behavior. Its getter retains the
nonreentrancy flag, but the current complete-unit lowering selects storage locks:
the HOL runtime has 148 bytes, compared with Python's 147, with the first byte
difference at offset 71. The lock operations are `SLOAD(0) == 2` versus
`TLOAD(0) == 1`. Python's output is stable across hash seeds 0 through 7.

No passing parity theorem is claimed for this fixture. Add its assertion and
manifest entry when the prerequisite lands; do not change the independent
expected bytes to encode the current discrepancy.

## Oracle generation

`all-fixtures.txt` lists every source, including the pending witness. The retained
`oracle/` files contain annotated AST/layout, deployment/runtime hex and a SHA256
provenance receipt generated with Vyper at `VYPER_PIN`, Python 3.11.11 and hash
seed 0. The generator verifies the imported commit, Python version, installation
root, Prague support, and agreement of the NONE/O1 Venom pipelines. NONE disables
the final assembly optimizer and matches the HOL identity finalizer.

Use an isolated installation of the pinned Vyper and its actual environment
versions. From the repository root:

```sh
CORPUS=bytecode/getters-constants
export PINNED_PYTHON=/path/to/pinned/environment/bin/python
export PINNED_INSTALL_ROOT=/path/to/pinned/installation
export EXPECTED_PYTHON=3.11.11
export GENERATOR_UV=your.actual.uv.version
PYTHONHASHSEED=0 "$PINNED_PYTHON" bytecode/python_o1_bytecode_oracle.py \
  --expected-commit "$(cat VYPER_PIN)" \
  --expected-python "$EXPECTED_PYTHON" --generator-uv "$GENERATOR_UV" \
  --expected-install-root "$PINNED_INSTALL_ROOT" \
  --sources "$CORPUS/sources" --fixture-manifest "$CORPUS/all-fixtures.txt" \
  --frontend --output "$CORPUS/oracle"
```

The sources path must be relative so exported JSON contains no machine paths.
Review the generated receipt and source/output hashes, then build the two
focused theories. Do not alter JSON after generation without regenerating its
receipt. This corpus does not replace the larger residual matrix in #565 or
claim that unrelated prerequisite defects have been repaired.
