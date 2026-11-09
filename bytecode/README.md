# O1 bytecode parity fixtures

This directory contains the independent Python oracle for the frozen 101-fixture
HOL-supported-subset corpus (12 of them not parity-checked; see [`pending-5127-port.md`](pending-5127-port.md)). It includes the original 23-fixture milestone and
78 subset/interaction fixtures.

- `python-o1-no-asm-opt-sources/` contains Vyper source counterparts to the HOL
  programs in `eval/evalCompilerScript.sml` and the `eval/evalCompilerSubset*`
  theories.
- `python-o1-no-asm-opt/` contains the pinned Python Vyper deployment/runtime
  bytecode and its provenance record.
- `python_o1_bytecode_oracle.py` generates the oracle.
- `python-o1-bytecode-fixtures` reproduces it.

The generated provenance records the pinned Python compiler, its dependencies,
the Vyper fixture source hashes, compilation settings, and output hashes. It
does not hash HOL scripts: they are not Python compiler inputs, and their
bytecode parity is checked separately by the native runner.

For a public summary of what the fixtures test and what remains unverified,
see [`docs/bytecode-fixture-coverage.md`](../docs/bytecode-fixture-coverage.md).

The oracle is generated with the exact revision in `../VYPER_PIN`, Python
3.11.11, `evm_version="prague"`, experimental codegen, `OptimizationLevel.NONE` (which uses the
same `PASSES_O1` Venom passes at this revision), no final assembly optimization,
and no bytecode metadata. The generator requires a clean Vyper checkout, clones
only committed objects, and installs them in an isolated environment using
`python-o1-oracle-constraints.txt`.

Before installing, the generator applies `patches/*.patch` to the pinned
revision in C-locale filename order, using `git apply` for each file. A failed
patch stops generation; an empty series leaves the pin unchanged. Each file
backports one upstream PR so independent fixes can be added separately and
removed when a new pin includes them. The current series contains:

- vyperlang/vyper#5127: an external call sends the selector and the encoded
  arguments, `4 + encoded length` bytes, rather than `4 + ` the argument
  tuple's ABI size bound.
- vyperlang/vyper#5239: a storage, transient or immutable variable is read at
  its own declared type, not at a wider expected type (such as an external
  call's parameter type), whose layout differs for nested bounded types.
- vyperlang/vyper#5254: the inliner binds the unused return-PC parameter
  to zero instead of the removed callee's label.

The provenance's `vyper_commit` names the unpatched base revision.

Name a new patch `<upstream-pr>-<slug>.patch`, and start it with the upstream
PR URL and its merge status (including the merge commit when merged). Keep
only that PR's backport in the file, adapted to apply after earlier filenames.
When migrating a branch with extra hunks in the old `vyper-pin.patch`, move
those hunks into their own PR files and remove the old file; do not duplicate
patches already in the series. Compare the old and new patched compiler trees
at `VYPER_PIN` to check that this migration preserves the oracle inputs.

On a repin, remove patches whose fixes the new pin contains, then check that
the remaining series applies and regenerate the oracles. A PR having merged
upstream does not by itself mean its fix is in `VYPER_PIN`.

HOL's EVM semantics (Verifereum) model Osaka, while the oracle is compiled with
`evm_version="prague"` (`ORACLE_EVM_VERSION`), the newest version the pinned
Vyper accepts. HOL's compile target is fork-neutral (`all_capabilities`: PUSH0,
MCOPY, transient storage and blob opcodes, all available since Cancun). The
compiled code never uses Osaka's only new opcode (CLZ) or its new precompile
(P256VERIFY), and never calls MODEXP, so the emitted bytes mean the same on
Prague and Osaka. The generator fails if the pinned Vyper supports a newer EVM
version, so a pin bump that adds Osaka forces regeneration with it.

Reproduce the committed oracle:

```sh
bytecode/python-o1-bytecode-fixtures --check \
  --vyper-repo /path/to/vyper
```

Regenerate it only from that verified compiler:

```sh
bytecode/python-o1-bytecode-fixtures --update \
  --vyper-repo /path/to/vyper
```

## HOL comparison

The native runner (`native/README.md`) compiles each fixture's program with

```sml
compile_vyper (K SOME) (o1_policy all_capabilities) <program>
```

and requires exact deployment and runtime byte equality with the oracle. A
feature suite's program must also pass the HOL checker in both modes;
membership in the supported programs is not checked. Build it, then run it from this directory:

```sh
holbuild build compilerNativeEmitTheory        # from the repository root
holbuild executable bytecode_parity_native
./native/bytecode_parity_native.exe .          # every suite
./native/bytecode_parity_native.exe . conversions   # one suite
```

CI's `native-parity` job runs it on every suite.

The 101 retained fixtures in `python-o1-no-asm-opt/` and the witnessed fixtures
of each feature suite are covered, except those listed in
[`pending-5127-port.md`](pending-5127-port.md); together they check the deployment and
runtime byte lists of each. The runner is trusted rather than kernel-checked
(see its Trust section). The independent oracle appears only in parity claims.
Any byte difference or checked-compiler `NONE` result fails. No HOL-generated
expected output or implementation-derived fallback is used. This is finite
fixture evidence, not a universal compiler-equivalence theorem.

## Supported-subset boundary

The machine-readable authority is
`.agent-files/tasks/evidence/TASK_089.ledger.json`, derived from the ten declared
HOL source files. It contains 1,485 rows: 506 supported, 795 partial (with
explicit supported/unsupported boundaries), and 184 unsupported. All 101
retained fixtures enter through checked `compile_vyper`. The strict
per-fixture input-term audit confirms 148 of 187 variant AST constructor
kinds present, 39 absent, and no `raw_call_flags` record. The corrected
ledger assigns each present AST constructor only to fixtures containing it;
22 lowering-arm rows have separate source-justified checked-path witnesses.
The remaining 1,107 code-producing lowering-arm rows have **no witness
claim**; an empty list does not prove non-execution. Six rows
(constructors and multiplier arms for `MEther`, `GEther`, `TEther`) are
explicitly outside the differential target because pinned Python rejects
those denominations. Their HOL definitions remain unchanged. See the linked
coverage document for the complete constructor census and precise distinction
between fixture inputs and lowering-arm execution.

## External-entry regressions

The external-entry regression corpus in `external-entries/` retains its source,
sanitized AST and exact bytecode oracle. With the pinned Vyper installed, check
these artifacts with:

```sh
python external-entries/generate.py --check
```

Run this command from this directory. To inspect a fixture's runtime IR:

```sh
vyper --experimental-codegen --optimize none --evm-version prague \
  -f ir_runtime external-entries/sources/dflt_one_lit.vy
```

`nr_internal_return` follows the DFT abort-ordering fix in
[vyperlang/vyper#5336](https://github.com/vyperlang/vyper/pull/5336), which the
pinned oracle predates. Its kernel check proves exact bytes from pinned Python
with that fix, compilation success, and inequality to the retained `.hex`
oracle for unpatched pinned Python.

## Fixture format

Each `.hex` file contains canonical lowercase, even-length hexadecimal:

```text
deploy=<hex bytes>
runtime=<hex bytes>
```

There is no `0x` prefix. Blank lines and `#` comments are accepted by the HOL
fixture reader.

## Event regressions (issue 570)

The seven additional event sources live in `python-event-no-asm-opt-sources/`,
with their own manifest `event-fixtures.txt`. They leave the frozen 101-fixture
corpus above unchanged. `python-event-no-asm-opt/` contains independently
generated deployment/runtime bytes and provenance; the corresponding sanitized
annotated AST and layout inputs live in `tests/fixtures/check_contract/events/`.
Three checker-only inputs, listed in `event-checker-fixtures.txt`, reproduce
e62, m14 and m49 with their real imports; `libp.vy` is m14's imported module.
They cover indexed bytes20 (argument and storage), the four recursive
argument-widening cases in issue 570, and a nested struct declared before its
member type.

With an isolated installation of VYPER_PIN using Python 3.11.11 and the exact
dependencies from `python-o1-oracle-constraints.txt`, reproduce these artifacts:

```sh
python3 bytecode/event_bytecode_oracle.py \
  --python /path/to/isolated/venv/bin/python --vyper-repo /path/to/clean/vyper
```

Add `--update` to regenerate them. The generator verifies the clean checkout,
installed compiler commit, Python version, dependency versions and import root.
It records source, bytecode, sanitized JSON and generator hashes. It does not
install packages or invoke uv. It uses the same Prague/NONE/experimental/no
metadata settings as the frozen oracle, and invokes the existing sanitizer.
Installed compiler Python sources and builtin interfaces are compared with the
clean checkout; provenance records the verified source count and tree hash.

`vyperEventRegressionTheory` covers checker mutations, source-topic
semantics, and the accepted event corpus.
`vyperImportedEventRegressionTheory` checks the single-module rejection of the
three imported-event inputs after real frontend translation, in both modes.
`vyperEventArgumentLifetimeTheory` checks a log whose first argument is a
dynamic array and whose second argument pops that array. It certifies both
checker modes and execution of the emitted argument code: the earlier value
remains `[1, 2]`, the pop returns `2`, and the local array becomes `[1]`.
Lowering saves aggregate arguments before a later potentially effectful
argument; pure suffixes and word arguments need no snapshot.
`vyperEventForwardStructTheory` certifies both checker modes and actual LOG
execution for the forward-declared nested struct, including its 32-byte value.

No HOL check currently compares the event fixtures' bytes with this oracle:
the native runner covers only the main corpus.

`eventEncodingPropsTheory` proves complete encoding invariance under checked
argument widening, with the declared signature hash. `eventTopicPropsTheory`
relates typed word operands to source topics and proves that primitive topic
lowering preserves the compiler state.
`eventTopicExecPropsTheory` proves execution of bytes/string topic hashing from
the length-prefixed memory representation, with explicit 256-bit address and
length bounds. It preserves existing operands and all state fields except the
new SSA variable bindings. Its saved theorems are checked for admission tags.

Tuple widening uses a bulk memory copy only when `memoryLayoutDefsTheory`'s
structural layout keys agree. That theory proves equal total footprints and
equal field offsets; arrays retain their element stride and bound in the key.
Other differing aggregate layouts use the typed copy path.

The fixed-array widening fixture also exercises duplication below EVM's DUP16
range. The stack planner spills the inaccessible prefix, uses DUP16, and
restores the prefix around the duplicated value. `deepDupChecksTheory` checks
the generated physical assembly at depths 16, 17, 31 and 32, covering both
restoration schedules and preserving the memory below the spill region.
`deepDupRestoreTheory` proves the interleaved restore/SWAP1 schedule for an
arbitrary number of restores, including repeated values, with exact stack,
memory expansion and instruction-count results in the assembly semantics.
`doDupModelTheory` relates the interleaved logical restore sequence to ordinary
restoration below a saved top operand, and proves that duplication preserves
the logical spill map and absence of fresh operands. These are alignment
lemmas; the full instruction-simulation proof remains a separate obligation.
