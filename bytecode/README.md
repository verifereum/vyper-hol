# O1 bytecode parity fixtures

This directory contains the independent Python oracle for the frozen 101-fixture
HOL-supported-subset corpus. It includes the original 23-fixture milestone and
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
- vyperlang/vyper#5332: constructor immutable bytestring stores copy the
  length word and live data words, rather than the declared capacity.
- vyperlang/vyper#5338: widening bytestring conversions allocate enough
  memory for the result type.

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
of each feature suite are covered; together they check the deployment and
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

## Fixture format

Each `.hex` file contains canonical lowercase, even-length hexadecimal:

```text
deploy=<hex bytes>
runtime=<hex bytes>
```

There is no `0x` prefix. Blank lines and `#` comments are accepted by the HOL
fixture reader.
