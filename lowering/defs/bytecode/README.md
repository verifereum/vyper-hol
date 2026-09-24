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
- `python-o1-bytecode-fixtures` reproduces it and optionally runs the HOL parity
  theorems.

The generated provenance records the pinned Python compiler, its dependencies,
the Vyper fixture source hashes, compilation settings, and output hashes. It
does not hash HOL scripts: they are not Python compiler inputs, and their
bytecode parity is checked separately by the HOL theorems.

For a public summary of what the fixtures test and what remains unverified,
see [`docs/bytecode-fixture-coverage.md`](../../../docs/bytecode-fixture-coverage.md).

The oracle is generated with the exact revision in `../../../VYPER_PIN`, Python
3.11.11, Prague, experimental codegen, `OptimizationLevel.NONE` (which uses the
same `PASSES_O1` Venom passes at this revision), no final assembly optimization,
and no bytecode metadata. The generator requires a clean Vyper checkout, clones
only committed objects, and installs them in an isolated environment using
`python-o1-oracle-constraints.txt`.

Reproduce the committed oracle:

```sh
lowering/defs/bytecode/python-o1-bytecode-fixtures --check \
  --vyper-repo /path/to/vyper
```

Regenerate it only from that verified compiler:

```sh
lowering/defs/bytecode/python-o1-bytecode-fixtures --update \
  --vyper-repo /path/to/vyper
```

## HOL comparison

`eval/evalCompilerBytecodeLib.sml` reads the independent oracle directly. The
parity theories under `eval/` evaluate

```sml
compile_vyper (K SOME) (o1_policy prague_capabilities) <program>
```

and requires exact deployment and runtime byte equality. The expensive fixture
evaluation is opt-in and does not raise the normal project's 2.5-second tactic
timeout:

```sh
lowering/defs/bytecode/python-o1-bytecode-fixtures --compare-hol \
  --vyper-repo /path/to/vyper
```

All 101 retained fixtures have an exact checked theorem; together they check 202
byte lists (deployment and runtime). Any byte difference or checked-compiler
`NONE` result fails. No HOL-generated expected output or implementation-derived
fallback is used. The current cached comparison and parity-theory build logs
contain no `Saved CHEAT` tags. This is finite fixture evidence, not a universal
compiler-equivalence theorem or a claim about unrelated existing proof debt.

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
