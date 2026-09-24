# O1 bytecode parity fixtures

This directory contains the independent Python oracle for the frozen 101-fixture
HOL-supported-subset corpus. It includes the original 23-fixture milestone and
78 retained subset/interaction fixtures. The resource-prohibitive `spill_join`
stress case is retired and is not part of the corpus.

- `python-o1-no-asm-opt-sources/` contains Vyper source counterparts to the HOL
  programs in `eval/evalCompilerScript.sml` and the `eval/evalCompilerSubset*`
  theories.
- `python-o1-no-asm-opt/` contains the pinned Python Vyper deployment/runtime
  bytecode and its provenance record.
- `python_o1_bytecode_oracle.py` generates the oracle.
- `python-o1-bytecode-fixtures` reproduces it and optionally runs the HOL parity
  theorems.

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
fallback is used. Existing upstream admitted dependencies can tag these concrete
comparison theorems `CHEAT`; matching byte evaluations are not yet a cheat-free
proof acceptance.

## Supported-subset boundary

The machine-readable authority is
`.agent-files/tasks/evidence/TASK_089.ledger.json`, derived from the ten declared
HOL source files. At the accepted revision it contains 1,485 rows: 506 supported,
795 partial (with explicit supported/unsupported boundaries), and 184
unsupported. All 1,301 code-producing rows have a retained fixture witness and
all 101 fixtures enter through checked `compile_vyper`. Unsupported domains are
not promoted merely to enlarge the fixture corpus.

## Fixture format

Each `.hex` file contains canonical lowercase, even-length hexadecimal:

```text
deploy=<hex bytes>
runtime=<hex bytes>
```

There is no `0x` prefix. Blank lines and `#` comments are accepted by the HOL
fixture reader.
