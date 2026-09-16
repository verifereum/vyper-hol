# O1 bytecode parity fixtures

This directory contains the independent Python oracle for the 23 checked HOL
compiler fixtures.

- `python-o1-no-asm-opt-sources/` contains Vyper source counterparts to the HOL
  programs in `../evalCompilerScript.sml`.
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

`evalCompilerBytecodeLib.sml` reads the independent oracle directly. Every
fixture theorem in `evalCompilerBytecodeScript.sml` evaluates

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

Any byte difference or checked-compiler `NONE` result fails. No HOL-generated
expected output or implementation-derived fallback is used.

## Fixture format

Each `.hex` file contains canonical lowercase, even-length hexadecimal:

```text
deploy=<hex bytes>
runtime=<hex bytes>
```

There is no `0x` prefix. Blank lines and `#` comments are accepted by the HOL
fixture reader.
