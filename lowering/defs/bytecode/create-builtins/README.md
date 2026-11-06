# Creation builtin witnesses

This corpus contains the 23 witnesses from `.agent-files/TASK.md`: all four
creation builtins, salted forms, constructor arguments, storage bytecode,
the forwarder alias, nested creation, and the raw-argument domain boundary.

The independent `oracle/` files were generated with the `VYPER_PIN` Vyper
(`0.5.0b1+commit.577d2534`), Prague, experimental codegen, optimization
`NONE`, and no bytecode metadata. `provenance.json` records source and output
hashes.

The compiler at the pin rejects `dom06_blueprint_rawargs_b32`, so its oracle
files are kept from `0.5.0a4+commit.cd74ce4f`, it is out of
`parity-fixtures.txt`, and `prepare` cannot reproduce this corpus as a whole. Keep that diagnostic and its oracle files when
regenerating the accepted fixtures. The fixtures whose bytecode changed at
the pin through vyperlang/vyper#5127 are out of `parity-fixtures.txt` and
listed in `../pending-5127-port.md`.

With the `VYPER_PIN` compiler on `PATH`, compare an accepted fixture's deploy
and runtime bytecode with its committed `.hex` file, for example:

```sh
vyper --experimental-codegen --evm-version prague -O none \
  --disable-bytecode-metadata -f bytecode,bytecode_runtime \
  lowering/defs/bytecode/create-builtins/sources/cp01_proxy.vy
cat lowering/defs/bytecode/create-builtins/oracle/cp01_proxy.hex
```

The compiler prints deploy then runtime, each with an `0x` prefix; the archive
uses `deploy=` and `runtime=` without that prefix. Repeat for the other
accepted sources, excluding `dom06_blueprint_rawargs_b32`. This compares
bytecode; it does not reproduce the historical environment receipt.

Run the checked frontend and HOL compiler comparison from the repository root:

```sh
holbuild build compileVyperTheory supportedProgramTheory vyperCheckContractFrontendLib
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --corpus create-builtins \
  --fixtures lowering/defs/bytecode/create-builtins/oracle \
  --output /tmp/create-hol
```

The task identifies separate prerequisites for dynamic scratch allocation
(#552), salted raw-create checker evaluation (#542), nested raw calls (#554),
and bytecode/raw-argument domain rules (#571). Keep their diagnostic verdicts
separate from unconditional creation-lowering failures.

The results below predate the `0.5.0b1` oracles: they compare against
`0.5.0a4+commit.cd74ce4f`. Observed comparison results on 2026-10-25, after matching Vyper's
`ADD`/`NOT`/`AND` DALLOCA alignment, pure-addition `BUMP`, the result-branch
FMP restore, and pinned Vyper's dead-output rule for multi-output instructions.
The full 23-witness probe produced these verdicts:

| Witnesses | Verdict | Relevant boundary |
| --- | --- | --- |
| `cp01_proxy`, `cp02_proxy_value_salt`, `cp03_proxy_rof`, `cp04_forwarder_alias` | MATCH | Proxy lowering, including CREATE2 and failure handling |
| `rcr01_rawcreate`, `rcr03_rawcreate_rof`, `rcr04_rawcreate_storage`, `rcr05_rawcreate_args`, `rcr02_rawcreate_args_salt`, `rcr06_rawcreate_salt` | MATCH | Snapshot uses the builtin's promoted `Bytes[49152]` capacity |
| `cc01_copy`, `cc02_copy_salt_value`, `cc03_copy_rof`, `nest02_stmt_create` | MATCH | Scratch restore, DALLOCA operand order, and dead-output stack planning |
| `cb01_blueprint` through `cb07_blueprint_args_salt` | MATCH | Scratch restore and dead-output stack planning |
| `dom06_blueprint_rawargs_b32` | MATCH | 200-byte runtimes agree; the #571 source-domain restriction remains a separate prerequisite |
| `nest01_create_in_call` | PARITY_DEFECT | Outer raw-call lowering (#554) still emits INVALID |

In that historical run, every witness was accepted by the checked frontend
and produced `SOME` bytecode.
Creation remains excluded by `supported_program`, as required until #575.
All 23 rows were compared against the current HOL compiler: 22 MATCH and one
PARITY_DEFECT in the nested `raw_call` dependency (#554).

For `cc01_copy`, pinned Vyper's pre-DFT runtime block contains a restore of
its FMP runner from the allocation pointer immediately before the final
`jnz`. DFT treats that restore as a root and schedules `bump` before the
independent preamble `shl`/`or`; the pinned runtime is 187 bytes. HOL's
conservative `fmp_block_restore` rejects blocks with successors, so the
builtin lowering emits this restore explicitly when failure must revert.
The copy, nested statement, and blueprint witnesses now match. Pinned Vyper
has no result branch in `revert_on_failure=False` forms; the explicit restore
is omitted there. Its stack planner still pops dead outputs from two-output
`BUMP` in a halting block, which closes `cc03` and `cb05`. A general
reclaim-policy experiment made the full compiler evaluation too slow to
validate and was reverted.

The kernel-checked tests `vyperCreateOracleTestTheory` and
`vyperCreateMemoryTestTheory` cover the source oracle's 48 creation/outcome
cases and compare each builtin's source initcode request to the memory slice
passed to CREATE by its compiled runtime. These finite tests do not establish
the general recursive ABI or creation-pipeline correctness theorem.

## Constructor alias checks

`vyperCtorAliasTestTheory` checks the CREATE memory request for
`tests/create/constructor-alias/sources/ctor_alias.vy` against the source
semantics. An earlier local array argument is read after a later `xs.pop()`
shortens it; source and HOL-compiled execution both request 129 initcode
bytes. Pinned Vyper snapshots the earlier argument before the pop, so its
bytecode for this witness is out of parity and listed in
`../pending-5127-port.md`.
`vyperCtorStorageAliasTestTheory` checks the corresponding storage-array case.
