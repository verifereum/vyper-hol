# Creation builtin witnesses

This corpus contains the 23 witnesses from `.agent-files/TASK.md`: all four
creation builtins, salted forms, constructor arguments, storage bytecode,
the forwarder alias, nested creation, and the raw-argument domain boundary.

The independent `oracle/` files were generated with pinned Vyper
`0.5.0a4+commit.cd74ce4f`, Prague, experimental codegen, optimization `NONE`,
and no bytecode metadata. `provenance.json` records source and output hashes.

With the pinned Vyper environment on `PATH`, regenerate and compare the inputs:

```sh
python lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus create-builtins --fixtures /tmp/create-oracle --check
```

Run the checked frontend and HOL compiler comparison from the repository root:

```sh
holbuild compileVyperTheory supportedProgramTheory vyperCheckContractFrontendLib
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --corpus create-builtins \
  --fixtures lowering/defs/bytecode/create-builtins/oracle \
  --output /tmp/create-hol
```

The task identifies separate prerequisites for dynamic scratch allocation
(#552), salted raw-create checker evaluation (#542), nested raw calls (#554),
and bytecode/raw-argument domain rules (#571). Keep their diagnostic verdicts
separate from unconditional creation-lowering failures.

Observed comparison results on 2026-10-25, after matching Vyper's
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

Every witness is accepted by the checked frontend and produces `SOME` bytecode.
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

## Constructor alias diagnostic

`tests/create/constructor-alias/sources/ctor_alias.vy` is an additional
diagnostic, outside the 23 required witnesses. Pinned Vyper accepts it. It
lowers the earlier local `xs` argument as a location, evaluates `xs.pop()`,
then copies the shortened `xs` into the constructor tuple. Both the updated
source evaluator and pinned CREATE now request 129 initcode bytes.

`holbuild vyperCtorAliasTestTheory` checks this with actual CREATE stack and
memory execution for both the pinned runtime and the separately checked HOL
runtime. The test requires the two runtimes to be distinct, so this diagnostic
is not counted as a parity witness. The separate
`vyperCtorStorageAliasTestTheory` checks that a storage array is read after
`pop` changes its length. Late reads cover local and top-level Names; other
located expression forms still need their source/callback bridge for the
general theorem.
