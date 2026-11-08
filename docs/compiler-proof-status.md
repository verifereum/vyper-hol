# Compiler proof status

Latest audit:

- [compiler-proof-status-2026-10-09.md](compiler-proof-status-2026-10-09.md)
  — accepted TASK056 statement/composition audit; S1–S7 admitted,
  environmental producers partial/absent; [TASK060 final exit verified](compiler-proof-milestone-1-exit-2026-10-09.md).

Historical snapshots:

- [compiler-proof-status-2026-09-28.md](compiler-proof-status-2026-09-28.md)

- [archive/compiler-proof-status-2026-06-24.md](archive/compiler-proof-status-2026-06-24.md)
- [archive/compiler-proof-progress-2026-04-07.md](archive/compiler-proof-progress-2026-04-07.md)
- [archive/compiler-proof-progress-2026-04-16.md](archive/compiler-proof-progress-2026-04-16.md)

Current integration boundary:

- S2 (`lower_vyper_runtime_unit_source_unit_ok`) is proved for any
  contract `check_contract` accepts, under `raw_shape_free_program tops`.
  `raw_shape_free_program` excludes creation and every `raw_call` from
  runtime bodies. Ordinary `msg.gas` values satisfy the shape. The unit shape
  rejects some raw-call lowerings (DELEGATECALL,
  DALLOCA for `msg.data`); a plain CALL/STATICCALL `raw_call` passes the
  shape, but the body-shape proof has no case for it yet, so the exclusion
  is wider than the shape needs. The public `vyper_call_correct` theorem still
  carries `supported_program`, which implies `raw_shape_free_program`.
  Immutable compilation and its encoding/deployment proofs remain available;
  the raw O1 shape contract admits `DLOAD` and `DLOADBYTES`, and the
  body-shape proof covers immutable locations, so S2 covers runtime
  immutable reads. Only `vyper_call_correct` still states
  `immutable_free_program`. The dated audit's exact public call schema
  predates that restriction.

Notes:

- Historical snapshots are preserved for context and may contain stale counts or theorem statuses.
- The dated latest audit is the current navigation/status document for compiler proof cleanup planning.

## Gas observations

`vyper_call_correct` and `e2e_deploy_correctness` tie source
`msg.gas` observations to the EVM frame's recorded GAS readings. Their
preconditions and resource-starvation alternative are unchanged.

DFT can reorder GAS instructions, so the source observations cannot in
general be an ordered subsequence of the EVM readings. `o1_gas_replay`
records the O1 schedules and a certified stage chain, including each
stage’s context shape and function row. At DFT it uses the
output run's canonical event oracle, keyed by call frame, block depth
and instruction ID; events absent from that run read zero. The input
reading list is a finite prefix replayed in source order, and every
fuel agrees with the same oracle. The other O1 stages retain the list.

`runtime_gas_replay` and `deploy_gas_replay` fix the corresponding
compiler phases and EVM entry state. The conclusions existentially choose
a mask `marks` and run the source with `gas_explicit marks gs` from that
certified list `gs`. The mask is existential and has no exported length
bound: `gas_prefix` pads exhausted readings with zero, so additional zero
observations remain permitted. These results compose the existing stage
proofs; they do not remove their admissions. The configured correctness
owner imports both call and deployment correctness, so the existing
`vyperLoweringHol` rollup reaches the constructor proof dependencies too.
