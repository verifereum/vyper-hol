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
  runtime bodies and from the default arguments the entry code evaluates.
  Ordinary `msg.gas` values satisfy the shape. The unit shape
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
