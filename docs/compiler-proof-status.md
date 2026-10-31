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

- S2 (`lower_vyper_runtime_unit_source_unit_ok`) is proved for
  `supported_program tops /\ immutable_free_program tops`. The public
  `vyper_call_correct` theorem carries the same explicit source restriction.
  Immutable compilation and its encoding/deployment proofs remain available;
  the raw O1 shape contract excludes `DLOAD` and `DLOADBYTES`, so this proof
  does not yet cover runtime immutable reads. The dated audit's exact public
  call schema predates this explicit restriction.

Notes:

- Historical snapshots are preserved for context and may contain stale counts or theorem statuses.
- The dated latest audit is the current navigation/status document for compiler proof cleanup planning.
