# ABI typing: immutable-arena migration

Authoritative semantics: `docs/IMMUTABLE_PROJECTION_PIN.md` (cd74ce4f).
No changes to semantic definitions, main EvalSoundness, frame, or small-step files.

## Consumer API

- `abi_operand_typed` now includes `AbiImmutable token off tv`, decoding from
  `st.abi_immutables`. Existing local-memory cell facts retain their names and
  statements. Immutable analogues cover capture, release, disjoint writes,
  root/path pop-length writes, and cross-arena writes.
- `abi_operand_valid` now includes immutable type well-formedness, matching tag,
  and `token < LENGTH st.abi_immutables`. **No decode/readiness or current array
  length premise.** `read_abi_operand_valid_typed` and staged/unwrap typing derive
  successful result typing from the actual decode and `decode_value_well_typed`.
- **Required consumer adjustment:** `abi_operand_valid_memory_frame` and the
  three `abi_{expr,place,exprs}_result_valid_memory_frame` theorems now require
  both arena lengths to be nondecreasing. The old memory-length-only statement
  is false for immutable operands. Existing theorem names remain available.
- `capture_abi_memory_typing_frame` additionally exports
  `rt.abi_immutables = st.abi_immutables`; `lookup_abi_local_sound` exports the
  same equality. Existing observations/conclusions are retained.

## New operation facts

`vyperAbiStateTyping` exports immutable capture typing/frame/length/prefix,
write typing/frame/length/keys, exact per-token conditional write footprint
(`write_abi_immutables_cell`), unmatched-key preservation, and local write/release
preservation of the immutable arena. Local capture also has a prefix theorem.

`vyperAbiReadTyping` exports validity preservation for captures/writes in either
arena, immutable validity across local release, and
`unwrap_abi_immutable_valid_snapshot` (complex immutable operands also copy).

`vyperAbiExprTyping` exports `capture_abi_immutable_valid` and
`lookup_abi_immutable_valid`; the latter accepts the typed immutable entry and
actual `get_immutables` result supplied by the source/global lookup proof.

`vyperAbiWriteTyping` exports `write_abi_immutables_typed_success`, mirroring the
existing local-write success theorem. Projection proofs cover the new constructor
without changing their semantic statements; their unused `vyperAbiReadOnly`
ancestor was removed, so the helper stack does not depend on frame/small-step
proofs. Decode typing remains storage-generic.

## Validation

**PASS, no CHEAT warnings:** aggregate target `vyperAbiImmutableTypingTestTheory`
built against current source. It depends on all seven helper modules, existing ABI
typing/bounds tests, and pinned immutable projection regressions. A subsequent
explicit build of all seven helper targets and all three typing test targets
finished successfully in 0.172s (source/dependency keys unchanged).

Build command (isolated output directory, shared toolchain):

```
cd .agent-files/type-abi-probes
holbuild --source-dir ../.. --jobs 2 build --skip-checkpoints \
  --tactic-timeout 2.5 vyperAbiImmutableTypingTestTheory
```

The new immutable typing test has **ten kernel-proved regressions**: invalid later
lengths without readiness, separate token arenas, typed complex immutable unwrap
snapshots, a typed raw complex popped cell beyond logical length, source-key
isolation, local cleanup, successful-read typing from validity alone, logical
length runtime bounds, malformed projection TypeErrors, and capacity runtime
bounds. No cheats or axioms are added. Build log: `.agent-files/abi-typing-current.log`.
