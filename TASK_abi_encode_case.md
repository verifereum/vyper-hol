# TASK: Prove ABI encode expression simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering/exprSimAggregatesScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_abi_encode_case:
  !nocalls ctx func cenv cx ann ensure mid t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann (AbiEncode ensure mid) t args)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Replace the target admission with a kernel-checked proof; no new admissions or axioms in its helpers.
- Preserve internal-call operands, exceptions, all method-id, tuple and singleton forms, and every existing value/frame guarantee.
- Repair ancestor proofs affected by the frozen snapshot definition changes while preserving their existing semantic statements, except the four explicitly authorized internal argument-compiler premise migrations below. Keep unrelated admissions and report inherited admitted dependencies of the target.
- Build the target and every changed helper theory.
- Commit checked work with trailer `Bot: astra (OpenAI GPT-6 Astra)`; do not push.

## Build

From the project root:
```sh
holbuild -j2 build exprSimAggregatesTheory
```

Build changed helper theories individually as needed. Use the shared wrapper, default tactic timeout and memory limits. No full dependent cone or CI matrix.

## Background

The rounded ABI allocation and matching resource-contract migration is already present. The approved delayed-operand repair adds function-mutability metadata and `compile_abi_encode_args`: composites are captured before a mutating suffix, while tuple staging remains unchanged. These executable definitions are frozen for this task. The source semantics and target theorem remain unchanged.

An independent preflight found no counterexample but returned UNKNOWN for the full case: the encoder input/resource adapters and full value/frame composition remain unproved. It checked the snapshot design against caller-scope restoration and local-memory preservation. This is not evidence that the full theorem is already proved.

## Domain Constraints

- No executable-definition, source-semantics, stage/contract or top-level assumption changes. Report an exact obstacle rather than silently restricting the theorem.
- Do not assume function-mutability metadata coherence: the endpoint permits an abstract compilation environment.
- Do not assume a canonical source memory layout or full declared capacity merely from `expr_val_at`: it exposes actual `val_footprint`.
- Do not assume literal ABI `has_type` from source typing: fixed bytes of width zero require attention at the existing source-to-encoder interface.
- Leave `compile_abi_decode_case` to its separate task. Do not edit decoder emitter definitions.
- No TRY/ORELSE around proof search, timeout overrides, unsafe tactics, skipped checks, or feature-exclusion premises.
- Keep substantive existing theorems. Do not replace existing proofs with admissions.

## Available Resources

- `lowering/exprSimAggregatesScript.sml`: target and aggregate cases.
- `lowering/exprSimHypsScript.sml`, `lowering/exprSimScript.sml`: case/IH, value, state and frame contracts.
- `lowering/defs/exprLoweringScript.sml`: frozen argument snapshots and ABI dispatch.
- `lowering/defs/compileEnvScript.sml`, `lowering/defs/compileVyperScript.sml`: function-mutability metadata.
- `lowering/defs/allocLimitsScript.sml`, `lowering/defs/builtinAbiScript.sml`: allocation limits and rounded encoder output.
- `lowering/abiBuiltinEncodeSourceScript.sml`, `lowering/abiScratchBuiltinSourceScript.sml`, `lowering/abiBuiltinEncodeWordScript.sml`, `lowering/abiBuiltinEncodeReusedInputScript.sml`: source and tuple encoders.
- `lowering/abiEncoderFragmentScript.sml`, `lowering/abiEncoderPropsScript.sml`: fragment and input/resource interfaces.
- `lowering/abiCallerAllocationScript.sml`, `lowering/abiTupleEncodeSlotScript.sml`: allocation and tuple adapters.
- `lowering/abiEncoderSourceProducerScript.sml`, `lowering/abiTupleEncodeOwnedBytesScript.sml`: source windows and encoding-equivalent tuple input adapters.
- `lowering/abiEncodeSnapshotTestScript.sml`: encountered alias regression.
- Source interpreter, source ABI and typing theories under `semantics/`.

## Notes

The target already contains its original admission. Snapshot definitions and the actual-builtin argument-prefix regression built successfully before launch. This does not establish the full expression case or authorize changing its frozen boundary.

The owner build reached `exprLoweringProps.ci_mono_type_builtin_abi_encode` and failed because its proof still handles `compile_multi_exprs`, while the frozen dispatch now calls `compile_abi_encode_args`. Repair this and any subsequent ancestor proof migrations without changing their semantic contracts. The full target has therefore not yet been parsed under the changed ancestors; independent statement preflight returned UNKNOWN with no counterexample. Definitions at 4c8875d94 are audited and frozen. The rounded scratch-producer fix is present at 898978c4e.


## Authorized snapshot helper migration (2026-11-04)

Argon approved this exact internal migration after checking the frozen dispatcher and the counterexample to the old structural trace:

- In `compile_abi_encode_tuple_trace` (abiBuiltinEncodeWord), replace `compile_multi_exprs cfn ce args origin = (ops,arg_st)` with `compile_abi_encode_args cfn ce args origin = (ops,arg_st)`.
- Make the same premise replacement in `compile_abi_encode_tuple_source`, `compile_abi_encode_tuple_output_live`, and `compile_abi_encode_tuple_producer` (abiBuiltinEncodeReusedInput).
- Keep every conclusion, resource bound, and frame guarantee relative to the actual `arg_st` unchanged. Replace the proof's old length lemma with a checked `compile_abi_encode_args_length`; search for and reuse it if already available.

Owner explicitly authorizes a replacement PLAN for C1.2 covering the structural trace and each of the three semantic consumers as separate proof/audit obligations. Prove the argument evaluation/snapshot relation needed by the frozen full endpoint independently; the premise migration does not establish that relation. Check downstream consumers (including abiScratchBuiltinProducer's theory import) before delivery. No other statement or executable-definition change is authorized by this clarification.

The diagnostic `abiEncodeTupleTraceProbe` confirms only a stale helper falsehood. It is not a counterexample to the full target. Remove this diagnostic theory from the final deliverable after its evidence has served the migration; retain the actual alias regression. The frozen full target and its assumptions remain unchanged.

## Authorized protected-label helper repair (2026-11-04)

The owner has checked the source and saved full-premise counterexample in
`abiProtectedLabelProbeScript.sml` at `3b42b428b`. It refutes only
`abi_args_success_not_label`: an immutable-base label can remain a valid operand,
and the helper lacks the typing conditions of the full expression boundary.
It does not refute `compile_abi_encode_case`.

Replace this false internal helper with a sound proved interface and migrate its
consumer in `abi_args_compile_sim_live`. Repair any associated internal
label-preservation helpers as needed. This explicitly overrides the earlier
helper-statement preservation restriction for this repair. Internal helper
premises may be corrected only when their actual callers discharge them; no new
assumption may reach the frozen expression theorem or its value/frame guarantees.
Executable definitions and source semantics remain frozen. Search all consumers,
prove the replacement and build every changed theory. Remove diagnostic probe
theories from the final deliverable after recording their evidence.

Reconcile the blocked C1.9 plan against this owner clarification, then resume
proof work. No further permission request is needed for this scoped repair.
