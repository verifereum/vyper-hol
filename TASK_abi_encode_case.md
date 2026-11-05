# TASK: the abi_encode builtin case

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimAbiEncodeScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_abi_encode_case:
  !nocalls ctx func cenv cx ann ensure mid t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann (AbiEncode ensure mid) t args)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- The theorem is proved with no `cheat` in `lowering/exprSimAbiEncodeScript.sml`, or in new helper theories named `exprSimAbiEncode<Part>` (not `exprSimAbiEncodeArgs*`, which another job owns). You may change the leaf's `Ancestors`.
- No new axioms or admissions. Definitions only as proof-only helpers.
- `holbuild -j4 build exprSimAbiEncodeTheory` passes at the default step limit.
- Commit checked work with the trailer `Bot: opus (Claude Opus 5.5)`; do not push.

## Build

From the project root:

```sh
holbuild -j4 build exprSimAbiEncodeTheory
```

Default tactic timeout and memory limits.

Many ancestor theories are admitted by a local overlay (their files are cheated in the work tree and marked skip-worktree). Inherited admissions from them are expected and fine; do not edit, commit or un-skip those files. The admitted ones this task relies on directly, each proved by a separate job with its statement frozen:
- `exprSimAbiGasBridge`: `frag_exec_gas_path`, `abi_decode_sim_gas_path`;
- `exprSimAbiEncodeArgs`: `compile_abi_encode_args_case_gas_sim`, the counted arg-list sim (its postcondition `abi_args_post` is in `abiEncodeArgsSim`).
Use those statements as they are. If one of them turns out insufficient, stop and say exactly what is missing rather than working around it.

## Background

`expr_vv_case` (`lowering/exprSimHypsDefsScript.sml`) unfolds to `expr_vv_sim` (`lowering/exprSimDefsScript.sml`): from `stmt_state_rel` at the fragment's start, running the compiled fragment follows `eval_expr` as a counted `gas_outcome`, ending in `vv_post` on success and `expr_exit` on an exception.

`eval_expr` of a `TypeBuiltin` type-checks, evaluates the operands with `eval_exprs`, then runs the pure `evaluate_type_builtin`. The lowering of `AbiEncode ensure method_id` (`compile_builtin_dispatch` in `lowering/defs/exprLoweringScript.sml`) has three branches:
1. one operand, `~ensure`, word type: `lower_value` the operand, `compile_alloc_buffer 32`, `MSTORE` it, then `lower_abi_encode` from that buffer;
2. one operand, `~ensure`, not a word type: `compile_expr` the operand, `unwrap_value`, then `lower_abi_encode` from the operand's pointer;
3. otherwise: `compile_abi_encode_args`, `compile_alloc_buffer` for the tuple, `compile_store_abi_tuple`, then `lower_abi_encode` from the tuple.

Each branch is a counted prefix (the operand sims from `exprs_case`, or the arg-list sim for branch 3) followed by GAS-free code: buffer allocation, stores, and the encoder. The encoder results (`lower_abi_encode_scratch_open`, `lower_abi_encode_scratch_source_open_rep` in `lowering/abiScratchBuiltinOpenSourceScript.sml`, and the tuple/word sources in `abiBuiltinEncodeReusedInput`, `abiBuiltinEncodeWord`, `abiBuiltinEncodeSource`) conclude `abi_decode_sim ctx func initial actual` for any `func` with the fragment's code; `abi_decode_sim_gas_path` turns that into a counted path with count 0. `lower_abi_encode_scratch_source_open_rep` also gives the source-side result (`evaluate_type_builtin ... = INL (BytesV bytes)`) and the output buffer's contents.

Composition templates for a counted prefix followed by a fragment: `expr_sim_suffix` and `compile_typed_unary_builtin_vv_sim` in `lowering/exprSimHashScript.sml`, `hash_run_path`; the keccak/sha256 cases in `lowering/exprSimBuiltinsScript.sml`.

## Domain Constraints

- Don't change existing theories; helpers go in new `exprSimAbiEncode<Part>` theories or in the leaf.
- No TRY/ORELSE around proof search, no timeout overrides, no unsafe tactics.

## Available Resources

- `lowering/exprSimDefsScript.sml`, `lowering/exprSimHypsDefsScript.sml`, `lowering/loweringPostsScript.sml`: `expr_vv_sim`, `expr_vv_case`, `exprs_case`, `vv_post`, `expr_exit`, `stmt_state_rel`.
- `lowering/exprSimAbiEncodeArgsScript.sml`, `lowering/abiEncodeArgsSimScript.sml`: the arg-list sim and `abi_args_post`.
- `lowering/exprSimAbiGasBridgeScript.sml`: `frag_gas_free`, `frag_exec_gas_path`, `abi_decode_sim_gas_path`.
- `lowering/abiScratchBuiltin*`, `lowering/abiBuiltinEncode*`, `lowering/abiTupleEncode*`, `lowering/abiEncode*Supplier*`, `lowering/abiEncodeOwnership*`, `lowering/abiEncodeEndpointMetadata*`: encoder, tuple store and supplier lemmas from earlier work.
- `lowering/exprSimHashScript.sml`, `lowering/exprSimBuiltinsScript.sml`, `lowering/exprSimWordArgsScript.sml`: counted composition examples.
- `lowering/fragGasModeScript.sml`, `lowering/fragGasPathScript.sml`, `lowering/fragGasSeqScript.sml`: `gas_marked_path` composition.
