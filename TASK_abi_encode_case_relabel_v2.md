# TASK: the abi_encode builtin case, through the relabeled bridge

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

- The theorem is proved with no `cheat` in `lowering/exprSimAbiEncodeScript.sml`, or in helper theories named `exprSimAbiEncode<Part>` (not `exprSimAbiEncodeArgs*` or `exprSimAbiEncodeOblivious*`, which other jobs own). The leaf's `Ancestors` may change.
- No new axioms or admissions. Definitions only as proof-only helpers.
- `holbuild -j4 build exprSimAbiEncodeTheory` passes at the default step limit.
- Commit checked work with the trailer `Bot: opus (Claude Opus 5.5)`; do not push.

## Build

```sh
holbuild -j4 build exprSimAbiEncodeTheory
```

Default tactic timeout and memory limits. Many ancestor theories are admitted by a local overlay (cheated in the work tree, skip-worktree); inherited admissions from them are expected. Do not edit, commit or un-skip those files.

The admitted theorems this task relies on directly, each proved by a separate job with its statement frozen:
- `exprSimAbiGasBridge`: `frag_exec_gas_path`, `abi_decode_sim_gas_path`, `frag_exec_gas_path_relabel`, `abi_decode_sim_gas_path_relabel`;
- `exprSimAbiEncodeOblivious`: `lower_abi_encode_start_oblivious`, `lower_abi_encode_frag_facts`;
- `exprSimAbiEncodeArgs`: `compile_abi_encode_args_case_gas_sim`, the counted arg-list sim (postcondition `abi_args_post` in `abiEncodeArgsSim`).

Use those statements as they are. If one turns out insufficient, stop and say exactly what is missing rather than working around it. In particular, if an encoder lemma you need carries a premise about an outer function (instruction inclusion `MEM i (fn_insts fn') ==> MEM i (fn_insts fn)`, distinct IDs relative to another function, or `alloca_room ctx fn'`/`lookup_function`) that the relabeled bridges' hypothesis can't supply, stop and name that lemma. Don't restate a bridge.

## Background

A previous run (this worktree's history up to 103d23229) found that the original bridges' `frag_gas_free` premise can't be discharged at the expression boundary. Its label conjuncts fail when the expression's entry label `sa.cs_current_bb` equals a label the encoder generates, and `expr_vv_sim` doesn't exclude that (witness: `lowering/exprSimAbiEncodeBridgeAuditScript.sml`). The relabeled bridges remove that need. Their hypothesis asks for the encoder's result from the relabeled start state `start_relabel L ids sa`, whose end state is `start_swap sa L ids sb`:
- `lower_abi_encode_start_oblivious` gives `lower_abi_encode ... (start_relabel L ids sa) = (out, start_swap sa L ids sb)`;
- for the encoder's own result, use the `alloca_room`-based window stack, not the scratch-budget lemmas. A previous run showed that `abi_decoder_budget` (needed by `lower_abi_encode_scratch_open`/`lower_abi_encode_scratch_source_open_rep`) can't be derived from the expression boundary (`exprSimAbiEncodeResourceProbe`): it reserves 32 bytes per instruction ID, while `alloca_room` covers only real ALLOCAs. The window stack proves `lower_abi_encode` from `alloca_inv`, `alloca_room` and `window_alloca_sites func (frag_ids st st')`, with no budget: `abiEncoderWindowContract`, `abiEncoderWindowRun` (`compile_abi_encode_to_buf_window_run`), `abiEncoderWindowSourceRun`, `abiEncodeWindowBuiltin` (`abi_window_builtin_setup`, `abi_window_builtin_finish`), and `abi_encode_relabel_registered_room` in `exprSimAbiEncodeBoundaryProbe`. `compile_abi_encode_to_buf_window_run` carries `alloca_room ctx func`, which needs `lookup_function func.fn_name ctx.ctx_functions = SOME func` and so can't be instantiated at the bridge's `fn'` directly. Use the relabeled hypothesis's `fn'.fn_name = fn.fn_name` and instruction inclusion to transfer room to `fn'` (as `abi_encode_relabel_registered_room` and `dcf54b181`'s observer allocation-room lemma do, e.g. through `ctx with ctx_functions := [fn']`). If no premise arrangement fits the bridge's `!fn'` hypothesis, stop and name the premise that blocks it;
- `lower_abi_encode_frag_facts` supplies `cs_extends`, `frag_ops_free`, the ID distinctness and the `FRONT` label premise. When the encoder emits no blocks, use the original `abi_decode_sim_gas_path` with `frag_gas_free` from the facts lemma.

`expr_vv_case` (`lowering/exprSimHypsDefsScript.sml`) unfolds to `expr_vv_sim` (`lowering/exprSimDefsScript.sml`): from `stmt_state_rel` at the fragment's start, running the compiled fragment follows `eval_expr` as a counted `gas_outcome`, ending in `vv_post` on success and `expr_exit` on an exception.

The lowering of `AbiEncode ensure method_id` (`compile_builtin_dispatch` in `lowering/defs/exprLoweringScript.sml`) has three branches:
1. one operand, `~ensure`, word type: `lower_value` the operand, `compile_alloc_buffer 32`, `MSTORE` it, then `lower_abi_encode` from that buffer;
2. one operand, `~ensure`, not a word type: `compile_expr` the operand, `unwrap_value`, then `lower_abi_encode` from the operand's pointer;
3. otherwise: `compile_abi_encode_args`, `compile_alloc_buffer` for the tuple, `compile_store_abi_tuple`, then `lower_abi_encode` from the tuple.

Each branch is a counted prefix (the operand sims from `exprs_case`, or the arg-list sim for branch 3), then straight-line or GAS-free code, then the encoder. If a block-emitting wrapper step (e.g. `compile_copy_memory` inside `compile_store_abi_tuple`, or `unwrap_value`) needs a counted path, prefer an existing counted lemma for it (look for ones in `exprSimUnwrap`, `exprSimCopy`, `storageCopyGasPath`). If none exists, state its obliviousness/facts pair in a new `exprSimAbiEncode<Part>` leaf against the same `frag_start_oblivious`/`frag_ops_free` definitions and use `frag_exec_gas_path_relabel`.

Composition templates for a counted prefix followed by a fragment: `expr_sim_suffix` and `compile_typed_unary_builtin_vv_sim` in `lowering/exprSimHashScript.sml`, `hash_run_path`; the keccak/sha256 cases in `lowering/exprSimBuiltinsScript.sml`.

The helper leaves from the previous run (`exprSimAbiEncode{Region,RegionTransfer,Observer,Context,Control,EntryControl,Compatibility,Interface,LabelProvenance,Producer,Registration,Resources,Separation,Window}`) may be reused or dropped. `exprSimAbiEncodeBridgeAudit` is a diagnostic: delete it once nothing needs it.

## Domain Constraints

- Don't change existing theories; helpers go in new `exprSimAbiEncode<Part>` theories or in the leaf.
- No TRY/ORELSE around proof search, no timeout overrides, no unsafe tactics.
