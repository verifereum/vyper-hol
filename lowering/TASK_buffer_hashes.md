# TASK: expression simulation of keccak256, sha256 and method_id (vyper-hol #636)

## Meta
Status: planned
Priority: P1
Created: 2026-10-27
Location: lowering/ (project root is the directory holding holproject.toml)

## Theorem Statement (FROZEN)

Three theorems in `lowering/exprSimBuiltinsScript.sml`, each currently `cheat`:

```sml
Theorem compile_keccak256_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Keccak256 args)

Theorem compile_sha256_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Sha256 args)

Theorem compile_method_id_other_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) /\
    ~(ann = BaseT (BytesT (Fixed 4)) /\
      ?la l. args = [Literal la l] /\
             IS_SOME (method_id_literal (Literal la l))) ==>
    expr_vv_ok cenv (Builtin ann MethodId args)
```

Supporting definitions (read them in their files): `expr_vv_ok`, `expr_sim_pre`,
`expr_sim_inv`, `expr_sim_below`, `alloc_limits_expr` (lowering/exprSimHypsScript.sml);
`expr_vv_sim`, `vv_post`, `vv_holds`, `vv_at`, `expr_sim`, `expr_post`,
`expr_val_rel`, `expr_val_at`, `val_footprint` (lowering/exprSimScript.sml);
`stmt_state_rel`, `alloca_room`, `pending_alloca_size`
(lowering/exprLoweringPropsScript.sml ~120-170); `state_rel`
(lowering/defs/compileEnvScript.sml:1194).

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper theories
 * and build them first.
 *
 * Building generic, powerful abstractions (lemmas, tactics,
 * conversions) that help this proof IS explicitly in scope.
 * The same machinery (a fresh ALLOCA'd buffer, MSTOREs into
 * it, an operand lowered then straight-line code) will be
 * reused by the struct/array literal and empty(T) cases.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build exprSimBuiltinsTheory` from the project root passes with no
   CHEAT for these three theorems and no FAIL; the other theorems of the theory keep
   their current status (several stay cheated; that is expected).
2. No duplicate or near-duplicate lemmas: reuse what exists (see Available
   Resources) and keep each new helper in its most general form.
3. Every proof step runs under holbuild's 2.5 s per-step timeout.

**If a theorem is false as stated:**
- Produce a concrete counterexample in HOL4.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <project root>
holbuild -j4 build exprSimBuiltinsTheory
```

## Background

vyper-hol proves the Vyper→Venom lowering correct. Issue #636 is the expression
simulation: for every expression, the Venom code `compile_expr` emits, run from a
state related (`stmt_state_rel`) to the source state, reaches its end with the
relation kept and the result held as the source value says (`vv_post`/`expr_post`),
or exits as the source error allows (`expr_exit`). `expr_ok` of every smaller
expression is the induction hypothesis (`expr_sim_below`). These three are the
builtins whose lowering hashes a memory buffer: `keccak256`, `sha256` (precompile 2
by STATICCALL) and `method_id` that is not folded to a bytes4 word. The lowering is
`compile_builtin_dispatch_body` (lowering/defs/exprLoweringScript.sml, cases
`Keccak256`, `Sha256` ~2733, `MethodId` ~2903) with helpers in
lowering/defs/builtinHashingScript.sml. Intuition for each is in SML comments next
to the theorems.

## Domain Constraints

- Never edit a proven statement, a definition, or a hypothesis (`expr_sim_pre`,
  `expr_sim_inv`, `stmt_state_rel` ...). New helper theorems and new helper theories
  are fine. A new definition needs a strong reason; prefer existing ones.
- No `cheat` in what you hand back. No `TRY`/`ORELSE` around `metis_tac` or any
  other search: select goals with `>~`, `>-`, `>|`. Never raise the step timeout.
- No `g`/`e`/`p` interactive sessions; build with holbuild.
- Stay in `lowering/exprSim*` files (and new helper theories next to them). Do not
  touch `lowering/intCall*` or statement-lowering files: other work is in flight there.
- Follow `AGENTS.md` at the project root (proof style, `rename1`, short proofs,
  helper lemmas for long cases, Theory/Ancestors headers).
- A new theory must be registered the way the repo registers others (check
  holproject.toml); prefer adding helpers to an existing exprSim theory or one new
  `exprSimHash` theory that exprSimBuiltins lists in Ancestors.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Buffer leaf precedent | lowering/exprSimLiteralBufferScript.sml | Bytes/string literal: ALLOCA a buffer, MSTOREs into it, `literal_alloca_run`, `literal_alloc_buffer_run`, `literal_mstore_state_rel`, `literal_emit_mstore_run`, `literal_memory_vv_post`, `compile_literal_other_vv_sim` (the Bytes[4] method_id literal is this case). Many helpers are `[local]`; promote ones you need rather than copying them. |
| Word builtins precedent | lowering/exprSimWordBuiltinsScript.sml, lowering/exprSimWordArgsScript.sml | One operand lowered with lower_value then straight-line code: `word_builtin_below_sim` etc. |
| Judgments | lowering/exprSimScript.sml, lowering/exprSimHypsScript.sml | definitions above; `expr_ok_stack`, `expr_ok_of_vv`, `expr_sim_pre_builtin_arg`, `expr_sim_pre_eval`, `eval_expr_builtin_value`, `expr_val_rel_footprint_agree` |
| method_id literal pieces | lowering/exprSimBuiltinsScript.sml | `compile_expr_method_id_literal`, `eval_expr_method_id_literal`, `eval_exprs_single_literal` |
| Fragment execution | lowering/fragExecScript.sml, lowering/exprLoweringPropsScript.sml | `frag_exec`, `run_inst_seq`, `emitted_insts`, `fn_has_code`, `stmt_state_rel_exec_alloca`, `alloca_room_next_lt`, `state_rel_frame`, `alloca_room_fields` |
| Emit helpers | lowering/emitHelperPropsScript.sml | `emitted_insts_emit_void`, `step_MSTORE`, step lemmas for MLOAD/ADD etc. |
| Local pointers | lowering/localPtrsPropsScript.sml | `local_ptrs_rel_mstore`, `local_ptrs_rel_alloca_disjoint`, `alloca_inv_fields` |
| Memory encoding | lowering/valueEncodingPropsScript.sml, valueEncodingProofsTheory | `val_in_memory`, `mem_bytes_at`, `mem_word_at`, `mem_bytes_at_mstore_same`, `EL_mem_bytes_at` |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | SHA3 (~901), STATICCALL (~1065, exec_ext_call ~471), GAS, ALLOCA (`exec_alloca`), MLOAD, MSTORE, SHR, SHL, ASSERT |
| Call oracle | venom/defs/venomCallOracleDefsScript.sml, extCallOracleScript.sml | `venom_call_request`, `consume_call_outcome_eq`, `take_outcome`, `computed_precompile`, `precompile_result_sha256`, `record_request` |
| Source semantics | semantics/vyperContextScript.sml | `evaluate_builtin` Keccak256 ~506, Sha256 ~512, MethodId ~606 |
| Typing | semantics/type/vyperTypeSystemScript.sml | `well_typed_builtin_app` Keccak256/Sha256 ~189, MethodId ~223 |
| Typed word encoding | lowering/defs (grep `typed_val_to_w256_def`), lowering/exprSimScript.sml `typed_val_to_w256_word_value` | bytesN values are left-aligned (PAD_RIGHT) words |
| More pointers | lowering/loweringSliceScript.sml:254 `stmt_state_rel_exec_alloca`; extCallOracle `take_outcome_computed_valid`, `adopt_outcome_static`; semantics/type `LENGTH_Keccak_256_w64` (vyperTypeBytesCryptoScript.sml:96); `value_has_type` (bytesN length) | no ready-made frame lemma for `write_memory_with_expansion` (STATICCALL's output write) was found |
| Python reference | ~/workspace/vyper at commit in VYPER_PIN, vyper/codegen_venom/builtins/hashing.py | what the lowering mirrors |

## Notes

- Other theorems in exprSimBuiltinsScript.sml stay cheated; leave them alone.
- The project's CI builds with `--skip-checkpoints --skip-proof-steps`; the
  local build above keeps the 2.5 s step timeout, which is the check that matters.
