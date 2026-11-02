# TASK: S3 memory-safe run: entry/halt leaves and the composition

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/ (lowering/entryHaltMemScript.sml, lowering/loweringMemCorrectScript.sml)

## Theorem Statement (FROZEN)

Six theorems, each currently `cheat` in its file. Prove all six. Copy of
each statement as it stands in the source (same text):

In `lowering/entryHaltMemScript.sml`:

```sml
Theorem compile_external_return_word_frag_mem:
  !ctx op ei msz nr nkey ut iv st x st' w P Q R.
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (!s. P s ==>
         eval_operand op s = SOME w /\ alloca_next_valid s /\
         ?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
               st.cs_next_id = SOME (b, 32)) /\
    (!s ss. P s /\ ss.vs_returndata = word_to_bytes w T /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient = s.vs_transient /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec_mem ctx st st' P Q R

Theorem compile_external_return_copy_frag_mem:
  !ctx op m msz nr nkey ut iv st x st' P Q R.
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    m <= msz /\ msz < dimword(:256) /\
    (!s. P s ==>
         alloca_next_valid s /\
         (?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id msz s).vs_allocas
                st.cs_next_id = SOME (b, msz)) /\
         ?p. eval_operand op s = SOME p /\
             (m = 0 \/ w2n p + m <= s.vs_alloca_next) /\
             !ss. ss.vs_returndata = mem_bytes_at (w2n p) m s.vs_memory /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient = s.vs_transient /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
                  R (Halt ss)) ==>
    frag_exec_mem ctx st st' P Q R

Theorem entry_decode_arg_mem_ok:
  !cenv cenv0 tenv fname args vals env i off hi st st' loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv <= s0.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts st st') s0
```

In `lowering/loweringMemCorrectScript.sml`:

```sml
Theorem compile_guarded_body_end_mem_safe:
  !ctx cenv nkey ut iv stmts rt st x st' sb fn s.
    compile_guarded_body cenv F nkey ut iv stmts rt st = (x, st') /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb /\ fn_has_code sb st' fn /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    !fuel. mem_safe_run fuel ctx fn s /\ (!e. run_from fuel ctx fn s <> Error e)

Theorem lower_vyper_runtime_unit_run_mem_safe:
  !tops rpolicy unit am tx ret vs fn lbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel unit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
```

**Do not modify these statements.** Prove them as-is, or produce a
counterexample.

## Completion Criteria

1. `holbuild -j4 build entryHaltMemTheory loweringMemCorrectTheory` passes
   with the six theorems above proved (no `cheat` in their proofs) and no
   FAILs.
2. The only `cheat`s left in `lowering/loweringMemCorrectScript.sml` are the
   four named admissions `body_stmts_sim_mem`,
   `external_entry_value_revert_mem`, `external_entry_reaches_body_mem` and
   `external_frame_ret_ok_mem`, unchanged. Don't prove, restate, weaken or
   add to them; `lower_vyper_runtime_unit_run_mem_safe` is proved *from*
   them.
3. No `cheat` in `lowering/entryHaltMemScript.sml`.
4. No duplicate or near-duplicate lemmas; helpers in their most general form.

**If a theorem is false as stated:**
- Produce a counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build entryHaltMemTheory loweringMemCorrectTheory
```

Run from the project root (the directory holding `holproject.toml` and this
file).

## Background

S3 says the lowered Vyper unit's raw Venom run is memory-safe: every
instruction executed reads and writes memory below the allocation frontier
(`vs_alloca_next`), except the revert-forwarding pair after a failed call
(`revert_forward_at`, see `venom/compiler/unitTransformDefsScript.sml` and
`mem_safe_block` in `venom/compiler/memSafeRunScript.sml`).

The three `entryHaltMem` theorems are the memory footprints of the external
return sequences and of one static argument's decode at the external entry:
memory-safe versions of `compile_external_return_word_frag`,
`compile_external_return_copy_frag` (lowering/loweringHaltScript.sml) and
`entry_decode_arg_run` (lowering/entryArgPtrsScript.sml). Other proofs will
use them to discharge the named admissions, so they're exported results.

`lower_vyper_runtime_unit_run_mem_safe` is composed like S1:
`lower_vyper_runtime_unit_correct` and `lower_vyper_runtime_unit_body` in
`lowering/loweringRuntimeCorrectScript.sml` are the template. The entry
either reverts on the call value or reaches the body. The body runs by
`body_stmts_sim_mem` at `d = NONE` with `RetQ = (\v es r. T)`, and it
either exits or lands at its end, where `compile_guarded_body_end_mem_safe`
applies. The four named admissions in `loweringMemCorrectScript.sml` are the
memory twins of S1's admissions and are assumed. S1's own admissions in
`loweringRuntimeCorrect` (`external_body_frame`, `external_body_source_ok`,
...) may also be used.

## Domain Constraints

- Build with holbuild only (no Holmake). The tactic timeout is the project
  default, 2.5 s per step; don't raise it.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with
  `>~`, `>-`, `>|`.
- Don't edit proven statements in other theories. Don't add axioms or new
  `cheat`s. New helper lemmas go in `entryHaltMemScript.sml` or
  `loweringMemCorrectScript.sml`, or in the theory they naturally belong
  to, if it's under `lowering/`.
- No `let` in theorem statements.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| frag_exec_mem, run_inst_seq_mem_ok, mem_safe_run_all_fuel, frag_exec_mem_complete, revert_forward_frag_mem, stop_frag_mem, frag_exec_mem_step, frag_exec_mem_run_inst_seq | lowering/fragExecMemScript.sml | memory-safe fragment judgment and rules |
| mem_safe_step/block/blocks/run, mem_safe_run_step, mem_safe_run_head, fuel monotonicity | venom/compiler/memSafeRunScript.sml | memory-safe runs |
| inst_mem_below_frontier, revert_forward, inst_mem_ok_in_fn | venom/compiler/unitTransformDefsScript.sml | frontier check |
| below_frontier_MSTORE, _MCOPY, _RETURN, ... | lowering/instMemFrontierScript.sml | per-opcode frontier forms |
| alloca_site_cases, step_alloca_site, alloca_site_frontier, return_buffer_mem_safe, compile_alloc_buffer_mem_ok, compile_alloc_buffer_frag_mem, compile_keccak256_word_mem_ok, emit_*_mem_ok | lowering/allocaFootprintScript.sml | ALLOCA buffer footprint leaves (template style) |
| return sequences, return_word_run, return_copy_run, *_parts, step_alloca_frame | lowering/loweringHaltScript.sml | the non-memory halt proofs |
| entry_decode_arg_run, entry_decode_arg_frame | lowering/entryArgPtrsScript.sml | the non-memory decode proofs |
| compile_decode_static_arg_calldata, compile_decode_word_arg_calldata | lowering/entryDecodePlanPropsScript.sml | decode simulations |
| static_dec, dec_frame, dec_run, decode_static_buf_run | lowering/abiDecodeStaticPropsScript.sml | static decode machinery |
| stmt_frag_mem, frame_ret_ok_mem, return_buf_frame | lowering/bodyMemoryDefsScript.sml | body memory judgments |
| S1 composition and admissions; guarded_body_code, guarded_body_stmts_env | lowering/loweringRuntimeCorrectScript.sml | template for the composition |
| compile_guarded_body_def, compile_register_positional_args_def | lowering/defs/moduleLoweringScript.sml | lowering definitions |
| exec_alloca_def, step_inst_base (INVALID, STOP) | venom/defs/venomExecSemanticsScript.sml | Venom semantics |
| alloca_next_valid | venom/defs/venomMemDefsScript.sml | alloca invariant |

## Notes

- A statement check (by reading, not built) judged all six provable. Word
  and copy: `w2n (n2w b) <= b` covers wrap, so no `b + 32 < dimword`
  premise is needed; the `SOME (b, size)` premise rules out an earlier
  allocation of another size at the ALLOCA site. Decode: for static
  arguments the decoder emits no scratch ALLOCAs, MCOPY or CALLDATACOPY;
  every MSTORE is inside `[w2n p, w2n p + type_memory_size tv)`, and the
  frontier is constant through the decode. A failing clamp aborts, after
  which `run_inst_seq_mem_ok` is trivially true.
