(*
 * Compiler Correctness — Draft Proof Architecture
 *
 * This file drafts the correctness proof statements that connect
 * all compiler phases to the Vyper-HOL semantics. It serves as
 * a blueprint for closing the remaining proof gaps.
 *
 * The compiler correctness theorem has three legs:
 *
 *   Vyper source ──[lowering]──> Venom IR ──[pipeline]──> Optimized Venom ──[codegen]──> EVM
 *
 * Leg 1 (Lowering):   call_external ~ run_context (run_lowering ...)
 * Leg 2 (Pipeline):  run_context ~ run_context ∘ pipeline (via ctx_pass_correct)
 * Leg 3 (Codegen):    run_context ~ EVM run (via codegen_correct + initial_evm_rel)
 *
 * Each leg produces observable_result_equiv which composes via
 * observable_equiv_trans to give vyper_evm_correspondence.
 *
 * TOP-LEVEL (drafts):
 *   vyper_lowering_correct      — Leg 1: Vyper source ~ Venom IR
 *   venom_pipeline_correct      — Leg 2: Venom IR ~ Optimized Venom (EXISTS, proved)
 *   codegen_semantics_correct   — Leg 3 sub-bridge: codegen preserves mem safety
 *   compiler_correct            — Full composition: Vyper ~ EVM
 *
 * BRIDGE OBLIGATIONS (drafts):
 *   lowering_state_rel          — Vyper abstract state ~ Venom state
 *   lowering_preserves_calls    — call_external ~ run_context after lowering
 *   codegen_context_obligations — lowering/pipeline preconditions required by codegen
 *)

Theory compilerCorrectnessDraft
Ancestors
  venomPipelineCorrect
  passSimulationDefs passSimulationProps
  stateEquiv stateEquivProps
  venomExecSemantics
  e2eDefs
  codegenCorrectness

(* =====================================================================
   Leg 2: Pipeline Correctness (ALREADY PROVED)
   ===================================================================== *)

(* venom_pipeline_correct is already proved — parameterized by per-phase
   correctness. compose_passes_correct lifts N per-pass theorems into
   a single ctx_pass_correct via rel_seq composition. *)

(* =====================================================================
   Leg 1: Lowering Correctness (DRAFT)
   ===================================================================== *)

(* The lowering transforms Vyper source (top-level declarations) into
   Venom IR (venom_context). The correctness theorem states:

   If call_external am tx produces (INL v, am') (success),
   then run_context on the lowered Venom context produces Halt ss'
   where ss' agrees with am' on observable state (accounts, storage,
   logs, returndata).

   If call_external am tx produces (INR (AssertException _), _) (revert),
   then run_context produces Abort Revert_abort ss' where accounts/storage
   are unchanged.

   Draft statement follows the top-level lowering theorem and keeps logs
   inside the external-call result relation. *)

(* Lowering state relation: maps Vyper abstract machine state to
   Venom state fields. Key mappings:
   - am.accounts ↔ s.vs_storage (via storage_rel)
   - am.tStorage  ↔ s.vs_transient_storage
   - tx.args      ↔ s.vs_call_ctx.cc_calldata (via calldata_encodes)
   - am.sources   ↔ ctx.ctx_functions (via run_lowering structure)
   - Environment values (caller, value, etc.) ↔ s.vs_call_ctx fields *)

(* Draft: The main lowering correctness theorem.
   This bridges Vyper source semantics to Venom IR execution. *)
Theorem vyper_lowering_correct_draft:
  !tenv cenv selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    am tx vs args ret.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0
    ==>
    !fuel.
      external_call_result_rel tenv cenv
        (initial_evaluation_context am.sources am.layouts tx)
        ret (call_external am tx) (run_context fuel ctx vs)
Proof
  cheat (* Bridge: requires proving lowering translation correct.
           Key subgoals:
           1. ABI encoding/decoding: calldata_encodes ↔ Venom MLOAD from calldata
           2. Expression evaluation: compile_expr produces correct Venom instructions
           3. Statement execution: compile_stmt preserves state correspondence
           4. Function dispatch: selector matching + function lookup
           5. Storage operations: s_store/s_load ↔ SSTORE/SLOAD
           6. Memory operations: Vyper heap ↔ Venom MSTORE/MLOAD
           7. Log emission: push_log ↔ LOG with correct topics/data
           8. Control flow: Vyper control flow ↔ Venom JMP/JNZ/STOP/REVERT
           These correspond to the existing lowering proof worktrees. *)
QED

(* =====================================================================
   Leg 3 Sub-Bridge: Codegen Structural Obligations (DRAFT)
   ===================================================================== *)

(* codegen_correct requires ctx_wf, codegen_ready, entry_fn_no_ret,
   and step_mem_safe. Codegen success alone cannot establish these
   source-context facts; lowering/pipeline correctness must supply them
   as explicit obligations. *)

(* Draft: explicit obligations required before applying codegen_correct. *)
Definition draft_codegen_context_obligations_def:
  draft_codegen_context_obligations ctx spill_hwm ⇔
    codegen_ready ctx ∧
    ctx_wf ctx ∧
    (!name efn. ctx.ctx_entry = SOME name ∧
                lookup_function name ctx.ctx_functions = SOME efn ⇒
                entry_fn_no_ret efn) ∧
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions ∧
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2)
End

Theorem draft_codegen_context_obligations_elim:
  !ctx spill_hwm.
    draft_codegen_context_obligations ctx spill_hwm ==>
    codegen_ready ctx /\ ctx_wf ctx /\
    (!name efn. ctx.ctx_entry = SOME name /\
                lookup_function name ctx.ctx_functions = SOME efn ==>
                entry_fn_no_ret efn) /\
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions /\
       step_inst fuel' ctx inst vs1 = OK vs2 ==>
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2)
Proof
  rw[draft_codegen_context_obligations_def]
QED

(* =====================================================================
   EVM Bridge: run_call Correspondence (DRAFT)
   ===================================================================== *)

(* The EVM bridge connects vyper_evm_correspondence (defined via VFM's
   `run` which executes ALL frames) to `run_call` (which stops when
   the current call frame completes).

   For outermost calls: run_call = run (depth 1, no frame pops possible)
   For inner calls: run_call stops at frame boundary via handle_exception

   Currently cheated in e2eCorrectnessScript as evm_correspondence_to_call_result. *)
Theorem evm_correspondence_to_call_result_draft:
  !tenv event_info am tx ret es.
    vyper_evm_correspondence tenv event_info ret am tx es /\
    ~NULL es.contexts
    ==>
    ?r es_final.
      run_call es = SOME (r, es_final) /\
      call_result_matches tenv event_info am tx ret r es es_final
Proof
  cheat (* Key subgoals:
           1. OWHILE termination: EVM has finite gas
           2. run_call stops at correct depth (frame boundary)
           3. handle_exception correctly pops frames
           4. Success: returndata encoding, accounts, logs match
           5. Revert: accounts rolled back, 0w on stack
           6. Error: T (no postcondition for source-level errors)
           Relies on EVM semantic properties of step/handle_exception. *)
QED

(* Draft: EVM REVERT preserves pre-call state.
   After REVERT, accounts and transient storage are unchanged
   because the EVM's rollback mechanism restores the pre-call state.
   For single-frame: rollback = pre-call accounts.
   For multi-frame: caller's rollback is pre-call. *)
Theorem evm_revert_state_unchanged_draft:
  !es es'. run es = SOME (INR (SOME Reverted), es') /\
           ~NULL es.contexts
           ==>
           state_unchanged es es'
Proof
  cheat (* EVM semantic property: REVERT opcode sets status to Reverted,
           handle_exception restores rollback.accounts.
           Key step: trace through handle_exception for Reverted case,
           showing it restores SND(HD es.contexts).accounts to
           pre-call values via rollback. *)
QED

(* =====================================================================
   Pass Correctness Migration: lift_result → pass_correct
   ===================================================================== *)

(* The standard correctness statement is pass_correct, which handles
   independent fuels for both sides. Several passes still use the
   older same-fuel lift_result statement.

   Migration path (for passes without Error disjunction):
     lift_result R s1 s2  ==>  pass_correct R R R exec1 exec2
   via: lift_result_implies_pass_correct + run_blocks_deterministic

   For passes WITH Error disjunction (like assign_elim):
     Must eliminate the error case first by strengthening preconditions
     (e.g. wf_ssa dominance guarantees variable availability).
*)

(* Draft: assert_combiner correctness as pass_correct.
   Current: lift_result (state_equiv (ac_fresh_vars_fn fn)) in
   assertCombinerCorrectnessScript.sml.
   Migration: ac has no Error disjunction, so direct conversion. *)
Theorem ac_pass_correct_draft:
  !ctx fn s.
    let fn' = ac_transform_function fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    (* ... same preconditions as ac_transform_function_correct ... *)
    True (* placeholder for full preconditions *)
    ==>
    pass_correct (state_equiv (ac_fresh_vars_fn fn))
                 (execution_equiv UNIV) (execution_equiv UNIV)
      (\fuel. run_blocks fuel ctx fn s)
      (\fuel. run_blocks fuel ctx fn' s)
Proof
  cheat (* Bridge from lift_result to pass_correct:
           - Prove run_blocks_deterministic for both fn and fn'
           - Apply lift_result_implies_pass_correct *)
QED

(* Draft: branch_opt correctness as pass_correct.
   Current: lift_result (state_equiv (bo_fresh_vars_fn fn)) in
   branchOptCorrectnessScript.sml.*)
Theorem bo_pass_correct_draft:
  !ctx live_at fn s.
    let fn' = branch_opt_function live_at fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\ fn_inst_wf fn /\
    (* ... same preconditions as branch_opt_function_correct ... *)
    True (* placeholder *)
    ==>
    pass_correct (state_equiv (bo_fresh_vars_fn fn))
                 (execution_equiv (bo_fresh_vars_fn fn))
                 (execution_equiv (bo_fresh_vars_fn fn))
      (\fuel. run_blocks fuel ctx fn s)
      (\fuel. run_blocks fuel ctx fn' s)
Proof
  cheat
QED

(* Draft: single_use_expansion correctness as pass_correct.
   Current: lift_result (state_equiv (sue_fresh_vars_fn fn)). *)
Theorem sue_pass_correct_draft:
  !ctx fn s.
    fn_inst_wf fn /\
    (* ... same preconditions as sue_expand_function_correct ... *)
    True (* placeholder *)
    ==>
    pass_correct (state_equiv (sue_fresh_vars_fn fn))
                 (execution_equiv (sue_fresh_vars_fn fn))
                 (execution_equiv (sue_fresh_vars_fn fn))
      (\fuel. run_blocks fuel ctx fn s)
      (\fuel. run_blocks fuel ctx (sue_expand_function fn) s)
Proof
  cheat
QED

(* Draft: affine_folding correctness as pass_correct.
   Current: lift_result (state_equiv {}) in
   affineFoldingCorrectnessScript.sml. *)
Theorem af_pass_correct_draft:
  !ctx fn s.
    fn_inst_wf fn /\
    (* ... same preconditions as af_transform_function_correct ... *)
    True (* placeholder *)
    ==>
    pass_correct (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (\fuel. run_blocks fuel ctx fn s)
      (\fuel. run_blocks fuel ctx (af_transform_function fn) s)
Proof
  cheat
QED

(* Draft: overflow_elim correctness as pass_correct.
   Current: lift_result (state_equiv {}) with Error disjunction in
   overflowElimCorrectnessScript.sml.
   NOTE: Has Error disjunction (similar to assign_elim).
   Must strengthen preconditions to eliminate error case
   (e.g. add wf_ssa to guarantee variable availability). *)
Theorem oe_pass_correct_draft:
  !ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\
    wf_ssa fn /\ (* Added to eliminate Error disjunction *)
    (* ... same preconditions as overflow_elim_function_correct ... *)
    True (* placeholder *)
    ==>
    pass_correct (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (\fuel. run_blocks fuel ctx fn s)
      (\fuel. run_blocks fuel ctx (overflow_elim_function fn) s)
Proof
  cheat (* Step 1: Prove same-fuel lift_result without Error disjunction
           (wf_ssa dominance eliminates unbound variable access)
           Step 2: Apply lift_result_implies_pass_correct *)
QED

(* =====================================================================
   Pipeline Instance (DRAFT)
   ===================================================================== *)

(* The O2 pipeline instance is currently cheated (o2_pipeline_ctx_pass_correct).
   To prove it, we need to compose individual pass correctness theorems
   using compose_passes_correct.

   The O2 pipeline (o2_fn_passes) applies:
   make_ssa → ircf → ricf → dse → load_elim → concretize_mem_loc →
   mem2var → single_use_expansion → tail_merge → cfg_normalization →
   branch_opt → lower_dload → literals_codesize → cse →
   algebraic_opt → affine_folding → assert_elim → overflow_elim →
   assert_combiner → remove_unused → sccp

   Each pass must have pass_correct proved (not just lift_result)
   before composition works. The compose_passes_correct theorem
   takes a list of (pass, R_ok, R_term) triples and combines via
   FOLDL rel_seq (=) [R_ok_1; R_ok_2; ...].

   Key constraint: each R_ok_i must imply observable_equiv for
   the final e2e theorem. state_equiv vars implies observable_equiv
   when vars ⊆ fresh variables (not observable).

   Strategy:
   1. Prove each pass's pass_correct with its specific R_ok
   2. Show each R_ok implies observable_equiv
   3. Apply compose_passes_correct
   4. Apply pass_correct_implies_observable with the composed relation *)

(* =====================================================================
   Full Compiler Correctness (DRAFT)
   ===================================================================== *)

(* The top-level theorem: compiling a Vyper program produces EVM bytecode
   that, when executed, gives the same result as the Vyper source semantics.

   This is vyper_call_correct in e2eCorrectnessScript, parameterized by
   the pipeline. The key dependencies are:

   1. vyper_lowering_correct (Leg 1) — currently cheated
   2. ctx_pass_correct pipeline R_ok R_term ctx vs (Leg 2) — parameterized
   3. codegen_correct (Leg 3) — proved (needs structural bridge cheats)
   4. evm_correspondence_to_call_result (EVM bridge) — cheated
   5. evm_revert_state_unchanged (EVM property) — cheated

   Closing all 7 bridge cheats would make vyper_call_correct fully proved
   (modulo the pipeline parameter, which composes individual pass proofs). *)

Theorem compiler_correct_draft:
  !program pipeline dispatch_strategy runtime_bc
   am tx tenv ret ctxt rb rest es event_info.
    (exists deploy_bc.
       compile_vyper program pipeline dispatch_strategy
         = SOME (deploy_bc, runtime_bc)) /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel program runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call am tx tenv ctxt.msgParams.data ret /\
    (* Pipeline correctness (composable from pass proofs) *)
    (let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn dispatch
            bucket_count fn_meta_bytes dense_buckets entry_info entry_label in
     ctx_pass_correct pipeline observable_equiv observable_equiv ctx vs)
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      ?r es_final.
        run_call es = SOME (r, es_final) /\
        call_result_matches tenv event_info am tx ret r es es_final
Proof
  cheat (* Logical structure:
           1. Apply vyper_lowering_correct to get Venom~Vyper correspondence
           2. Apply e2e_venom_pipeline to get pipeline~original correspondence
           3. Apply e2e_venom_to_evm to get EVM~Venom correspondence
           4. Apply evm_correspondence_to_call_result to bridge to run_call
           Corollary of vyper_call_correct once all bridge cheats close. *)
QED
