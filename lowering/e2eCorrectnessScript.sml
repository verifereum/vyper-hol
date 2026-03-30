(*
 * End-to-End Vyper-to-EVM Correctness
 *
 * Composes three legs:
 *   1. vyper_to_venom_correct: call_external ~ run_context
 *   2. venom_pipeline_correct: run_context ~ run_context o pipeline
 *   3. codegen_correct: run_context ~ EVM run
 *
 * TOP-LEVEL:
 *   compile_vyper_raw      -- full compilation chain (exploded args)
 *   compile_vyper_raw_well_formed -- compilation => codegen preconditions
 *   e2e_vyper_to_evm       -- Vyper source semantics ~ EVM execution
 *
 * Definitions (return_data_encodes, log_entry_corresponds,
 * state_effects_match, etc.) are in e2eDefsTheory.
 *)

Theory e2eCorrectness
Ancestors
  e2eDefs
  vyperLoweringCorrect vfmExecution
  venomPipelineCorrect
  passSimulationDefs
  codegenCorrectness
  stateEquivProps
  venomExecSemantics
  vyperABI
  compileEnv
  venomInst

(* ===== Full Compilation ===== *)

(* Full compilation: lowering + pass pipeline + codegen.
   Pipeline is a parameter -- instantiate for O2, O3, Os, etc. *)
Definition compile_vyper_raw_def:
  compile_vyper_raw selectors ext_fns int_fns fb_fn
                dispatch bucket_count fn_meta_bytes entry_label
                (pipeline : venom_context -> venom_context)
                fn_eom_map data_seg =
    let ctx = run_lowering selectors ext_fns int_fns fb_fn
                dispatch bucket_count fn_meta_bytes entry_label in
    let ctx' = pipeline ctx in
    codegen ctx' fn_eom_map data_seg
End

(* ===== Component Theorems ===== *)

(* Pipeline preserves Venom semantics.
   Follows from ctx_pass_correct -> pass_correct -> result_equiv.
   result_equiv preserves all observable state including returndata,
   accounts, transient, and logs (via execution_equiv). *)
Theorem e2e_venom_pipeline:
  !ctx pipeline fresh vs.
    ctx_pass_correct pipeline fresh ctx vs
    ==>
    !fuel. ?fuel'.
      result_equiv fresh
        (run_context fuel ctx vs)
        (run_context fuel' (pipeline ctx) vs)
Proof
  cheat
QED

(* Codegen correctness: Venom execution corresponds to EVM execution.
   Wraps codegen_correct with initial_evm_rel. *)
Theorem e2e_venom_to_evm:
  !ctx fn_eom_map data_seg bytecode spill_hwm vs fuel.
    codegen_ready ctx /\
    ctx_wf ctx /\
    codegen ctx fn_eom_map data_seg = SOME bytecode /\
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions /\
       step_inst fuel' ctx inst vs1 = OK vs2 ==>
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) /\
    spill_mem_covered spill_hwm vs.vs_memory
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      (case run_context fuel ctx vs of
         Halt vs' =>
           ?es'. run es = SOME (INR NONE, es') /\
                 final_state_rel vs' es'
       | Abort Revert_abort vs' =>
           ?es'. run es = SOME (INR (SOME Reverted), es') /\
                 final_state_rel vs' es'
       | Abort ExHalt_abort vs' =>
           ?es' exc. run es = SOME (INR (SOME exc), es') /\
                     exc <> Reverted /\
                     final_state_rel vs' es'
       | OK _ => F
       | IntRet _ _ => F
       | Error _ => T)
Proof
  cheat
QED

(* ===== Codegen Hypothesis Theorems ===== *)

(* Compilation produces a well-formed codegen-ready context.
   Discharged by construction: run_lowering produces wf context,
   pipeline passes preserve well-formedness, codegen succeeds.

   The spill_hwm is determined by the codegen's stack plan:
   it is the maximum sa_next_offset across all function plans.
   step_mem_safe holds because Vyper's memory allocator ensures
   all user allocations are below fn_eom (which is 0 for the
   whole-context case, meaning no user memory overlaps spills).
   spill_mem_covered holds because the entry code expands
   memory to cover the maximum spill offset. *)
Theorem compile_vyper_raw_well_formed:
  !selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes entry_label
    pipeline fn_eom_map data_seg bytecode fresh vs.
  let ctx = run_lowering selectors ext_fns int_fns fb_fn
              dispatch bucket_count fn_meta_bytes entry_label in
  let ctx' = pipeline ctx in
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
    ctx_pass_correct pipeline fresh ctx vs
    ==>
    codegen_ready ctx' /\ ctx_wf ctx' /\
    ?spill_hwm.
      (!fn inst vs1 vs2 fuel'.
         MEM fn ctx'.ctx_functions /\
         step_inst fuel' ctx' inst vs1 = OK vs2 ==>
         step_mem_safe <| sa_fn_eom := 0;
                          sa_next_offset := spill_hwm;
                          sa_free_slots := [] |> vs1 vs2) /\
      spill_mem_covered spill_hwm vs.vs_memory
Proof
  cheat
QED

(* ===== Full E2E: Vyper to EVM ===== *)

(* Composes all three legs into a single theorem relating Vyper
   source semantics to EVM bytecode execution.
 *
 * Correspondence:
 *   Vyper success (INL v)       => EVM normal halt, returndata =
 *                                  ABI encoding of v, accounts,
 *                                  transient storage, and logs match
 *   Vyper revert (AssertExc)    => EVM REVERT, state_unchanged
 *   Vyper error                 => T (indicates source-level error;
 *                                  could be strengthened to F under
 *                                  well-formedness of am/tx)
 *   Break/Continue/Return       => F -- internal control flow,
 *                                  never escapes call_external
 *)

(* Main E2E theorem: Vyper source semantics ~ EVM execution.

   Gas: existential -- there exists a gas bound such that with enough
   gas, EVM execution always produces the correct result. Non-vacuous:
   the success case is always reachable. No OOG escape hatch needed.

   ctx_pass_correct is an assumption because the pipeline is
   parametric -- it holds for any pipeline assembled from
   semantics-preserving passes (e.g., the standard O2 pipeline).
   It is proved per-pipeline by composing individual pass proofs.
   See e2e_vyper_to_evm_O2 for a concrete instance. *)
Theorem e2e_vyper_to_evm:
  !tenv event_info pipeline selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes entry_label
    fn_eom_map data_seg bytecode
    am tx vs fresh args ret.
  let ctx = run_lowering selectors ext_fns int_fns fb_fn
              dispatch bucket_count fn_meta_bytes entry_label in
    (* Compilation produces bytecode *)
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
    (* Source function exists, calldata valid, selector routes *)
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0 /\
    (* Pipeline preserves semantics (proved per-pipeline by
       composing individual pass correctness theorems) *)
    ctx_pass_correct pipeline fresh ctx vs
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      vyper_evm_correspondence tenv event_info ret am tx es
Proof
  cheat
QED

(* ===== Concrete Pipeline Instances ===== *)

(* O2 pipeline preserves semantics.
   Instantiates venom_pipeline_correct for the O2 pass sequence.
   No ctx_pass_correct assumption -- discharged by composing
   individual O2 pass correctness theorems.
   Analysis functions (make_ssa, ircf, ricf, dse, amap, live_at)
   are parameters of the pass sequence. *)
Theorem e2e_vyper_to_evm_O2:
  !tenv event_info selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes entry_label
    ircf_global ricf_global threshold
    make_ssa ircf ricf dse_analysis amap live_at
    fn_eom_map data_seg bytecode
    am tx vs args ret.
  let pipeline = venom_pipeline ircf_global ricf_global threshold
        (o2_fn_passes make_ssa ircf ricf dse_analysis amap live_at) in
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      vyper_evm_correspondence tenv event_info ret am tx es
Proof
  cheat
QED
