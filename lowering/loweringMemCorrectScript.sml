(*
 * S3, Milestone 5: the lowered unit's raw run is memory-safe
 *
 * lower_vyper_runtime_unit_run_mem_safe is composed like S1
 * (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct): the entry
 * reaches the selected function's body or reverts on the call value, the
 * body runs, and it returns or falls off its end.  Each piece is the
 * memory-safe twin of S1's: the body by bodyMemoryDefs's judgments at
 * d = NONE (an external frame has no caller return buffer), the end by
 * entryHaltMem's leaves.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_memory_ok -- S3, from the run through
 *     mem_safe_raw_unit_memory_ok
 *   lower_vyper_runtime_unit_run_mem_safe -- the memory-safe run
 *   compile_guarded_body_end_mem_safe -- falling off the end of the body
 *
 * Named admissions (cheats), each a memory twin of a piece S1 rests on:
 *   body_stmts_sim_mem -- body_stmts_sim with memory (SEQ-658's body
 *     footprint)
 *   external_entry_value_revert_mem, external_entry_reaches_body_mem --
 *     S1's entry bridge with memory (#639, #867)
 *   external_frame_ret_ok_mem -- the frame's returns with memory (#640),
 *     from entryHaltMem's return leaves
 *)
Theory loweringMemCorrect
Ancestors
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound
  vyperLoweringCorrect loweringRuntimeCorrect fragExecMem bodyMemoryDefs
  entryHaltMem stmtSim bodySim bodySimMain moduleLowering stmtLowering
  vyperTypeSystem vyperState

val _ = Parse.hide "body";

(* ===== The body (SEQ-658) ===== *)

(* ADMITTED (SEQ-658): body_stmts_sim with memory, in a frame whose
   caller return buffer, if any, is d. *)
Theorem body_stmts_sim_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    eval_stmts cx ss es = (res, es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) es res es'
Proof
  cheat
QED

(* ===== The entry (#639, #867) ===== *)

(* ADMITTED (#639): external_entry_value_revert's run is memory-safe. *)
Theorem external_entry_value_revert_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env e st efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    !fuel. mem_safe_blocks fuel unit.cu_context efn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED

(* ADMITTED (#639): external_entry_reaches_body, with the body's frame
   free of a caller return buffer, and with a memory-safe run from the
   body's start making the run from __entry memory-safe: the selector
   dispatch and the entry checks touch no memory, and the argument decode
   writes only the parameters' buffers (entryHaltMem's
   entry_decode_arg_mem_ok). *)
Theorem external_entry_reaches_body_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      stmt_state_rel unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      alloca_history func s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      cenv.ce_return_buf = NONE /\
      ((!fuel. mem_safe_run fuel unit.cu_context func s0) ==>
       !fuel. mem_safe_blocks fuel unit.cu_context efn
                (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                            vs_inst_idx := 0 |>))
Proof
  cheat
QED

(* ===== The frame's returns (#640) ===== *)

(* ADMITTED (#640): external_frame_ret_ok with memory, for any outcome of
   the return: every return sequence halts memory-safely, by entryHaltMem's
   return leaves after the returned expression's memory simulation. *)
Theorem external_frame_ret_ok_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok_mem NONE unit.cu_context func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\v es r. T) cenv ret
Proof
  cheat
QED

(* ===== The end of the body ===== *)

(* Falling off the end of the guarded body (no lock): a STOP, or INVALID
   for a function with a return type; neither touches memory. *)
Theorem compile_guarded_body_end_mem_safe:
  !ctx cenv nkey ut iv stmts rt st x st' sb fn s.
    compile_guarded_body cenv F nkey ut iv stmts rt st = (x, st') /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb /\ fn_has_code sb st' fn /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    !fuel. mem_safe_run fuel ctx fn s /\ (!e. run_from fuel ctx fn s <> Error e)
Proof
  cheat
QED

(* ===== S3 ===== *)

(* The run from the unit's entry is memory-safe: every instruction it
   executes, callee frames included, reads and writes memory below the
   allocation frontier (or is a revert forwarding).  Excluding
   source_exempt is essential: dynamic decoding can read unchecked
   offsets. *)
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
Proof
  cheat
QED

(* S3, Milestone 5: the memory-safe run (above) through the bridge
   mem_safe_raw_unit_memory_ok, with alloca_frontier_inv as the frontier
   bound.  The bridge's structural premises (an entry function with an entry
   block, distinct labels, an acyclic reachable call graph, the allocation
   budget below the word size) are lowering_context_ok, which run_lowering
   checks. *)
Theorem lower_vyper_runtime_unit_memory_ok:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)
    ==> raw_unit_memory_ok unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >> strip_tac >>
  drule run_lowering_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  drule lowering_context_ok_alloca_budget >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    metis_tac[lookup_function_MEM, lookup_function_result_name] >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  qspecl_then [`unit.cu_context`, `vs`, `"__entry"`, `fn`, `lbl`,
               `alloca_frontier_inv`] mp_tac mem_safe_raw_unit_memory_ok >>
  impl_tac
  >- (rpt conj_tac
      >- simp[]
      >- simp[]
      >- simp[]
      >- fs[listTheory.EVERY_MEM]
      >- (irule alloca_frontier_inv_closed >> simp[])
      >- (irule alloca_frontier_inv_entry >>
          simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, listTheory.MEM_MAP,
               reachable_call_graph_acyclic_def] >>
          fs[initial_venom_state_rel_def] >> metis_tac[])
      >- metis_tac[alloca_frontier_inv_bound]
      >> drule_all lower_vyper_runtime_unit_run_mem_safe >> simp[]) >>
  simp[]
QED

