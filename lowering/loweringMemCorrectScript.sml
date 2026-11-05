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
 *     mem_safe_raw_unit_memory_ok, and from the pointer discipline and
 *     taint bound
 *   lower_vyper_runtime_unit_run_mem_safe -- the memory-safe run
 *   compile_guarded_body_end_mem_safe -- falling off the end of the body
 *
 * Named admissions (cheats), each a memory twin of a piece S1 rests on:
 *   body_stmts_sim_mem -- body_stmts_sim with memory (#641's body
 *     footprint)
 *   external_entry_value_revert_mem, external_entry_reaches_body_mem --
 *     S1's entry bridge with memory (#639, #867)
 *   external_frame_ret_ok_mem -- the frame's returns with memory (#640),
 *     from entryHaltMem's return leaves
 *   lower_vyper_runtime_unit_ptr_taint -- S3's pointer discipline and
 *     taint bound
 *)
Theory loweringMemCorrect
Ancestors
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect loweringRuntimeCorrect fragExecMem bodyMemoryDefs
  entryHaltMem stmtSim bodySim bodySimMain moduleLowering stmtLowering
  vyperTypeSystem vyperState

val _ = Parse.hide "body";

(* ===== The body (#641) ===== *)

(* ADMITTED (#641): body_stmts_sim with memory, in a frame whose
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
        (package_external_fn tops T (K global_nonreentrant_slot)
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
      (package_external_fn tops T (K global_nonreentrant_slot)
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
  rpt gen_tac >> strip_tac >>
  Cases_on `rt` >>
  gvs[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, comp_get_def, emitHelperTheory.emit_inst_def,
      fresh_id_def, emit_def] >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts ++ [inst]` >>
  drule fn_has_code_same_block >> simp[] >>
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by simp[] >>
  gen_tac >>
  `mem_safe_step fuel ctx inst s` by
    simp[Abbr `inst`, mem_safe_step_non_invoke,
         inst_mem_below_frontier_def, source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
  `?r. step_inst fuel ctx inst s = r /\
       (!s'. r <> OK s') /\ (!e. r <> Error e)` by
    (simp[Abbr `inst`, step_inst_non_invoke] >>
     pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all run_from_step_exit >> simp[]
QED

(* The source exemption rules out the body judgment's exceptional error. *)
Theorem external_body_not_empty_bytes_error:
  !tops am tx ret mut args fbody env orc es0 res es'.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody es0 = (res, es') /\
    ~source_exempt tops (call_external orc [] am tx) ==>
    res <> INR (Error (RuntimeError "convert empty bytes to signed"))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule_all call_external_selected_body >> strip_tac >>
  drule_all call_external_body_run >>
  disch_then (qspecl_then [`type_env tops`, `ret`] strip_assume_tac) >>
  gvs[source_exempt_def, unspecified_behaviour_exempt_def]
QED

Theorem stmt_frag_mem_complete:
  !d ctx func cx lctx RetQ cenv m es res es' sa sb s0 cenv'.
    stmt_frag_mem d ctx func cx lctx RetQ cenv m es res es' /\
    m sa = (cenv', sb) /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\
    ~block_is_terminated sa /\ stmt_res_ok lctx res /\
    res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!s. stmt_lands lctx sb res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb) ==>
         ?fuel. mem_safe_run fuel ctx func s /\
                (!e. run_from fuel ctx func s <> Error e)) ==>
    !fuel. mem_safe_run fuel ctx func s0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [stmt_frag_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
  simp[] >> strip_tac
  >- (qpat_x_assum `!s. stmt_lands _ _ _ _ /\ _ ==> _`
        (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
      metis_tac[mem_safe_run_all_fuel]) >>
  metis_tac[exit_result_not_error, mem_safe_run_all_fuel]
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
  rpt gen_tac >> strip_tac >>
  `?mut args fbody.
     lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody) /\
     LENGTH tx.args = LENGTH args /\
     IS_SOME (bind_arguments (type_env tops) args tx.args)` by
    (fs[valid_vyper_call_def] >> metis_tac[]) >>
  `?env. bind_arguments (type_env tops) args tx.args = SOME env` by
    (Cases_on `bind_arguments (type_env tops) args tx.args` >> fs[]) >>
  Cases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sres, es0)` >> Cases_on `sres`
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all external_entry_reaches_body_mem >> strip_tac >>
      drule_all external_body_frame >> strip_tac >>
      drule_all external_frame_ret_ok_mem >>
      disch_then (qspec_then `func` assume_tac) >>
      Cases_on `eval_stmts
        (initial_evaluation_context am.sources am.layouts tx NONE) fbody es0` >>
      rename1 `_ = (res, es')` >>
      drule_all external_body_source_ok >> strip_tac >>
      drule_all external_body_not_empty_bytes_error >> strip_tac >>
      `rt = if ret = NoneT then NONE else SOME ret` by
        gvs[package_external_fn_def, set_external_package_target_def] >>
      drule guarded_body_code >> strip_tac >>
      drule_all guarded_body_stmts_env >> strip_tac >>
      drule_all body_stmts_sim_mem >>
      disch_then (qspec_then `NoLoop` assume_tac) >>
      `fn_has_code sa sb func /\ fn_has_code sb st' func` by
        (drule_all fn_has_code_split >> simp[]) >>
      qpat_x_assum `(!fuel. mem_safe_run _ _ _ _) ==> _` irule >>
      drule stmt_frag_mem_complete >>
      disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
      impl_tac
      >- (simp[ret_pc_ok_def, return_buf_frame_def] >>
          rpt strip_tac >> gvs[stmt_lands_def] >>
          drule compile_guarded_body_end_mem_safe >>
          disch_then (qspecl_then [`unit.cu_context`, `sb`, `func`, `s`] mp_tac) >>
          simp[] >> disch_then (qspec_then `0` mp_tac) >> metis_tac[]) >>
      simp[]) >>
  irule external_entry_value_revert_mem >> metis_tac[]
QED

(* S3's pointer discipline and taint bound: planned admission, Milestone 5.
   The rest of o1PassContract's source invariant (o1_src_inv), which the O1
   pipeline's simulation (S4) takes beside raw_unit_memory_ok: every
   reachable access other than a revert forward stays in the frame's
   allocations or above the empty reserved region, and what a call request
   or the result reads from moved memory is bounded by the call's dead
   bytes.  Proof idea: the same allocation-budget and buffer-layout
   induction as lower_vyper_runtime_unit_run_mem_safe. *)
Theorem lower_vyper_runtime_unit_ptr_taint:
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
    ==> ptr_discipline 0 unit.cu_context vs /\
        taint_within
          (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
          unit.cu_context vs
Proof
  cheat
QED

(* S3, Milestone 5: the memory-safe run (above) through the bridge
   mem_safe_raw_unit_memory_ok, with alloca_frontier_inv as the frontier
   bound, and the pointer discipline and taint bound (above), with the
   empty reserved region.  The bridge's structural premises (an entry
   function with an entry block, distinct labels, an acyclic reachable call
   graph, the allocation budget below the word size) are
   lowering_context_ok, which run_lowering checks.  The other conjuncts
   come from run_lowering: no eom, and no reserved global region. *)
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
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within
          (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
          unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
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
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  `reachability_closed alloca_frontier_inv unit.cu_context` by
    (irule alloca_frontier_inv_closed >> simp[]) >>
  `fn_entry_inv alloca_frontier_inv unit.cu_context fn
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>)` by
    (irule alloca_frontier_inv_entry >>
     simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, listTheory.MEM_MAP,
          reachable_call_graph_acyclic_def] >>
     fs[initial_venom_state_rel_def] >> metis_tac[]) >>
  `!f inst s. alloca_frontier_inv unit.cu_context f inst s ==>
              s.vs_alloca_next < dimword (:256)` by
    (rpt strip_tac >> drule alloca_frontier_inv_bound >> simp[]) >>
  `!fuel. mem_safe_blocks fuel unit.cu_context fn
            (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>)` by
    (drule_all lower_vyper_runtime_unit_run_mem_safe >> simp[]) >>
  drule_all mem_safe_raw_unit_memory_ok >> strip_tac >>
  drule lower_vyper_runtime_unit_raw_defaults >> strip_tac >>
  drule_all lower_vyper_runtime_unit_ptr_taint >> strip_tac >>
  simp[fixed_region_reserved_def]
QED

