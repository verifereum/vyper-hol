(* Memory-checked allocation and argument-store handoff. *)
Theory stmtSimCustomErrorMemPrepare
Ancestors
  stmtSimCustomErrorPrepare stmtSimCustomErrorMemStore bodyMemAggregateAlloc
  bodyMemoryPreds bodyCustomErrorExprReady bodyCustomErrorReady
  exprLoweringProps loweringStateRelDefs loweringPosts exprSimHypsDefs compileEnv valueEncodingDefs
  venomMemDefs venomState finite_map pred_set stmtSimDefs bodyCustomErrorSource
  stmtSimLogAllocate stmtLowering fragExec exprSimAggregatesAllocCounted
  allocLimits bodySim exprSimSource bodyCustomErrorWindowBounds
  supportedExprs vyperValue bodyExprPreFacts abiCallerTupleLayout valueEncodingProps
  list vyperTypeABI gasOutcome fragGasMode allocaHistory

Theorem custom_error_allocate_store_ready_mem:
  body_inv tops ctx ce cx /\
  EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Raise (RaiseCustomError err)) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv ce cx env es /\
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
  stmt_exprs_ok ce (Raise (RaiseCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
  body_exprs_mem_ok cx (custom_error_exprs err) /\
  ce.ce_error_info (nsid_to_string id) = SOME params /\
  err = CustomError id positional kwargs /\
  MAP expr_type (custom_error_exprs err) = MAP SND params /\
  compile_alloc_buffer (type_memory_bytes ce (TupleT (MAP SND params))) sa = (buf,sa') /\
  compile_custom_error_store_args ce (custom_error_exprs err) (MAP SND params)
    buf.buf_operand 0 sa' = ((),sm) /\
  fn_has_code sa sa' func /\ fn_has_code sa' sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?inst x t b tvs.
    buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sa'.cs_next_id /\ not_fresh_at sa' x /\
    local_ptrs_reserved ce sa' /\ (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path T ctx func s0 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sa'.cs_current_bb /\ t.vs_inst_idx = LENGTH sa'.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\ lookup_var x t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id =
      SOME (b,type_memory_bytes ce (TupleT (MAP SND params))) /\
    b + type_memory_bytes ce (TupleT (MAP SND params)) < dimword (:256) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP SND params) = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT (MAP SND params)) = SOME (TupleTV tvs) /\
    type_memory_size_list tvs = type_memory_bytes ce (TupleT (MAP SND params)) /\
    type_memory_bytes ce (TupleT (MAP SND params)) < 2 ** 64 /\
    abi_size_bound ce.ce_struct_fields (TupleT (MAP SND params)) + 32 < 2 ** 64 /\
    gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx (custom_error_exprs err)) (es,t)
      (\res ee r. ?vs. res = INL vs /\ r.vs_current_bb = sm.cs_current_bb /\
        r.vs_inst_idx = LENGTH sm.cs_current_insts /\ expr_sim_inv ce cx env ee /\
        stmt_state_rel ctx func ce cx ee r /\
        alloca_history func r /\ t.vs_alloca_next <= r.vs_alloca_next /\ tuple_in_memory vs tvs b r.vs_memory /\
        (!z w. not_fresh_at sa' z /\ lookup_var z t = SOME w ==>
          lookup_var z r = SOME w) /\
        (!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
        (!p n. b <= p /\ p+n <= b+type_memory_bytes ce (TupleT (MAP SND params)) /\
          (p+n <= b \/ b+type_memory_size_list tvs <= p) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n t.vs_memory) /\
        (!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ aid < sa'.cs_next_id /\
          (p+n <= b \/ b+type_memory_bytes ce (TupleT (MAP SND params)) <= p) /\
          (!name lo sz. local_region ce es.scopes t name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n t.vs_memory) /\
        locals_kept ce es ee t r /\
        (EVERY ($~ o expr_has_effect) (custom_error_exprs err) ==>
          (!name lo sz. local_region ce es.scopes t name lo sz ==>
            mem_bytes_at lo sz r.vs_memory = mem_bytes_at lo sz t.vs_memory) /\
          (!p n. (p+n <= b \/ b+type_memory_bytes ce (TupleT (MAP SND params)) <= p) /\
            (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
              sa'.cs_next_id <= i.inst_id /\ FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
              regions_disjoint p n c sz) ==>
            mem_bytes_at p n r.vs_memory = mem_bytes_at p n t.vs_memory)))
      (\res ee exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit)
Proof
  strip_tac >>
  `type_memory_bytes ce (TupleT (MAP SND params)) < 2 ** 64 /\
   abi_size_bound ce.ce_struct_fields (TupleT (MAP SND params)) + 32 < 2 ** 64` by
    (qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
     simp[stmt_exprs_ok_def, alloc_limits_stmt_def, custom_error_alloc_ok_def] >>
     metis_tac[]) >>
  `type_memory_bytes ce (TupleT (MAP SND params)) < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >>
  `well_typed_exprs env (custom_error_exprs err)` by
    metis_tac[custom_error_raise_args_well_typed] >>
  `type_memory_bytes ce (TupleT (MAP expr_type (custom_error_exprs err))) < 2 ** 64` by
    metis_tac[] >>
  drule_all custom_error_tuple_layout >> strip_tac >>
  `!e ee. MEM e (custom_error_exprs err) /\ expr_sim_inv ce cx env ee ==>
    expr_body_pre ce cx env e ee` by
    (rpt strip_tac >> irule custom_error_raise_arg_body_pre >> metis_tac[]) >>
  `!e. MEM e (custom_error_exprs err) ==>
    (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
      acyclic_struct_metadata ce.ce_struct_fields)` by
    (rpt strip_tac >> fs[listTheory.EVERY_MEM] >> metis_tac[supported_pure_int_calls]) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b (type_memory_size_list tvs)` by
    (rpt strip_tac >>
     irule (SRULE [] (Q.INST [`off` |-> `0`] custom_error_buffer_immutable_frame)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     gvs[] >> qexistsl_tac [`iv`,`name`] >> simp[]) >>
  gvs[] >>
  drule_at (Pat `compile_custom_error_store_args _ _ _ _ _ _ = _`)
    custom_error_store_args_sim_mem >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `_.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >> simp[] >>
  (impl_tac >- (conj_tac >- metis_tac[] >> metis_tac[])) >>
  disch_tac >> qexistsl_tac [`inst`,`t`,`b`] >> simp[]
QED
