(* Memory-checked boundaries for the custom-error argument head. *)
Theory stmtSimCustomErrorMemStoreHead
Ancestors
  stmtSimCustomErrorMemUnwrap stmtSimCustomErrorMemTypedCopy
  exprSimAggregateBodyCounted exprSimAggregateChildren exprSimMemUnwrap
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimProps exprLoweringProps
  loweringPosts compileEnv context gasSummary fragGasMode fragGasPathMem
  exprSimUnwrapProps exprSimUnwrap fragGasPath typedMemoryCopy vyperTypeArgFits
  aggregateEvaluatedLayout exprSimHypsDefs loweringStateRelDefs exprSimDefs
  vyperInterpreter vyperState venomState freshWrites exprOperandVar
Libs
  monadsyntax

Theorem unwrap_value_body_rebased_path_mem:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' tv vv r /\
  alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path T ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ r.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule vv_post_rebase >> disch_then assume_tac >>
  `vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
     sm r es' (Value v) vv r` by metis_tac[vv_post_read_result] >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e)
     es' (Value v) vv r` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     simp[vv_store_bound_def, read_result_def, return_def] >> metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ es _ _ _ _ tv _ _` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ es' _ _ _ _ tv _ _` kall_tac >>
  Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, comp_return_def] >>
      qexists_tac `r` >> simp[gas_marked_path_def, gas_path_mem_rules] >>
      drule expr_post_of_vv_post_stack >> simp[]) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- suspend "same" >>
  `p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  `is_word_type t ==> t = expr_type e /\
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt` by
    (strip_tac >>
     `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
       gvs[expr_body_pre_def] >>
     drule_all post_value_type_widens >>
     simp[vyperTypeSystemTheory.type_widens_to_def] >> strip_tac >>
     `t = post_value_type ce e` by
       (gvs[vv_post_def, vv_holds_def] >>
        Cases_on `t` >> gvs[is_word_type_def, is_bytestring_type_def] >>
        Cases_on `b` >> gvs[is_word_type_def, is_bytestring_type_def] >>
        Cases_on `b'` >> gvs[is_word_type_def, is_bytestring_type_def]) >>
     `is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
     metis_tac[post_value_type_word]) >>
  mp_tac (GEN_ALL unwrap_memory_marked_read_mem) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  (impl_tac >- simp[]) >>
  strip_tac >> gvs[gas_marked_exec_def, read_result_def, return_def] >>
  qexists_tac `u` >> simp[] >>
  metis_tac[gas_marked_path_def, gas_marked_path_exec, gas_path_normal]
QED

Resume unwrap_value_body_rebased_path_mem[same]:
  mp_tac unwrap_value_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  (impl_tac >- (simp[] >> rpt conj_tac
    >- (gvs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) 
    >- metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
    rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[])) >>
  strip_tac >> qexists_tac `u` >> simp[gas_marked_path_def] >>
  metis_tac[gas_marked_path_def, gas_marked_path_exec, gas_path_normal]
QED

Finalise unwrap_value_body_rebased_path_mem
