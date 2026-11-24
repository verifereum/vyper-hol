(* The false-copy positional branch reads the evaluated source result,
   but retains the child cursor, physical state, and both ghosts. *)
Theory entryCreateExtPosRetained
Ancestors
  entryCreateFocusSpec entryCreatePathScope bodyFullExtCallPosList
  bodyFullExtCallPosAggregate bodyFullExtCallPosTransport abiEncodeArgsCase
  exprSimUnwrap exprSimMemorySource exprOperandVar exprLoweringProps
  exprLowering compileEnv exprSimHyps entryCreateCompletedCut fragGasOriginPtr
  gasSummary vyperState vyperStorageFootprint vyperStorageTrace loweringPosts
  bodyMemoryDefs context

Theorem extcall_pos_retained_snapshot_site:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,si) /\
  ~exprs_can_mutate cenv (xs ++ kw_es) /\
  ~is_word_type (lowered_value_type cenv e) /\
  compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv) si = (sv,sm) /\
  local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  create_operand_at si t /\ ~t.vs_halted /\ ee.gas_obs = [] /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       storage_well_formed_on cx es (FST H)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e
       (es,sa,si,s0,vv,G0,tn0) H (INL tv) ee G tn t) ==>
  sm = si /\
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 si sm
    (read_result cx tv) (ee,t,G,tn)
    (\H res mid G' tn' u. ?v. res = INL v /\
      extcall_positional_post keep_pure DF lo d ctx func cenv cx env
        kw_es [e] [sv] sa sm es s0 G0 tn0 H (INL [v]) mid G' tn' u) R
Proof
  strip_tac >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
     lowered_value_type cenv e` by metis_tac[extcall_operand_snapshot_type] >>
  `sm = si /\ sv = ext_call_arg_value (lowered_value_type cenv e) vv` by
    gvs[compile_snapshot_vv_def, comp_return_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (Cases_on `read_result cx tv ee` >> rename1 `read_result cx tv ee = (read_res,read_state)` >>
     drule_then strip_assume_tac read_result_state >>
     Cases_on `read_res` >> gvs[] >>
     qpat_assum `!H. _ ==> create_operand_vv_post _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon ee.storage_trace`
         (drule_then (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def]))) >>
     gvs[] >> metis_tac[GEN_ALL vv_post_failed_read]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,ee)` by
    simp[bind_def] >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> strip_tac >>
  `~is_word_type (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt ==> val_wf rt v` by
    (rpt strip_tac >> qpat_assum `~is_word_type (expr_type e) ==> _`
      (drule_then strip_assume_tac) >> gvs[]) >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  `sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id` by
    metis_tac[compile_expr_extends] >>
  `local_ptrs_reserved cenv si` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand sv = Var x ==> not_fresh_at si x` by
    (`!x. vv_operand vv = Var x ==> not_fresh_at si x` by
       metis_tac[cj 1 compiler_compile_var] >>
     Cases_on `vv` >> fs[ext_call_arg_value_def, vv_operand_def]) >>
  `~exprs_can_mutate cenv kw_es` by fs[exprs_can_mutate_append] >>
  rewrite_tac[scoped_operand_outcome_def] >> simp[] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl [`INL v`,`ee`,`OK t`,`G`,`tn`] >>
  simp[create_operand_full_scope_def, create_expr_prefix_nil, gas_explicit_def,
       gas_origin_ptr_path_rules] >>
  conj_tac >- fs[create_operand_at_def] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[] >>
  qpat_assum `!H. _ ==> create_operand_vv_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def])) >>
  gvs[] >>
  `valid_horizon cx (es with gas_obs := obs) H ee.storage_trace` by
    (`valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `eval_expr cx e (es with gas_obs := _) = (INL tv,ee)`
          (mp_then Any mp_tac valid_horizon_frame) >>
        simp[cj 5 evaluate_storage_trace_frame]) >>
     `storage_well_formed_on cx es (FST H)` by metis_tac[] >>
     `storage_well_formed_on cx (es with gas_obs := obs) (FST H) <=>
      storage_well_formed_on cx es (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >>
     fs[valid_horizon_def]) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) t = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
       val_in_memory rt v (w2n w) mem)` by fs[arithmeticTheory.ADD_COMM] >>
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by simp[] >>
  `!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op G t` by simp[] >>
  drule_all (REWRITE_RULE [] (Q.INST
    [`sv` |-> `ext_call_arg_value (lowered_value_type cenv e) vv`]
    extcall_pos_aggregate_read_at)) >> strip_tac >>
  qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `return_buf_frame d cenv si t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >> simp[]) >>
  `wb_frame cenv es ee sa s0 t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `vv_store_bound cx (post_value_type cenv e) _ _ raw _ _`
    (mp_then (Pos last) mp_tac extcall_saved_physical_store_bound) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  fs[fragExecTheory.exit_result_def, extcall_positional_post_def, create_operand_at_def,
     vv_location_def, arithmeticTheory.ADD_COMM] >>
  qpat_assum `ext_call_arg_value _ _ = _` (fn eq =>
    gvs[eq, ext_call_arg_value_def] >> rpt conj_tac >>
    (qexistsl [`sa`,`si`,`si`,`vv`,`raw`] ORELSE qexistsl [`sa`,`si`,`si`,`raw`]) >>
    simp[eq])
QED
