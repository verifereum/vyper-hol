(* The mapping-target suffix contains only the selected key hash and slot
   computation. Its bad-storage focus stays at the index exit. *)
Theory entryCreateTargetMapping
Ancestors
  bodyFullTargetMapping bodyFullTargetMappingOutcome entryCreateSubscriptMapRun
  entryCreatePathScope entryCreateFocusSpec entryCreateCompletedCut
  exprLoweringProps exprLowering emitHelper context abiEncoderProps compileEnv
  venomInst venomExecSemantics venomState fragExec fragGasOriginPtr gasSummary
  bodyFullTargetDefs bodySimFull bodySim loweringPosts bodyPtrDefs gasContext
  vyperTypeSystem vyperTypeEnv vyperInterpreter vyperState vyperStorageFootprint
  ptrDiscipline allocaHistory list rich_list pred_set arithmetic

Theorem mapping_extension_scoped[local]:
  mapping_extension_observed (DF,lo,E,ctx,func,PG) cx st0
    source (es,s,G0,tn0) (t,G,tn) Q /\
  create_operand_full_scope a b E ctx func s [] (OK t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a b source
    (es,s,G0,tn0) Q R
Proof
  simp[mapping_extension_observed_def] >> strip_tac >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]`
  >- (disj1_tac >> simp[create_operand_focus_scope_def] >>
      metis_tac[create_expr_prefix_nil]) >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`ee`,`OK t`,`G`,`tn`] >> simp[gas_explicit_def]
QED

Theorem target_mapping_tail_scoped_cut:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (HashMapT kt vt) /\
  type_place_target env (SubscriptTarget bt e) = SOME et /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (iop, sn) /\
  compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r, sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env mid1 /\
  eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv, mid1) /\
  bind (eval_expr cx e) (read_result cx)
    (mid1 with gas_obs := index_gas) = (INL v, mid2) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2 /\
  storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
  ~t2.vs_halted /\ t2.vs_current_bb = sn.cs_current_bb /\
  t2.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func t2 /\
  s0.vs_alloca_next <= t1.vs_alloca_next /\ t1.vs_alloca_next <= t2.vs_alloca_next /\
  (!H. valid_horizon cx st0 H mid2.storage_trace ==>
    target_post H ctx func cenv cx es sa sm s0 mid1 pv (HashMapT kt vt) rb t1 /\
    ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
    target_ptr_ok cenv pv rb G1 tn1 t1 /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
    expr_store_bound cx (expr_type e) v iop t2 /\
    ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
    ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e iop G2 t2) /\
    ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 sn sb (extend_place cx pv (ValueSubscript v)) (mid2,t2,G2,tn2)
    (\H res ee G tn t. ?pv'. res = INL pv' /\
      target_post H ctx func cenv cx es sa sb s0 ee pv' et r t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\ target_ptr_ok cenv pv' r G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt q. expr_exit res q) /\
  create_operand_cut sn sb (gas_explicit_sites ctx shadow_ctx) ctx func (cx_tops cx) cx st0
    (extend_place cx pv (ValueSubscript v)) (mid2,t2)
Proof
  strip_tac >> drule_all target_mapping_tail_observed >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  `create_operand_at sn t2` by simp[create_operand_at_def] >>
  conj_tac
  >- (irule mapping_extension_scoped >> first_assum (irule_at Any) >>
      irule mapping_suffix_raw_scope >> metis_tac[]) >>
  irule mapping_suffix_visit_inventory >> metis_tac[]
QED
