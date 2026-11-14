(* Exact frozen-cut diagnostic boundary. No additional representation premise. *)
Theory bodyFullTargetArraySuffix
Ancestors
  bodyFullTargetSubscript bodyFullTargetArraySource bodyFullTargetArrayLoad
  bodyFullTargetArrayScalar bodyFullTargetAttribute targetSubscriptMemory
  targetSubscriptStorage bodyPtrDefs loweringPosts freshWrites
  finite_map pair list bodyFullTargetDefs venomState ptrDiscipline exprLoweringProps
  targetSubscriptSplit bodyPtrBopInMemoryContents vyperTypeSystem
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants vyperTyping
  vyperValue compileEnv valueEncoding vyperTypeEnv

Definition array_tail_packet_def:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 <=>
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  type_place_target env (SubscriptTarget bt e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (iop, sn) /\
  compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r, sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env mid1 /\ mid1.gas_obs = [] /\
  eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv, mid1) /\
  bind (eval_expr cx e) (read_result cx)
    (mid1 with gas_obs := index_gas) = (INL v, mid2) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2 /\
  storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
  ~t1.vs_halted /\ ~t2.vs_halted /\
  t1.vs_current_bb = sm.cs_current_bb /\
  t1.vs_inst_idx = LENGTH sm.cs_current_insts /\
  t2.vs_current_bb = sn.cs_current_bb /\
  t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history func t1 /\ alloca_history func t2 /\
  s0.vs_alloca_next <= t1.vs_alloca_next /\
  t1.vs_alloca_next <= t2.vs_alloca_next /\
  (!H. valid_horizon cx st0 H mid2.storage_trace ==>
    target_post H ctx func cenv cx es sa sm s0 mid1 pv (Type (ArrayT et bd)) rb t1 /\
    ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
    target_ptr_ok cenv pv rb G1 tn1 t1 /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
    expr_store_bound cx (expr_type e) v iop t2 /\
    ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
    ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e iop G2 t2) /\
    ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2)
End

Theorem array_tail_packet_base_at_index[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  ?w. eval_operand (FST rb) t2 = SOME w /\
      place_ptr_rel cenv cx t2 pv w (FST (SND rb)) (Type (ArrayT et bd)) /\
      op_taint tn2 (FST rb) = {} /\
      op_prov G2 (FST rb) = op_prov G1 (FST rb)
Proof
  simp[array_tail_packet_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[target_post_def] >> strip_tac >>
  `place_ptr_rel cenv cx t2 pv w (FST (SND rb)) (Type (ArrayT et bd))` by
    (irule target_place_ptr_values_frame >> qexistsl [`t1`, `sm`] >>
     fs[expr_post_def]) >>
  `!lbl. FST rb <> Label lbl` by
    metis_tac[target_subscript_typed_base_not_label] >>
  Cases_on `FST rb` >> gvs[eval_operand_def, target_ptr_ok_def,
    op_taint_def, op_prov_def, ghost_kept_at_def, expr_post_def] >>
  metis_tac[]
QED

(* Diagnostic: robust root layout supplies a clean current nested header. *)
Theorem array_tail_robust_path_header_clean[local]:
  !path tv a vs off mem k etv cap tn.
    value_has_type tv a /\ well_formed_type_value tv /\
    (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv a off m) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic cap)) ==>
    mem_word_taint tn.t_mem (off + k) = {}
Proof
  rpt strip_tac >> irule dynarray_memory_header_clean >>
  qexistsl_tac [`cap`, `mem`, `etv`, `vs`] >>
  metis_tac[mem_path_offset_current_value]
QED

Theorem array_tail_packet_source_index:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  expr_sim_inv cenv cx env mid2 /\
  stmt_state_rel H ctx func cenv cx mid2 t2 /\
  ?i iw. v = IntV i /\ eval_operand iop t2 = SOME iw /\
    i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw))
Proof
  simp[array_tail_packet_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all target_array_source_cases >> strip_tac >>
  simp[] >> conj_tac >- fs[expr_post_def] >>
  `is_int_type (expr_type e)` by
    gvs[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()] >>
  fs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  Cases_on `expr_type e` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT ity)` >> Cases_on `ity` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def] >>
  fs[expr_post_def, expr_val_rel_def, evaluate_type_def, AllCaseEqs(),
     is_word_type_def, typed_val_to_w256_def, val_to_w256_def,
     post_value_type_def] >>
  mp_tac exprSimArithTheory.math_val_i2w >>
  disch_then (qspec_then `expr_type e` (qspec_then `i` mp_tac)) >>
  gvs[arithmeticPropsTheory.math_val_def, is_signed_type_def,
      type_bits_def, within_int_bound_def]
QED
