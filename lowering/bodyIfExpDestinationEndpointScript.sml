(* Destination-indexed endpoints for selected conditional arms. *)
Theory bodyIfExpDestinationEndpoint
Ancestors
  bodyIfExpAggregateEndpoint bodyIfExpNormalizationSuffix bodyIfExpWidenedTyping
  bodyIfExpSelectedEndpoint bodyIfExpMemory exprSimIfExp exprLowering
  bodyIfExpArmLayout bodySim gasSummary vyperState stmtReasonVvMemory

Theorem ifexp_compiled_arm_assign_phi[local]:
  ~is_word_type dty /\ ~is_bytestring_type dty /\ sty <> dty /\
  ~same_memory_layout ce sty dty /\
  (?src. unwrap_value ce vv = compileEnv$comp_return src) /\
  compile_ifexp_arm ce dty sty vv sa = (op,sb) /\
  emit_inst ASSIGN [op] [rv] sb = ((),sc) /\
  fn_has_code sb sc func ==>
  !buf sm. compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf,sm) ==>
    emitted_blocks sm sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def, contextTheory.compile_store_memory_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  irule ifexp_typed_normalization_assign_exit_phi >>
  metis_tac[]
QED

Theorem ifexp_compiled_aggregate_assign_phi:
  compile_expr ce ty e se = (vv,sa) /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  ~is_word_type (lowered_value_type ce e) /\
  lowered_value_type ce e <> expr_type e /\
  ~same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  emit_inst ASSIGN [op] [rv] sb = ((),sc) /\
  fn_has_code sb sc func ==>
  !buf sm. compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sa = (buf,sm) ==>
    emitted_blocks sm sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `?src. unwrap_value ce vv = compileEnv$comp_return src` by
    (irule ifexp_different_type_unwrap_pure >> metis_tac[]) >>
  metis_tac[ifexp_compiled_arm_assign_phi]
QED

Theorem ifexp_compiled_same_layout_endpoint:
  compile_expr ce ty e se = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  lowered_value_type ce e <> expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  post_value_type ce e = lowered_value_type ce e /\
  same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dtv /\
  0 < type_memory_size stv /\ value_has_type dtv v /\ val_wf dtv v /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s ==>
  sb = sa /\
  expr_post ctx func ce cx (IfExp (expr_type e) c a b) es origin sb s0 ee v op s /\
  vv_store_bound cx (expr_type e) (expr_type e) ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  `?src sw. unwrap_value ce vv = compileEnv$comp_return src /\
     src = vv_operand vv /\
     expr_post ctx func ce cx e es origin sa s0 ee v src s /\
     eval_operand src s = SOME sw /\
     w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (irule bodyIfExpCompiledAggregateTheory.ifexp_compiled_aggregate_source >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[compile_ifexp_arm_def, compileEnvTheory.comp_return_def] >>
  conj_tac
  >- (irule ifexp_post_annotated >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `val_store_size dtv v <= type_memory_size dtv` by
    (irule exprSimPropsTheory.val_store_size_le >> simp[]) >>
  simp[exprSimMemDefsTheory.vv_store_bound_def, contextTheory.mk_ptr_def] >>
  rpt strip_tac >> gvs[] >>
  `type_memory_size dtv <= type_memory_size stv` by
    (`type_memory_size dtv = type_memory_size stv` by
       (fs[contextTheory.same_memory_layout_def] >> metis_tac[]) >> simp[]) >>
  decide_tac
QED

Theorem ifexp_selected_destination_marked_endpoint_mem:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  ~is_word_type (expr_type e) /\
  compile_expr ce ty e se = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  emit_inst ASSIGN [op] [rv] sb = ((),sc) /\
  stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce se /\ local_ptrs_reserved ce origin /\
  local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  vv_post ctx func ce cx e es origin sa s0 (ee with gas_obs := []) raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e)
    (ee with gas_obs := []) raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?right tv v u.
    gas_marked_exec T (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) right (INL tv) (ee with gas_obs := []) (OK u) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx func ce cx (IfExp (expr_type e) c a b) es origin sb s0
      (ee with gas_obs := []) v op u /\
    vv_store_bound cx (expr_type e) (expr_type e) (ee with gas_obs := []) tv
      (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule stmtReasonVvMemoryTheory.vv_post_read_ok >> strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by simp[vyperStateTheory.bind_def] >>
  Cases_on `post_value_type ce e = expr_type e`
  >- suspend "normal" >>
  suspend "physical"
QED

Resume ifexp_selected_destination_marked_endpoint_mem[normal]:
  `!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     type_memory_bytes ce (expr_type e) = type_memory_size tv /\
     type_memory_size tv < 2 ** 64` by
    (rpt strip_tac >> drule exprSimHypsTheory.expr_body_pre_copy_ok >>
     simp[] >> metis_tac[]) >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
   env.type_defs = get_tenv cx` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def,
        exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule exprSimSourceTheory.expr_body_pre_var_types_well_formed >> strip_tac >>
  `~same_memory_layout ce (lowered_value_type ce e) (expr_type e) ==>
     is_bytestring_type (expr_type e)` by
    (Cases_on `is_bytestring_type (expr_type e)` >> simp[] >>
     drule_all exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
     strip_tac
     >- metis_tac[ifexp_copy_types] >>
     gvs[vyperASTTheory.expr_type_def, loweringPostsTheory.post_value_type_def] >>
     metis_tac[ifexp_copy_types]) >>
  `!tv. same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     ?avt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME avt /\
       type_memory_size tv <= type_memory_size avt` by
    metis_tac[ifexp_body_arm_runtime_sizes] >>
  drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)
    ifexp_selected_marked_endpoint_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      irule ifexp_body_pre_read_typed >>
      qexistsl [`ce`, `env`, `es with gas_obs := gs`, `st`] >>
      reverse conj_tac >- simp[exprSimHypsDefsTheory.expr_body_pre_def] >>
      gvs[vyperStateTheory.bind_def]) >>
  strip_tac >>
  qexistsl [`[]`, `tv`, `v'`, `u`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[loweringPostsTheory.expr_post_def, vyperASTTheory.expr_type_def] >> metis_tac[]) >>
  qpat_x_assum `gas_marked_exec _ _ (conditional_result _ _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
  metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_not_halted,
            fragGasModeTheory.gas_marked_path_def]
QED

Resume ifexp_selected_destination_marked_endpoint_mem[physical]:
  `~is_bytestring_type (expr_type e)` by
    metis_tac[loweringPostsTheory.post_value_type_bytestring] >>
  `expr_body_pre ce cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[exprSimHypsDefsTheory.expr_body_pre_def] >>
  drule_at (Pat `expr_body_pre _ _ _ _ _`) ifexp_aggregate_source_typing >>
  disch_then (qspecl_then [`v`, `ee with gas_obs := []`] mp_tac) >>
  impl_tac >- gvs[vyperStateTheory.bind_def] >> strip_tac >>
  `0 < type_memory_size stv` by
    (irule ifexp_physical_source_positive >> metis_tac[]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    gvs[vyperTypeSystemTheory.type_widens_to_def] >>
  `~is_word_type (lowered_value_type ce e) /\
   ~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[ifexp_aggregate_source_kind] >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size,
              exprSimHypsDefsTheory.expr_body_pre_def] >>
  Cases_on `same_memory_layout ce (lowered_value_type ce e) (expr_type e)`
  >- suspend "same" >>
  suspend "aggregate"
QED
Resume ifexp_selected_destination_marked_endpoint_mem[same]:
  drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)
    ifexp_compiled_same_layout_endpoint >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (expr_type _) = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (lowered_value_type _ _) = _`)) >>
  disch_then (qspecl_then [`c`, `b`, `a`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >> gvs[] >>
  `gas_marked_exec T (ctx,func) (read_result cx raw)
     (ee with gas_obs := [],s) [] (INL v) (ee with gas_obs := []) (OK s)` by
    (simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     conj_tac
     >- (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
     irule (cj 1 fragGasPathMemTheory.gas_path_mem_rules) >> simp[]) >>
  drule_all ifexp_marked_conditional_of_read_mem >> strip_tac >>
  qexistsl [`[]`, `tv`, `v`, `s`] >> simp[] >>
  fs[exprSimMemDefsTheory.vv_store_bound_def] >> metis_tac[]
QED
Resume ifexp_selected_destination_marked_endpoint_mem[aggregate]:
  `type_memory_bytes ce (expr_type e) = type_memory_size dtv /\
   type_memory_size dtv < 2 ** 64` by
    metis_tac[exprSimHypsTheory.expr_body_pre_copy_ok] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by fs[bodySimTheory.body_inv_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)
    ifexp_compiled_aggregate_marked_endpoint_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (expr_type _) = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (lowered_value_type _ _) = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`c`, `b`, `a`] mp_tac) >>
  impl_tac >- suspend "aggregate_premises" >>
  strip_tac >> qexistsl [`REPLICATE n F`, `tv`, `v`, `u`] >> simp[]
QED
Resume ifexp_selected_destination_marked_endpoint_mem[aggregate_premises]:
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- (simp[wordsTheory.dimword_def] >> gvs[]) >>
  conj_tac
  >- fs[exprSimHypsDefsTheory.expr_body_pre_def,
        exprSimHypsDefsTheory.expr_sim_inv_def] >>
  metis_tac[ifexp_compiled_aggregate_assign_phi]
QED
Finalise ifexp_selected_destination_marked_endpoint_mem
