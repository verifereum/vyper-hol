(* Store effects for internal memory returns, before exit composition. *)
Theory bodyIntCallMemoryStoreEffect
Ancestors
  bodyIntCallFamStmtReturnMemoryEndpoint bodyIntCallFamStmtReturnBytesEffect
  bodyIntCallFamStmtReturnTypes bodyIntCallFamStmtReturnEndpointTypes
  bodyIntCallJointStmtBoundary bodyIntCallJointContract bodyIntCallCopySharpRank
  exprSimHyps exprSimHypsDefs exprSimDefs loweringPosts stmtLowering
  exprLoweringProps compileEnv typedMemoryCopy vyperTypeInvariants
  valueEncodingTyping fragExec exprSimSource context placeMemoryCopyEffect
  bodyIntCallFamStmtReturnStoreEffect loweringStateRelDefs annassignRelayoutBounds

Theorem compound_return_store_effect:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  fp.jc_rb = SOME (bw,cap) /\
  type_widens_to (get_tenv fp.jc_cx) sty fp.jc_ret_ty /\
  evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  value_has_type fp.jc_ret_tv v /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  regions_disjoint (w2n sw) (type_memory_size stv) (w2n bw) cap /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  compile_store_memory ce src dst fp.jc_ret_ty sty su = ((),sm) /\
  ~is_word_type fp.jc_ret_ty /\ ~is_bytestring_type fp.jc_ret_ty /\
  (sty = fp.jc_ret_ty ==> type_memory_size fp.jc_ret_tv + 64 < dimword (:256)) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  eval_operand dst u = SOME bw /\ eval_operand src u = SOME sw /\
  fn_has_code su sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
  u.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?t. val_in_memory fp.jc_ret_tv v (w2n bw) t.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func su sm u t (w2n bw) cap
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  drule_all intcall_copy_metadata >> strip_tac >>
  `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv /\
   cap = type_memory_size fp.jc_ret_tv` by
    (fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `w2n bw + cap < dimword (:256)` by
    (irule intcall_return_buffer_bound >> metis_tac[]) >>
  Cases_on `sty = fp.jc_ret_ty`
  >- (gvs[] >>
      SUBGOAL_THEN ``fp.jc_ret_ty = fp.jc_ret_ty \/
        is_bytestring_type fp.jc_ret_ty /\ is_bytestring_type fp.jc_ret_ty`` assume_tac
      >- simp[] >>
      `type_memory_bytes ce fp.jc_ret_ty = type_memory_size fp.jc_ret_tv` by metis_tac[] >>
      `(if is_word_type fp.jc_ret_ty then sw = typed_val_to_w256 fp.jc_ret_tv v
        else val_in_memory fp.jc_ret_tv v (w2n sw) u.vs_memory)` by simp[] >>
      drule_all compatible_store_effect >>
      disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
      qexists_tac `t` >> simp[] >>
      irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> irule compile_store_memory_relayout_effect >> simp[] >>
  conj_tac >- metis_tac[value_has_type_val_wf] >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw`, `get_tenv fp.jc_cx`] >>
  fs[regions_disjoint_def] >> metis_tac[value_has_type_val_wf]
QED

Theorem intcall_memory_store_effect:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es0 /\
  type_widens_to env.type_defs (expr_type e) fp.jc_ret_ty /\
  fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_returns_count = 0 /\
  fp.jc_ret_ty <> NoneT /\ ~is_word_type fp.jc_ret_ty /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\ value_has_type fp.jc_ret_tv v /\
  expr_val_rel fp.jc_cx (post_value_type ce e) v op s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME bw /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) ==>
   ?w a k. eval_operand op s = SOME w /\ a <= w2n w /\
     w2n w + type_memory_size tv <= a + k /\ a + k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  ci_mono sa su /\ u.vs_memory = s.vs_memory /\
  (!p. eval_operand p u = eval_operand p s) /\
  compile_store_memory ce op dst fp.jc_ret_ty (lowered_value_type ce e) su = ((),sm) /\
  fn_has_code su sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
  u.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?t. val_in_memory fp.jc_ret_tv v (w2n bw) t.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func su sm u t (w2n bw) cap
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es0 /\ well_typed_expr env e /\
   alloc_limits_expr ce e` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  drule_all return_post_type_widens >> strip_tac >>
  `~is_word_type (post_value_type ce e)` by metis_tac[type_widens_from_word] >>
  `?sw. eval_operand op s = SOME sw /\
     val_in_memory tv v (w2n sw) s.vs_memory` by fs[expr_val_rel_def] >>
  `(!x. op = Var x ==> not_fresh_at su x) /\
   (!x. dst = Var x ==> not_fresh_at su x)` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  Cases_on `is_bytestring_type fp.jc_ret_ty`
  >- (`is_bytestring_type (expr_type e)` by metis_tac[typed_copy_bytestring_source] >>
      `post_value_type ce e = expr_type e` by simp[] >>
      `is_bytestring_type (post_value_type ce e)` by simp[] >>
      `type_alloc_ok ce (post_value_type ce e)` by metis_tac[alloc_limits_expr_type_alloc_ok] >>
      drule_all intcall_type_alloc_headroom >> strip_tac >>
      drule_all expr_sim_inv_memory_size >> strip_tac >>
      `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv /\
       cap = type_memory_size fp.jc_ret_tv` by (fs[intcall_frame_ok_def] >> metis_tac[]) >>
      gvs[] >> irule bytestring_store_effect >> simp[] >>
      goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
      qexistsl_tac [`post_value_type ce e`, `tv`, `sw`, `get_tenv fp.jc_cx`] >> simp[]) >>
  `post_value_type ce e <> NoneT /\ ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_NoneT, type_widens_from_bytestring] >>
  qpat_x_assum `post_value_type ce e <> NoneT /\ _ ==> _` mp_tac >>
  simp[] >> strip_tac >> gvs[] >>
  `regions_disjoint (w2n sw) (type_memory_size tv) (w2n bw) cap` by
    (irule intcall_return_buffer_source_disjoint >>
     goal_assum (drule_at Any) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `w2n sw + type_memory_size tv < dimword (:256)` by decide_tac >>
  `post_value_type ce e = fp.jc_ret_ty ==>
   type_memory_size fp.jc_ret_tv + 64 < dimword (:256)` by
    (strip_tac >> irule return_post_equal_headroom >>
     goal_assum (drule_at Any) >> fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `(!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t) /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    (conj_tac >- metis_tac[expr_body_pre_var_types_well_formed] >>
     drule_all intcall_copy_metadata >> simp[]) >>
  drule return_store_post_type >>
  disch_then (qspecl_then [`op`, `fp.jc_ret_ty`, `dst`, `ce`] mp_tac) >>
  simp[] >> disch_then (mp_tac o SRULE []) >>
  (impl_tac >- metis_tac[]) >> disch_tac >>
  irule compound_return_store_effect >> simp[] >>
  goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
  qexistsl_tac [`dst`, `op`, `tv`, `post_value_type ce e`, `sw`] >> simp[] >>
  metis_tac[]
QED
