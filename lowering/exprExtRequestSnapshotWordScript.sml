(* Word snapshots retain a safe operand, not a fabricated producer post. *)
Theory exprExtRequestSnapshotWord
Ancestors
  exprExtRequestSnapshotProbe exprExtRequestJointUnwrap exprSafeOperand
  exprExtRequestHistory gasSummary loweringPosts exprLowering compileEnv
  bodyIntCallCompilerTags context exprSimMemorySource abiEncodeArgsSim exprSimHyps
  exprExtRequestReconstruct aggregateEvaluatedLayout

Theorem extrequest_snapshot_word_endpoint:
  unwrap_value cenv vv sn = (op,sb) /\
  is_word_type (lowered_value_type cenv e) /\ ~expr_has_effect e /\
  compile_expr cenv ty e sa = (vv,sc) /\
  expr_body_pre cenv cx env e es /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  read_result cx r ee = (INL v,ee) /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ee t /\
  (case vv of StackValue ty a => safe_operand sc a
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?u. compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) sn =
        (StackValue (lowered_value_type cenv e) op,sb) /\
    gas_marked_exec F (ctx,func) (read_result cx r) (ee,t)
      [] (INL v) ee (OK u) /\
    expr_val_rel cx (expr_type e) v op u /\ safe_operand sb op /\
    stmt_state_rel ctx func cenv cx ee u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k u.vs_memory = mem_bytes_at p k t.vs_memory) /\
    extrequest_history_frame cenv cx ee sn t ee sb u
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by
    (metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type]) >>
  `lowered_value_type cenv e = expr_type e` by
    (metis_tac[expr_body_pre_lowered_fits, abi_args_word_fits_eq]) >>
  `vv_type vv = expr_type e` by
    (drule intcall_compile_expr_tag >>
     disch_then (qspecl_then [`ty`, `sa`, `cenv`] mp_tac) >> simp[]) >>
  `ext_call_arg_value (expr_type e) vv = vv` by
    (Cases_on `vv` >> gvs[vv_type_def, ext_call_arg_value_def]) >>
  `compile_snapshot_vv cenv copy vv sn = (StackValue (expr_type e) op,sb)` by
    (metis_tac[extrequest_snapshot_word]) >>
  `word_result_ok sn vv` by
    (Cases_on `vv` >> gvs[word_result_ok_def, vv_type_def] >>
     fs[extrequest_history_frame_def] >>
     metis_tac[exprSafeOperandTheory.safe_operand_mono]) >>
  `safe_operand sb op` by (drule_all unwrap_value_safe_operand >> simp[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    extrequest_joint_unwrap_read >> simp[] >>
  disch_then (qspecl_then [`t`, `sn`, `sb`, `op`, `ee`] mp_tac) >>
  simp[] >> strip_tac >>
  `v' = v` by
    (gvs[gas_marked_exec_def] >>
     qpat_x_assum `!tail. read_result _ _ _ = _`
       (qspec_then `ee.gas_obs` mp_tac) >> simp[]) >>
  qexists_tac `u` >> gvs[expr_post_def] >> metis_tac[]
QED

Theorem extrequest_snapshot_word_history:
  is_word_type ty /\ expr_val_rel cx ty v op t /\ safe_operand sc op /\
  extrequest_history_frame cenv cx es sc t es' sn t' ==>
  expr_val_rel cx ty v op t' /\ safe_operand sn op
Proof
  strip_tac >>
  `safe_operand sn op` by
    (fs[extrequest_history_frame_def] >>
     metis_tac[exprSafeOperandTheory.safe_operand_mono]) >>
  gvs[expr_val_rel_def] >>
  drule_all extrequest_history_operand >>
  metis_tac[]
QED
