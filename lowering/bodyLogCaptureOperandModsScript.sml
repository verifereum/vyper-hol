(* Static operand safety for a typed captured Log argument. *)
Theory bodyLogCaptureOperandMods
Ancestors
  exprBodyPreProps exprSimHypsDefs exprReasonOperand exprSafeOperand
  abiBuiltinAllocation loweringShapeRules exprLowering compileEnv context

Theorem log_capture_operand_not_label_mods:
  expr_body_pre_mods mods ce cx env e entry /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) ==>
  !l. vv_operand sv <> Label l
Proof
  strip_tac >>
  `!l. vv_operand vv <> Label l` by
    (drule expr_body_pre_mods_well_typed >> strip_tac >>
     drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def] >> strip_tac >>
     drule_all compile_expr_reason_uniform >>
     disch_then (qspec_then `expr_type e` mp_tac) >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum drule >> Cases_on `vv` >>
     simp[reason_result_shape_def,vv_operand_def]) >>
  `vv_operand (ext_call_arg_value (lowered_value_type ce e) vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def,vv_operand_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def] >> IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[comp_return_def] >>
      strip_tac >> gvs[vv_operand_def] >> drule unwrap_value_not_label >> simp[]) >>
  Cases_on `copy` >> simp[comp_bind_def,comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[vv_operand_def,mk_ptr_def] >>
      qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
      simp[compile_materialize_vv_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      drule abi_builtin_alloc_buffer_shape >> simp[emit_op_eq]) >>
  strip_tac >> gvs[]
QED
