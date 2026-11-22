(* Snapshotting an ABI operand preserves exclusion of label operands. *)
Theory abiEncodeSnapshotOperandProps
Ancestors
  abiBuiltinAllocation exprSafeOperand loweringShapeRules exprLowering
  context compileEnv venomInst pair
Libs pairLib

Theorem abi_snapshot_operand_not_label:
  (!l. vv_operand vv <> Label l) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (sv,ss) ==>
  !l. vv_operand sv <> Label l
Proof
  strip_tac >>
  `vv_operand (ext_call_arg_value ty vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def, vv_operand_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def] >> IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[comp_return_def] >>
      strip_tac >> gvs[vv_operand_def] >> drule unwrap_value_not_label >> simp[]) >>
  Cases_on `copy` >> simp[comp_bind_def, comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
      qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
      simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      drule abi_builtin_alloc_buffer_shape >> simp[emit_op_eq]) >>
  strip_tac >> gvs[]
QED
