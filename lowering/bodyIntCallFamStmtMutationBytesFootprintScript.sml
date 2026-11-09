(* Physical bytes capacity need not equal the expression annotation's capacity. *)
Theory bodyIntCallFamStmtMutationBytesFootprint
Ancestors
  memoryLocalRhsProps valueCopyBytes exprSimHypsDefs
Libs
  monadsyntax

Theorem intcall_bytes_read_physical_footprint:
  expr_body_pre ce cx env e es /\ supported_expr tops e /\
  ce.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  is_bytestring_type (lowered_value_type ce e) /\
  is_bytestring_type dty /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  val_footprint dtv v <= type_memory_bytes ce (lowered_value_type ce e)
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (drule_all memory_rhs_read_lowered_typed >> simp[]) >>
  `value_runtime_typed env dty v` by
    (drule_all memory_rhs_read_destination_typed >> simp[]) >>
  qpat_x_assum `value_runtime_typed env dty v` mp_tac >>
  drule_all memory_rhs_runtime_layout >> strip_tac >> strip_tac >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  gvs[] >> irule bytestring_val_footprint_le >> metis_tac[]
QED
