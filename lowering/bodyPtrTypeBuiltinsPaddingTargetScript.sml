(* Target-lifting probes; no claim of a complete counterexample. *)
Theory bodyPtrTypeBuiltinsPaddingTarget
Ancestors
  bodyPtrTypeBuiltinsPaddingWitness bodyPtrPreds exprSimPtr exprSimSource
  vyperTypeCallGraph fragGasPathPtr ptrSafeRun ptrDiscipline venomInst

Theorem padding_operand_universal:
  body_exprs_ptr_ok cx [Name (BaseT (BytesT (Dynamic 1))) "x"]
Proof
  simp[body_exprs_ptr_ok_def, body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Name (BaseT (BytesT (Dynamic 1))) "x") es` by
    (simp[expr_sim_pre_body] >> gvs[int_calls_expr_def]) >>
  metis_tac[leaf_expr_sim_ptr]
QED

Theorem padding_actual_mul_edge_forbidden:
  s.vs_current_bb = padding_runtime_label /\ s.vs_inst_idx = 8 /\
  op_taint tn (Var "%10") <> {} ==>
  ~gas_path_ptr_edge D lo ctx padding_runtime_function PG G tn s n G' tn' r
Proof
  strip_tac >> strip_tac >>
  fs[gas_path_ptr_edge_def, padding_runtime_function_equation,
     mk_raw_function_def, lookup_block_def, listTheory.FIND_def,
     listTheory.INDEX_FIND_def, get_instruction_def] >>
  gvs[] >>
  qpat_x_assum `ptr_safe_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_safe_step_def, ptr_inst_ok_def, taint_ok_def] >> metis_tac[]
QED
