(* Static readiness of the two EC arithmetic operands. *)
Theory bodyECArithOperandReadyMods
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimSource supportedExprTraverse
  allocLimits gasContext vyperTypeCallGraph vyperTypeSystem vyperAST list

Theorem ec_arith_member_pre[local]:
  (!n. bt <> Slice n) /\
  expr_body_pre_mods mods ce cx env (Builtin ann bt args) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env mid ==>
  expr_body_pre_mods mods ce cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, byte_widths_expr_def,
       int_calls_expr_def, expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  `!p. supported_expr_exists p e ==>
       supported_expr_exists p (Builtin ann bt args)` by
    (simp[Once supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  `alloc_limits_expr ce e` by
    (irule alloc_limits_builtin_arg >> qexistsl_tac [`ann`,`args`,`bt`] >> simp[]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[well_typed_exprs_member]
  >- metis_tac[byte_widths_exprs_mem]
  >- metis_tac[call_evaluation_safe_exprs_mem]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[int_calls_exprs_every_mem]
QED

Theorem ec_arith_operand_ready_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  expr_body_pre_mods mods ce cx env (Builtin a bt args) es ==>
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?e1 e2. args = [e1;e2] /\ expr_type e1 = a /\
    expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
    expr_body_pre_mods mods ce cx env e1 es /\
    (!mid. expr_sim_inv_mods mods ce cx env mid ==>
           expr_body_pre_mods mods ce cx env e2 mid)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n. bt <> Slice n` by
    (qpat_x_assum `bt = ECAdd \/ bt = ECMul` strip_assume_tac >> simp[]) >>
  `well_typed_builtin_app a bt (MAP expr_type args)` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def]) >>
  `LENGTH args = 2` by
    (qpat_x_assum `bt = ECAdd \/ bt = ECMul` strip_assume_tac >>
     gvs[well_typed_builtin_app_def]) >>
  `expr_sim_inv_mods mods ce cx env es` by (drule expr_body_pre_mods_inv >> simp[]) >>
  `!e mid. MEM e args /\ expr_sim_inv_mods mods ce cx env mid ==>
     expr_body_pre_mods mods ce cx env e mid` by
    (rpt strip_tac >> irule ec_arith_member_pre >> metis_tac[]) >>
  qpat_x_assum `bt = ECAdd \/ bt = ECMul` strip_assume_tac >>
  gvs[LENGTH_EQ_NUM_compute, well_typed_builtin_app_def]
QED
