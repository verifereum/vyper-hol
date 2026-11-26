(* Static readiness and exception propagation for ECRecover's operand list. *)
Theory bodyECRecoverOperandReadyMods
Ancestors
  exprSimPrecompiles exprBodyPreProps exprSimHypsDefs exprSimSource
  supportedExprTraverse allocLimits gasContext exprSimDefs vyperTypeCallGraph
  compileEnv vyperTypeSystem vyperInterpreter vyperValue vyperState vyperAST list

Theorem ecrecover_member_pre[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann ECRecover args) entry /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env st ==>
  expr_body_pre_mods mods ce cx env e st
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, byte_widths_expr_def,
       int_calls_expr_def, expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  `!p. supported_expr_exists p e ==>
       supported_expr_exists p (Builtin ann ECRecover args)` by
    (simp[Once supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  `alloc_limits_expr ce e` by
    (irule alloc_limits_builtin_arg >>
     qexistsl_tac [`ann`,`args`,`ECRecover`] >> simp[]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[well_typed_exprs_member]
  >- metis_tac[byte_widths_exprs_mem]
  >- metis_tac[call_evaluation_safe_exprs_mem]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[int_calls_exprs_every_mem]
QED

Theorem ecrecover_member_type[local]:
  well_typed_builtin_app ann ECRecover (MAP expr_type args) /\ MEM e args ==>
  is_word_type (expr_type e) /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv
Proof
  strip_tac >> drule ecrecover_typing >> simp[] >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute] >> gvs[is_word_type_def, evaluate_type_def]
QED

Theorem ecrecover_operand_ready_mods:
  expr_body_pre_mods mods ce cx env (Builtin ann ECRecover args) entry ==>
  well_typed_builtin_app ann ECRecover (MAP expr_type args) /\
  ann = BaseT AddressT /\ LENGTH args = 4 /\
  (!e. MEM e args ==>
     is_word_type (expr_type e) /\
     (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv) /\
     !st. expr_sim_inv_mods mods ce cx env st ==>
          expr_body_pre_mods mods ce cx env e st)
Proof
  strip_tac >>
  `well_typed_builtin_app ann ECRecover (MAP expr_type args)` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def]) >>
  `ann = BaseT AddressT /\ LENGTH args = 4` by (drule ecrecover_typing >> simp[]) >>
  simp[] >> gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac ecrecover_member_type >>
  simp[] >> rpt strip_tac >> drule_all ecrecover_member_pre >> simp[]
QED

Theorem ecrecover_operand_admissible_mods:
  LENGTH args = 4 /\
  gas_admissible (bind (eval_expr cx (Builtin ann ECRecover args))
                      (read_result cx)) expr_res_ok es ==>
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR ex => expr_res_ok (INR ex)) es
Proof
  strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[eval_expr_ecrecover_read_action, gas_admissible_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `eval_exprs cx args (es with gas_obs := gs) = (rr,ee)` >>
  Cases_on `rr` >- simp[] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED
