(* A reached false assertion starts its synthetic Raise at the condition's
   forced-read endpoint. Keep the raw success for the evaluator's child rule. *)
Theory bodyAssertPayloadSourceMods
Ancestors
  bodyWriteSubscriptSourceMods bodyBranchCellFrameMods bodyQualifiedStmtSupport
  bodySim allocLimits compileVyper supportedStmts supportedStmtTraverse
  vyperInterpreter vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperSubscriptOverlap vyperState list finite_map

Theorem assert_false_read_source_mods[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\ mid.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV F), mid with gas_obs := tail)) ==>
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  (?tv st. eval_expr cx e (es with gas_obs := xs) = (INL tv,st) /\
           read_result cx tv st = (INL (BoolV F),mid))
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) =
   (INL (BoolV F),mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := xs)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := xs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  simp[] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs(), PULL_EXISTS]
QED

Theorem assert_payload_false_source_ready_mods:
  ((?r. ak = AssertReason r /\ rr = RaiseReason r) \/
   (?err. ak = AssertCustomError err /\ rr = RaiseCustomError err)) /\
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\ mid.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV F), mid with gas_obs := tail)) /\
  supported_stmt tops bindings (Assert e ak) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assert e ak) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  type_stmt env ret_ty (Assert e ak) = SOME env' /\
  stmt_exprs_ok cenv (Assert e ak) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (Assert e ak) /\
  (!key. MEM (WriteAcc (StateRef key)) (accesses_stmt (Assert e ak)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e ak)) /\
  EVERY P (int_calls_stmt (Assert e ak)) ==>
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  (?tv st. eval_expr cx e (es with gas_obs := xs) = (INL tv,st) /\
           read_result cx tv st = (INL (BoolV F),mid)) /\
  supported_stmt tops bindings (Raise rr) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Raise rr) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  type_stmt env ret_ty (Raise rr) = SOME env /\
  stmt_exprs_ok cenv (Raise rr) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (Raise rr) /\
  (!key. MEM (WriteAcc (StateRef key)) (accesses_stmt (Raise rr)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise rr)) /\
  EVERY P (int_calls_stmt (Raise rr)) /\
  (qualified_stmt_decls_ok mods (Assert e ak) ==> qualified_stmt_decls_ok mods (Raise rr))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "payload") strip_assume_tac) >>
  drule_all_then strip_assume_tac assert_false_read_source_mods >>
  asm_x "payload" strip_assume_tac >>
  gvs[supported_stmt_def, supported_assert_reason_def, supported_raise_reason_def,
      supported_stmt_expr_exists_def, supported_assert_exists_def, supported_raise_exists_def,
      type_stmt_def, AllCaseEqs(),
      stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_assert_def,
      alloc_limits_raise_def, stmt_valued_return_def, qualified_stmt_decls_ok_def,
      accesses_stmt_def, accesses_assert_reason_def, accesses_raise_reason_def,
      int_calls_stmt_def, int_calls_assert_reason_def, int_calls_raise_reason_def] >>
  rpt conj_tac >> rpt strip_tac >>
  metis_tac[call_evaluation_safe_append_right]
QED
