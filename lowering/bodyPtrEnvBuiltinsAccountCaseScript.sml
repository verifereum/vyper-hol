(* Account family consumer boundaries. *)
Theory bodyPtrEnvBuiltinsAccountCase
Ancestors bodyPtrEnvBuiltinsEntryFrame bodyPtrEnvBuiltinsAccounts bodyPtrEnvBuiltinsAccountOperand
  bodyPtrEnvBuiltinsOperandCompose bodyPtrEnvBuiltinsBoundary bodyPtrEnvBuiltinsMethodTyping
  exprSimAccounts exprSimUnopProps exprSimUnopComposeProps
  exprSimWordArgs exprSimSource exprSimHypsDefs exprSimProps
  exprLowering exprLoweringProps exprOperandVar freshWrites bodyPtrEnvBuiltinsCodeProbe
  bodyPtrDefs bodyPtrPreds gasSummaryComposePtr fragGasPathPtr gasSummary gasExemptCert
  vyperTypeBuiltins vyperTypeSystem vyperInterpreter vyperValue vyperState
  builtinSimple vyperTypeInvariants vyperContext vyperTyping vyperAST
  compileEnv context loweringPosts venomState venomInst finite_map list fragExec exprSimHyps

Theorem account_suffix_extends:
  (case item of
     Balance => emit_op BALANCE [arg]
   | Codesize => emit_op EXTCODESIZE [arg]
   | Codehash => emit_op EXTCODEHASH [arg]
   | IsContract => comp_bind (emit_op EXTCODESIZE [arg]) (\c. emit_op GT [c; Lit 0w])
   | Address => comp_return arg
   | Code => comp_return arg) sm = (op,sb) ==>
  cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `item` >> simp[comp_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends_next_var >>
  metis_tac[cs_extends_refl, cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem account_source_result:
  LENGTH bs = 20 /\ accounts_well_typed es.accounts /\
  evaluate_type (get_tenv cx) (account_item_type item) = SOME tv ==>
  unop_result cx (account_item_type item) (Acc item) tys (BytesV bs) es =
    INL (evaluate_account_op item bs (lookup_account (word_of_bytes_be bs) es.accounts)) /\
  value_has_type tv
    (evaluate_account_op item bs (lookup_account (word_of_bytes_be bs) es.accounts))
Proof
  strip_tac >> conj_tac
  >- simp[unop_result_def, evaluate_builtin_def] >>
  irule (Q.INST [`addr_v` |-> `BytesV bs`] account_well_typed_op |> SRULE []) >>
  simp[value_has_type_def] >> conj_tac
  >- gvs[accounts_well_typed_def] >>
  qexists_tac `get_tenv cx` >> simp[]
QED

Theorem account_singleton_sim_ptr:
  item <> Code /\
  expr_body_pre cenv cx env (Builtin (account_item_type item) (Acc item) [e]) es /\
  expr_sim_ptr d ctx PG fn cenv cx (BaseT AddressT) e es ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (Builtin (account_item_type item) (Acc item) [e]) es
Proof
  strip_tac >> drule account_body_pre_args >> strip_tac >> gvs[] >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_acc >> strip_tac >>
  drule account_suffix_extends >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> goal_assum (drule_at Any) >>
     simp[builtin_args_length_ok_def, precompile_builtin_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `bind (eval_expr cx (Builtin (account_item_type item) (Acc item) [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v ee. (unop_result cx (account_item_type item) (Acc item) [expr_type e] v ee,ee))` by
    (irule eval_expr_unop_action_general >>
     simp[builtin_args_length_ok_def, precompile_builtin_def]) >>
  pop_assum SUBST1_TAC >> irule scalar_suffix_outcome_compose >>
  conj_tac
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]) >>
  goal_assum (drule_at Any) >>
  suspend "normal"
QED

Resume account_singleton_sim_ptr[normal]:
  rpt strip_tac >> gvs[] >>
  drule_all method_id_marked_operand_facts >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,ee with gas_obs := [])` by
    (gvs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >> strip_tac >>
  `accounts_well_typed ee.accounts` by
    gvs[expr_sim_inv_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  `?tv. evaluate_type (get_tenv cx) (account_item_type item) = SOME tv` by
    (Cases_on `item` >> gvs[account_item_type_def, evaluate_type_def]) >>
  `eval_operand x t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV l))` by
    (gvs[expr_post_def, expr_val_rel_def, is_word_type_def, evaluate_type_def] >> metis_tac[]) >>
  `op_taint tn x = {} /\ op_prov G x = NONE` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  `local_ptrs_rel fn cenv (ee with gas_obs := []).scopes t` by
    (gvs[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
  `local_ptrs_rel fn cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `stmt_state_rel ctx fn cenv cx ee t` by
    gvs[expr_post_def] >>
  fs[] >>
  drule_at (Pat `bind _ _ _ = _`) operand_account_suffix_run >>
  simp[expr_post_entry_gas_obs, ghost_kept_entry_gas_obs] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule_all account_source_result >> strip_tac >>
  qexistsl_tac [`INL (evaluate_account_op item l
    (lookup_account (word_of_bytes_be l) ee.accounts))`, `ee`, `G''`, `tn''`, `t'`] >>
  simp[unop_result_gas_obs, expr_type_def, account_item_type_word] >>
  conj_tac >- suspend "post" >>
  simp[ptr_val_ok_def, account_item_type_word]
QED
Resume account_singleton_sim_ptr[post]:
  rpt strip_tac >> irule expr_post_unop >>
  simp[account_item_type_word] >>
  conj_tac
  >- (simp[expr_val_rel_def, account_item_type_word] >>
      goal_assum (drule_at Any) >> simp[]) >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise account_singleton_sim_ptr

Theorem body_account_ptr_case:
  (!s'' x t.
     type_check (builtin_args_length_ok (Acc item) (LENGTH args)) "Builtin args" s'' =
       (INL x,t) ==> body_exprs_ptr_ok cx args) ==>
  body_expr_ptr_ok cx (Builtin ann (Acc item) args)
Proof
  strip_tac >> Cases_on `item = Code` >- gvs[body_code_ptr_case] >>
  irule body_expr_ptr_stack >> conj_tac >- simp[compile_acc_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  rpt gen_tac >> strip_tac >>
      drule account_body_pre_args >> strip_tac >> gvs[] >>
      `body_exprs_ptr_ok cx [e]` by
        (first_x_assum (qspecl_then [`es`, `es`] mp_tac) >>
         simp[builtin_args_length_ok_def, type_check_def, assert_def, return_def]) >>
      irule account_singleton_sim_ptr >> simp[] >> conj_tac
      >- (qexists_tac `env` >> simp[]) >>
      irule body_expr_ptr_sim >> simp[] >>
      conj_tac >- metis_tac[body_exprs_ptr_head] >>
      conj_tac >- (qexists_tac `tops` >> simp[]) >>
      qexists_tac `env` >> simp[]
QED
