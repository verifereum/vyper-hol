(* The raw scalar operation after two successful linked operand reads. *)
Theory bodyBopWordReachedRunMods
Ancestors
  bodyFullPostsMods bodySimStmtFacts exprBodyPreProps exprSimHyps exprSimHypsDefs
  bodyWriteSubscriptSourceMods
  exprBopSimProps exprBopSimDefs exprSimSource exprSimOperators
  bodyPtrBopScalarRun bodyPtrBopScalarDispatch loweringPosts
  vyperTypeSystem vyperTypeBuiltins vyperTypeInvariants vyperTypeEvalCaseProofs
  vyperTypeCallStackSoundness vyperState vyperAST vyperInterpreter
  gasOutcomeFull gasContext vyperStorageFootprint freshWrites
  allocLimits supportedExprTraverse vyperTypeCallGraph list
  vyperTypeExprSoundness exprSimProps
Libs monadsyntax

Theorem reached_bop_child_pres[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (Bop bop) [a;b]) es ==>
  expr_body_pre_mods mods ce cx env a es /\
  (!mid. expr_sim_inv_mods mods ce cx env mid ==>
    expr_body_pre_mods mods ce cx env b mid) /\
  byte_widths_expr a
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, well_typed_builtin_app_def,
       int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  drule_then assume_tac call_evaluation_safe_append_right >>
  fs[constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED

Theorem reached_bop_operand_source[local]:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  expr_sim_inv_mods mods ce cx env ee /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!n. expr_int_literal e = SOME n ==> v = IntV n) /\
  (shift_amount_ok e ==> ?i. v = IntV i /\ 0 <= i)
Proof
  strip_tac >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    fs[value_runtime_typed_def] >>
  simp[] >> conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] bop_value_scopes_dom) >> simp[]) >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  conj_tac >- metis_tac[eval_expr_int_literal_agrees] >>
  strip_tac >> drule_all eval_expr_shift_amount >> simp[]
QED

Theorem reached_bop_admissible[local]:
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2]))
    (read_result cx)) expr_res_ok es /\
  (!tail. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := l ++ tail) =
     (INL v1,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := r ++ tail) =
     (INL v2,fin with gas_obs := tail)) /\ fin.gas_obs = [] ==>
  expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin)
Proof
  strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  PURE_REWRITE_TAC [REWRITE_RULE [ETA_AX] eval_expr_bop_bind, gas_admissible_def] >>
  disch_then (irule o SPEC_ALL) >>
  qexistsl_tac [`fin`,`l ++ r`] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _` (qspec_then `r` assume_tac) >>
  qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  PURE_ONCE_REWRITE_TAC [bind_def] >> asm_rewrite_tac[] >> simp[] >>
  PURE_ONCE_REWRITE_TAC [bind_def] >> asm_rewrite_tac[] >> simp[]
QED

Theorem reached_bop_operand_word[local]:
  expr_post_mods H ctx func ce cx e ee sa sb s0 fin v op u /\
  word_value_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v ==> eval_operand op u = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by metis_tac[word_value_type_word] >>
  `word_value v` by metis_tac[word_value_type_typed] >>
  fs[expr_post_mods_def, expr_post_def, post_value_type_word] >>
  drule_all expr_val_rel_typed >> simp[typed_val_to_w256_word_value]
QED

Theorem bop_word_reached_run_mods:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  bop <> In /\ bop <> NotIn /\
  expr_body_pre_mods mods ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  (bop = Exp ==> IS_SOME (expr_int_literal e1) \/
    ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e2) /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2]))
    (read_result cx)) expr_res_ok es /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  s1.cs_next_var <= s2.cs_next_var /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
     (INL v1,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
     (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
     (INL v2,fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func ce cx e1 es sa s1 s0 mid v1 x t /\ mid.gas_obs = []) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post_mods H ctx func ce cx e2 mid s1 s2 t fin v2 y u /\ fin.gas_obs = []) ==>
  is_word_type ann /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  (?B. bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
         (emitted_insts s2 sb) B /\ op IN B) /\
  ((?v r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
      word_value v /\ run_inst_seq (emitted_insts s2 sb) u = OK r /\
      eval_operand op r = SOME (val_to_w256 v)) \/
   (?m r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin =
      INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts s2 sb) u = Abort Revert_abort r))
Proof
  strip_tac >> drule_then strip_assume_tac reached_bop_child_pres >>
  `is_word_type (expr_type e1) /\ is_word_type ann` by
    metis_tac[word_value_type_word,well_typed_binop_word_result] >>
  `type_bits (expr_type e1) MOD 8 = 0` by metis_tac[byte_widths_expr_type] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  `mid with gas_obs := [] = mid /\ fin with gas_obs := [] = fin` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit left s0.vs_gas_readings) = (INL v1,mid)` by
    (qpat_assum `bind (eval_expr cx e1) _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  `bind (eval_expr cx e2) (read_result cx)
     (mid with gas_obs := gas_explicit right t.vs_gas_readings) = (INL v2,fin)` by
    (qpat_assum `bind (eval_expr cx e2) _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all_then strip_assume_tac reached_bop_operand_source >>
  qpat_assum `!mid. expr_sim_inv_mods _ _ _ _ mid ==> _`
    (qspec_then `mid` (drule_then assume_tac)) >>
  drule_all_then strip_assume_tac reached_bop_operand_source >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin)` by
    (irule reached_bop_admissible >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`es`,`gas_explicit left s0.vs_gas_readings`,`mid`,
       `gas_explicit right t.vs_gas_readings`] >> simp[]) >>
  `eval_operand x t = SOME (val_to_w256 v1) /\ eval_operand y u = SOME (val_to_w256 v2)` by
    (conj_tac
     >- (qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
           (mp_then (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
              reached_bop_operand_word) >> simp[] >> disch_then irule >>
         qexists_tac `tv` >> simp[]) >>
     qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_then (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
          reached_bop_operand_word) >> simp[] >> disch_then irule >>
     qexists_tac `tv'` >> simp[]) >>
  `eval_operand x u = SOME (val_to_w256 v1)` by
    (irule eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s1`,`t`] >>
     fs[expr_post_mods_def, expr_post_def]) >>
  `!z. x = Var z ==> not_fresh_at s2 z` by metis_tac[not_fresh_at_mono] >>
  simp[] >> conj_tac
  >- (irule bop_scalar_binop_certificate >> simp[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  irule bop_scalar_typed_run >> simp[] >>
  conj_tac >- (qexistsl_tac [`x`,`y`] >> simp[]) >>
  metis_tac[]
QED
