(* Counted comparison of two source-order digest operands. *)
Theory bodyMemBopHeldCompare
Ancestors
  bodyMemBopHeldOperand bodyMemoryPreds exprSimMemDefs exprSimHypsDefs
  exprSimHyps exprSimProps exprSimSource exprBopSimProps exprBopLowering
  exprLowering compileEnv loweringPosts gasSummary gasOutcome gasCount
  fragExec venomState vyperInterpreter vyperState vyperValue vyperTypeSystem
  list rich_list bodyMemBopHeldFacts vyperAST exprSimOperators stmtReasonVvMemory
  exprBopDigestProps bodyMemBopHeldPost vyperTypeExprSoundness byte
  vyperTypeExprResult vyperTypeInvariants fragGasMode
Libs
  pairLib

Theorem held_typed_digest_source[local]:
  (bop = Eq \/ bop = NotEq) /\
  (?cap. ty = BaseT (BytesT (Dynamic cap)) \/ ty = BaseT (StringT cap)) /\
  value_runtime_typed env ty v1 /\ value_runtime_typed env ty v2 /\
  (v1 = BytesV bs1 \/ ?str. v1 = StringV str /\ bs1 = MAP (n2w o ORD) str) /\
  (v2 = BytesV bs2 \/ ?str. v2 = StringV str /\ bs2 = MAP (n2w o ORD) str) ==>
  !ee. bop_result cx ann bop [ty;ty] v1 v2 ee =
    INL (BoolV (if bop = Eq then
      (word_of_bytes_be (Keccak_256_w64 bs1):bytes32) = word_of_bytes_be (Keccak_256_w64 bs2)
      else (word_of_bytes_be (Keccak_256_w64 bs1):bytes32) <> word_of_bytes_be (Keccak_256_w64 bs2)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `value_runtime_typed _ _ v1`
    (strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
  qpat_x_assum `value_runtime_typed _ _ v2`
    (strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
  `tv' = tv` by metis_tac[optionTheory.SOME_11] >>
  gen_tac >> rewrite_tac[word_of_bytes_be_def] >>
  irule comparison_source_result >> metis_tac[]
QED

Theorem held_bytestring_compare_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
  body_exprs_mem_ok cx [e1;e2] ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (qpat_assum `expr_body_pre _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_body_pre_def, well_typed_expr_def,
                             well_typed_builtin_app_def]) >> simp[]) >>
  drule_all held_bytestring_eqne_types >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[expr_type_def, is_word_type_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  drule_all held_lower_value_compare >> disch_then (fn th => rewrite_tac[th]) >>
  strip_tac >> RULE_ASSUM_TAC (PURE_REWRITE_RULE [LET_THM]) >>
  qmatch_asmsub_abbrev_tac `UNCURRY f d1` >>
  PairCases_on `d1` >> rename1 `UNCURRY f (h1,s1)` >>
  qpat_x_assum `UNCURRY _ _ = _` mp_tac >> simp[Abbr `f`] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `UNCURRY g d2` >> PairCases_on `d2` >>
  rename1 `UNCURRY g (h2,s2)` >>
  qpat_x_assum `UNCURRY _ _ = _` mp_tac >> simp[Abbr `g`] >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `expr_type e1 = expr_type e2` by simp[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb /\
   local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
   fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
   (!z. h1 = Var z ==> not_fresh_at s1 z) /\
   (!z. h2 = Var z ==> not_fresh_at s2 z)` by
    (irule held_compare_cuts >>
     conj_tac >- (qexists_tac `bop` >> qexists_tac `op` >> asm_rewrite_tac[LET_THM]) >>
     conj_tac >- (qexists_tac `e1` >> pure_rewrite_tac[LET_THM] >> metis_tac[]) >>
     conj_tac >- (qexists_tac `e2` >> pure_rewrite_tac[LET_THM] >> metis_tac[]) >>
     simp[]) >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_mem ctx func cenv cx (expr_type e1) e1 es` by
    (qpat_assum `body_exprs_mem_ok _ _`
      (mp_tac o ONCE_REWRITE_RULE [body_exprs_mem_ok_def]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     pure_once_rewrite_tac[body_expr_mem_ok_def] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `expr_type e1`, `es`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV) bop_first_admissible) >> strip_tac >>
  qpat_assum `(h1,s1) = _` (assume_tac o SYM) >>
  drule_all (PURE_REWRITE_RULE [LET_THM] held_digest_operand_outcome) >>
  disch_tac >>
  pure_once_rewrite_tac[CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_bop_bind] >>
  qmatch_asmsub_abbrev_tac `gas_outcome T _ _ _ _ Qa Ra` >>
  irule gas_outcome_bind_value >>
  qexistsl_tac [`Qa`, `Ra`] >>
  reverse conj_tac
  >- (conj_tac
      >- (simp[Abbr `Ra`] >> rpt gen_tac >>
          Cases_on `res` >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Qa _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `Qa`] >>
  disch_then (qx_choose_then `v1` (qx_choose_then `bs1`
    (map_every assume_tac o CONJUNCTS))) >>
  qexists_tac `v1` >>
  conj_tac >- first_assum ACCEPT_TAC >> BETA_TAC >>
  qpat_x_assum `res = INL v1` SUBST_ALL_TAC >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) bop_second_admissible) >> disch_tac >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (irule (BETA_RULE (Q.INST
       [`P` |-> `\(v:value) ee. expr_sim_inv cenv cx env ee`]
       (CONV_RULE (DEPTH_CONV ETA_CONV) bop_prefix_continuation))) >>
     goal_assum (drule_at Any) >>
     rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by
       metis_tac[expr_body_pre_gas_obs] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `body_expr_mem_ok cx e2` by
    (qpat_assum `body_exprs_mem_ok _ _` mp_tac >>
     pure_once_rewrite_tac[body_exprs_mem_ok_def] >>
     disch_then (mp_tac o CONJUNCT2) >>
     (impl_tac
      >- (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
          strip_tac >>
          first_x_assum (qspec_then `[]` mp_tac) >>
          simp_tac (srw_ss()) [bind_def, AllCaseEqs()] >>
          metis_tac[])) >>
     simp[body_exprs_mem_ok_def]) >>
  `expr_body_pre cenv cx env e2 (mid with gas_obs := [])` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `expr_sim_mem ctx func cenv cx (expr_type e2) e2 (mid with gas_obs := [])` by
    (qpat_assum `body_expr_mem_ok cx e2`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
     disch_then drule_all >>
     disch_then (qspecl_then [`func`, `expr_type e2`] (ACCEPT_TAC o CONJUNCT1))) >>
  `is_bytestring_type (expr_type e2)` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (rewrite_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `expr_type e1 = expr_type e2` (fn th =>
    qpat_assum `(h2,s2) = _`
      (assume_tac o SYM o PURE_REWRITE_RULE [th])) >>
  drule_all (Q.INST [`e` |-> `e2`]
    (PURE_REWRITE_RULE [LET_THM] held_digest_operand_outcome)) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome T _ _ _ (mid with gas_obs := [],t) Qb Rb` >>
  irule gas_outcome_bind_value >>
  qexistsl_tac [`Qb`, `Rb`] >>
  reverse conj_tac
  >- (conj_tac
      >- (simp[Abbr `Rb`, Abbr `Ra`] >> rpt gen_tac >>
          Cases_on `res` >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Qb _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `Qb`] >>
  disch_then (qx_choose_then `v2` (qx_choose_then `bs2`
    (map_every assume_tac o CONJUNCTS))) >>
  qexists_tac `v2` >>
  conj_tac >- first_assum ACCEPT_TAC >> BETA_TAC >>
  qpat_x_assum `res = INL v2` SUBST_ALL_TAC >>
  `!lbl. h1 <> Label lbl` by
    (qpat_assum `(h1,s1) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `bytestring_literal_hash e1` >>
     simp[LET_THM] >>
     pairarg_tac >>
     simp[compile_bytestring_hash_def, emitHelperTheory.emit_op_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, LET_THM]) >>
  `eval_operand h1 t' = SOME (word_of_bytes_be (Keccak_256_w64 bs1))` by
    (qpat_assum `eval_operand h1 t = _` mp_tac >>
     qpat_assum `!z. h1 = Var z ==> _` mp_tac >>
     qpat_assum `!x w. not_fresh_at s1 x /\ _ ==> _` mp_tac >>
     qpat_assum `!lbl. h1 <> Label lbl` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `h1` >> simp_tac (srw_ss()) [eval_operand_def] >>
     metis_tac[]) >>
  drule_all (PURE_REWRITE_RULE [LET_THM] held_compare_counted_nofresh) >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  `value_runtime_typed env (expr_type e1) v1` by
    (irule (BETA_RULE (Q.INST
       [`P` |-> `\(v:value) ee. value_runtime_typed env (expr_type e1) v`]
       (CONV_RULE (DEPTH_CONV ETA_CONV) bop_prefix_continuation))) >>
     goal_assum (drule_at Any) >>
     rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by
       metis_tac[expr_body_pre_gas_obs] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
     simp_tac (srw_ss()) [expr_result_typed_def, expr_runtime_typed_def,
       value_result_typed_def, value_runtime_typed_def] >>
     strip_tac >> first_x_assum (qspec_then `v` mp_tac) >> simp[]) >>
  `value_runtime_typed env (expr_type e2) v2` by
    (irule (BETA_RULE (Q.INST
       [`P` |-> `\(v:value) ee. value_runtime_typed env (expr_type e2) v`]
       (CONV_RULE (DEPTH_CONV ETA_CONV) bop_prefix_continuation))) >>
     goal_assum (drule_at Any) >>
     rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e2 ((mid with gas_obs := []) with gas_obs := gs)` by
       metis_tac[expr_body_pre_gas_obs] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
     simp_tac (srw_ss()) [expr_result_typed_def, expr_runtime_typed_def,
       value_result_typed_def, value_runtime_typed_def] >>
     strip_tac >> first_x_assum (qspec_then `v` mp_tac) >> simp[]) >>
  `!ee. bop_result cx (BaseT BoolT) bop [expr_type e1; expr_type e2] v1 v2 ee =
    INL (BoolV (if bop = Eq then
      (word_of_bytes_be (Keccak_256_w64 bs1):bytes32) = word_of_bytes_be (Keccak_256_w64 bs2)
      else (word_of_bytes_be (Keccak_256_w64 bs1):bytes32) <> word_of_bytes_be (Keccak_256_w64 bs2)))` by
    (qpat_assum `expr_type e2 = expr_type e1`
       (fn th => pure_rewrite_tac[th]) >>
     irule held_typed_digest_source >>
     conj_tac >- (qpat_assum `(?n. expr_type e1 = _) \/ _` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexists_tac `env` >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `expr_type e2 = expr_type e1` (fn th =>
       qpat_assum `value_runtime_typed _ _ v2` (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  simp_tac (srw_ss()) [gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp_tac (srw_ss()) [gas_summary_at_def] >>
  qexistsl_tac [`INL (BoolV (if bop = Eq then
      (word_of_bytes_be (Keccak_256_w64 bs1):bytes32) = word_of_bytes_be (Keccak_256_w64 bs2)
      else (word_of_bytes_be (Keccak_256_w64 bs1):bytes32) <> word_of_bytes_be (Keccak_256_w64 bs2)))`,
    `mid'`, `OK u`] >>
  conj_tac >- simp[gas_marked_exec_def, gas_marked_path_def] >>
  simp_tac (srw_ss()) [] >>
  disj1_tac >> reverse conj_tac
  >- (simp[] >> decide_tac) >>
  irule held_digest_compare_post >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl_tac [`mid`, `s1`, `s2`, `t`, `t'`] >>
      `sa.cs_next_id <= s1.cs_next_id /\
       sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var` by
        (qpat_assum `ci_mono sa s1` mp_tac >>
         qpat_assum `ci_mono s1 s2` mp_tac >>
         simp_tac (srw_ss()) [exprLoweringPropsTheory.ci_mono_def] >>
         rpt strip_tac >> first_assum ACCEPT_TAC) >>
      `locals_kept cenv mid t t'` by
        (qpat_assum `locals_kept _ (mid with gas_obs := []) _ _` mp_tac >>
         simp_tac (srw_ss()) [locals_kept_def] >>
         disch_then ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs]
QED
