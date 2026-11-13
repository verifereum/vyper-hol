(* Counted composition of two word operands and their actual operator path. *)
Theory exprSimBopTyped
Ancestors
  exprBopSimDefs exprBopSimProps gasSummary gasOutcome gasSummaryCompose gasExemptCert gasNormalPrefix
  gasStorage vyperStorageTrace vyperStorageFootprint
  exprSimProps
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragGasMode fragGasPath fragExec varsExt  freshWrites exprBopLowering loweringSlice
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding venomExecSemantics venomInst venomState
  vyperValue integer integer_word int_bitwise words intBits vyperTyping
Libs
  pairLib


Theorem compile_bop_typed_sim:
  !ctx func cenv cx ty ann bop e1 e2 es tv1 tv2.
    ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
    ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
    is_word_type ann /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e2 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!x y sa sb op.
       compile_binop bop x y (expr_type e1)
         (if bop = Exp then expr_int_literal e1 else NONE)
         (if bop = Exp then expr_int_literal e2 else NONE) sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do result <- eval_expr cx e1; read_result cx result od)
        (es with gas_obs := gs1) = (INL v1, es1) ==>
       expr_sim ctx func cenv cx (expr_type e1) e2 es1 /\
       !gs2 v2 es2. (do result <- eval_expr cx e2; read_result cx result od)
         (es1 with gas_obs := gs2) = (INL v2, es2) ==>
         binop_frag_words ctx func cenv cx bop (expr_type e1) ann
           (if bop = Exp then expr_int_literal e1 else NONE)
           (if bop = Exp then expr_int_literal e2 else NONE)
           [expr_type e1; expr_type e2] v1 v2
           (typed_val_to_w256 tv1 v1) (typed_val_to_w256 tv2 v2) es2) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_bop >> strip_tac >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ e2 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x y sa sb op. compile_binop _ _ _ _ _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `cs_extends s1 sb /\ cs_extends sa s2` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func`
    by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[bop_first_admissible] >>
  `!v1 v2. storage_trace_frame
      (\es2. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es2, es2))` by
    simp[storage_trace_frame_def, bop_result_def] >>
  `storage_trace_frame (bind (eval_expr cx e1) (read_result cx)) /\
   storage_trace_frame (bind (eval_expr cx e2) (read_result cx))` by
    (conj_tac >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_bad_storage_at_bind_left >> simp[] >> (rw[] >> irule storage_trace_frame_bind_all >> simp[]))
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
           irule gas_bad_storage_at_bind_left >>
           reverse conj_tac
           >- (irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
           rw[] >> irule storage_trace_frame_bind_all >> simp[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "left_normal"
      >> suspend "left_exit") >>
  suspend "left_exempt"
QED

Resume compile_bop_typed_sim[left_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
    (drule_then strip_assume_tac) >>
  rename1 `expr_post _ _ _ _ _ e1 _ _ _ _ _ v1 _ t` >>
  `?obs. es_end.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (bind (eval_expr cx e1) _)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    simp[valid_horizon_def] >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     expr_post H ctx func cenv cx e1 es sa s1 s0 (es_end with gas_obs := [])
       v1 x t` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?v. _` drule >> simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     gas_value_prefix H F (ctx, func, cenv, cx) (expr_type e1, e1)
       (sa, s1, x) (es, s0) marks (v1, es_end, t)` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H)` by metis_tac[] >>
     `expr_post H ctx func cenv cx e1 es sa s1 s0
        (es_end with gas_obs := []) v1 x t` by metis_tac[] >>
     simp[gas_value_prefix_def] >> metis_tac[]) >>
  qpat_x_assum `res = INL v1` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` mp_tac) >>
  strip_tac >>
  qpat_x_assum `!gs1 v1 es1. _`
    (mp_tac o REWRITE_RULE [ETA_AX]) >>
  disch_then drule >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx))
     expr_res_ok (es_end with gas_obs := [])` by
    metis_tac[bop_second_admissible] >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) t /\
     storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       drule >> simp[expr_post_def]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `expr_sim _ _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`st0`, `s1`, `s2`, `y`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
      pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_bad_storage_at_bind_right >>
      qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _` (irule_at Any) >>
      simp[] >> irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end'.storage_trace`)
       >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
           pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
           irule gas_bad_storage_at_bind_right >>
           qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _` (irule_at Any) >>
           simp[] >> irule gas_bad_storage_at_bind_left >>
           reverse conj_tac
           >- (irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
           simp[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end'.storage_trace)
         es_end'.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "right_normal"
      >> suspend "right_exit") >>
  suspend "right_exempt"
QED
Resume compile_bop_typed_sim[left_exit]:
  Cases_on `res`
  >- (qpat_x_assum `(\res ee r. _) _ _ _`
        (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac o
         SIMP_RULE (srw_ss()) []) >> gvs[]) >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >>
  conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gnvs[] >> first_assum ACCEPT_TAC
QED
Resume compile_bop_typed_sim[left_exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  drule (REWRITE_RULE [ETA_AX] bop_first_exempt_cert) >> metis_tac[]
QED
Resume compile_bop_typed_sim[right_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?v. _`
    (drule_then strip_assume_tac) >>
  rename1 `expr_post _ _ _ _ _ e2 _ _ _ _ _ v2 _ u` >>
  `?obs'. es_end'.storage_trace = es_end.storage_trace ++ obs'` by
    (qpat_assum `gas_marked_exec _ _ _ (es_end with gas_obs := [], t) _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (bind (eval_expr cx e2) _)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end'.storage_trace ==>
       valid_horizon cx st0 H es_end.storage_trace` by
    simp[valid_horizon_def] >>
  `!H. valid_horizon cx st0 H es_end'.storage_trace ==>
     gas_value_prefix H F (ctx, func, cenv, cx) (expr_type e1, e2)
       (s1, s2, y) (es_end with gas_obs := [], t) marks' (v2, es_end', u)` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H es_end.storage_trace` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) t /\
      storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
       metis_tac[] >>
     `expr_post H ctx func cenv cx e2 (es_end with gas_obs := []) s1 s2 t
        (es_end' with gas_obs := []) v2 y u` by
       (qpat_x_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?v. _`
          drule >> simp[]) >>
     simp[gas_value_prefix_def] >> metis_tac[]) >>
  qpat_x_assum `res = INL v2` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK u` SUBST_ALL_TAC >>
  qpat_assum `gas_marked_exec _ _ _ _ _ (INL v2) _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `!gs2 v2 es2. _` (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
  `?H. valid_horizon cx st0 H es_end'.storage_trace` by metis_tac[] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  drule_all (Q.INST [`mid` |-> `es_end`, `fin` |-> `es_end'`,
                     `left` |-> `marks`, `right` |-> `marks'`]
               (SIMP_RULE bool_ss [PULL_EXISTS]
                 (REWRITE_RULE [ETA_AX] bop_normal_prefix_summary))) >> simp[]
QED
Resume compile_bop_typed_sim[right_exit]:
  Cases_on `res`
  >- (qpat_x_assum `(\res ee r. _) _ _ _`
        (qspec_then `storage_trace_horizon es_end'.storage_trace` mp_tac o
         SIMP_RULE (srw_ss()) []) >> gvs[]) >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >>
  conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v1) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gnvs[] >> first_assum ACCEPT_TAC
QED
Resume compile_bop_typed_sim[right_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  irule_at Any (REWRITE_RULE [ETA_AX] bop_second_exempt_cert) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Finalise compile_bop_typed_sim

Theorem compile_bop_sim:
  !ctx func cenv cx ty ann bop e1 e2 es.
    ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
    ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
    is_word_type ann /\
    is_word_type (expr_type e1) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
    is_word_type (expr_type e2) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e2 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!x y sa sb op.
       compile_binop bop x y (expr_type e1)
         (if bop = Exp then expr_int_literal e1 else NONE)
         (if bop = Exp then expr_int_literal e2 else NONE) sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do result <- eval_expr cx e1; read_result cx result od)
       (es with gas_obs := gs1) = (INL v1, es1) ==>
       word_value v1 /\
       expr_sim ctx func cenv cx (expr_type e1) e2 es1 /\
       !gs2 v2 es2. (do result <- eval_expr cx e2; read_result cx result od)
         (es1 with gas_obs := gs2) = (INL v2, es2) ==>
         word_value v2 /\
         binop_frag ctx func cenv cx bop (expr_type e1) ann
           (if bop = Exp then expr_int_literal e1 else NONE)
           (if bop = Exp then expr_int_literal e2 else NONE)
           [expr_type e1; expr_type e2] v1 v2 es2) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `IS_SOME (evaluate_type _ (expr_type e1))`
    (qx_choose_then `t1` assume_tac o
     REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ (expr_type e2))`
    (qx_choose_then `t2` assume_tac o
     REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule compile_bop_typed_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t1`, `t2`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs1 v1 es1. _ ==> word_value v1 /\ _` drule >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs2 v2 es2. _ ==> word_value v2 /\ _` drule >> strip_tac >>
  gvs[typed_val_to_w256_word_value, binop_frag_def]
QED
