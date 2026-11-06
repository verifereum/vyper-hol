(* Source-only bridges for counted mixed word/vv operand composition. *)
Theory exprSimBopRestWordCompose
Ancestors
  gasSummary gasSummaryCompose gasExemptCert exprBopSimProps vyperState
  vyperInterpreter exprSimMemorySource list allocLimits exprSimHypsDefs
  localPtrsProps exprSimProps freshWrites exprSimBopRestWordTail exprSimUnwrapProps
  exprSimBopRestWordFacts exprBopLowering exprSimSource exprSimHyps
Libs
  pairLib

Theorem rest_word_marked_read:
  gas_marked_exec memory (ctx, func) (eval_expr cx e)
    (es,s0) marks (INL tv) mid (OK t) /\
  (!tail. read_result cx tv (mid with gas_obs := tail) =
    (INL v, mid with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx, func)
    (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) mid (OK t)
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  simp[bind_def]
QED

Theorem rest_word_raw_second_exempt_cert:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx e2) (return ()))
    (mid with gas_obs := [],t) right (err,ee) (leaf,sf) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2]))
                      (read_result cx)) (return ()))
    (es,s0) (left ++ right) (err,ee) (leaf,sf)
Proof
  strip_tac >> drule force_exempt_cert >> strip_tac >>
  irule (REWRITE_RULE [ETA_AX] bop_second_exempt_cert) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_mixed_marked_tail:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e2)
    (mid with gas_obs := [],t) right (INL tv2) fin (OK u) /\
  (!tail. read_result cx tv2 (fin with gas_obs := tail) =
    (INL v2,fin with gas_obs := tail)) /\
  gas_marked_exec memory (ctx,func)
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin with gas_obs := [],u) suffix res last r ==>
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0) (left ++ right ++ suffix) res last r
Proof
  strip_tac >> drule_all rest_word_marked_read >> strip_tac >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_mixed_tail_summary:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e2)
    (mid with gas_obs := [],t) right (INL tv2) fin (OK u) /\
  (!tail. read_result cx tv2 (fin with gas_obs := tail) =
    (INL v2,fin with gas_obs := tail)) /\
  gas_marked_exec memory (ctx,func)
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin with gas_obs := [],u) suffix res last r /\
  ((?z. r = OK z /\ Q res (last with gas_obs := []) z) \/
   (exit_result r /\ R res (last with gas_obs := []) r)) ==>
  gas_summary_at memory (ctx,func) (left ++ right ++ suffix)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0) Q R
Proof
  strip_tac >> drule_all rest_word_mixed_marked_tail >> strip_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `last`, `r`] >> simp[]
QED

Theorem rest_word_mixed_post:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  vv_post ctx func cenv cx e2 es1 s1 sm t es2 tv vv q /\
  expr_val_rel cx ann v out q /\
  expr_val_at cenv cx ann sa ct es2 v out q /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id ==>
  expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
    es sa ct s0 es2 v out q
Proof
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.vv_post_def] >> strip_tac >>
  simp[vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s1 x'` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (fn th => rewrite_tac [GSYM th]) >>
      qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      disch_then irule >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
          qexists `n` >> irule local_region_frame >>
          conj_tac >- (qexists `func` >>
            gvs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
          qexistsl [`sa`, `es1.scopes`, `t`] >> asm_rewrite_tac[])
      >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
          qexists `sa.cs_next_id` >> asm_rewrite_tac[]) >>
      metis_tac[]) >>
  irule locals_kept_trans >> qexistsl [`es1`, `sa`, `t`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem rest_word_array_alloc_bound:
  is_word_type ty /\ type_alloc_ok cenv (ArrayT ty bd) ==>
  (case bd of Fixed n => n | Dynamic n => n) < dimword (:256)
Proof
  strip_tac >>
  `elem_size_in_location cenv LocMemory ty = word_scale LocMemory` by
    metis_tac[exprSimBopRestWordTailTheory.rest_word_word_stride] >>
  `type_memory_bytes cenv ty = 32` by
    fs[compileEnvTheory.elem_size_in_location_def,
      compileEnvTheory.is_slot_addressed_def, compileEnvTheory.word_scale_def] >>
  Cases_on `bd` >>
  gvs[allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def,
    compileEnvTheory.type_memory_bytes_def, wordsTheory.dimword_def] >> decide_tac
QED

Theorem rest_word_mixed_outcome:
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  compile_expr cenv (expr_type e2) e2 s1 = (vv,sm) /\
  compile_var_array_membership cenv x vv (expr_type e2) (bop = In) sm = (out,ct) /\
  fn_has_code sa s1 func /\ fn_has_code s1 sm func /\ fn_has_code sm ct func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    expr_res_ok es /\
  expr_sim ctx func cenv cx (expr_type e1) e1 es /\
  (!left v1 mid t.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e1) (read_result cx))
      (es,s0) left (INL v1) mid (OK t) /\
    expr_post ctx func cenv cx e1 es sa s1 s0 (mid with gas_obs := []) v1 x t /\
    t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
    expr_vv_sim ctx func cenv cx (expr_type e2) e2 (mid with gas_obs := []) /\
    gas_admissible (eval_expr cx e2) expr_vv_res_ok (mid with gas_obs := []) /\
    MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes /\
    !right tv fin u.
      gas_marked_exec F (ctx,func) (eval_expr cx e2)
        (mid with gas_obs := [],t) right (INL tv) fin (OK u) /\
      vv_post ctx func cenv cx e2 (mid with gas_obs := []) s1 sm t
        (fin with gas_obs := []) tv vv u /\
      u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
      ?v2 suffix last q v.
        (!tail. read_result cx tv (fin with gas_obs := tail) =
          (INL v2,fin with gas_obs := tail)) /\
        gas_marked_exec F (ctx,func)
          (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
          (fin with gas_obs := [],u) suffix (INL v) last (OK q) /\
        vv_post ctx func cenv cx e2 (mid with gas_obs := []) s1 sm t
          (last with gas_obs := []) tv vv q /\
        expr_val_rel cx ann v out q /\
        expr_val_at cenv cx ann sa ct (last with gas_obs := []) v out q /\
        q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx)) (es,s0)
    (\res ee q. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
        es sa ct s0 ee v out q /\
      q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[bop_first_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "left_normal"
      >> suspend "left_exit") >>
  suspend "left_exempt"
QED

Resume rest_word_mixed_outcome[left_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists `marks` >> disj1_tac >> simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INR exc`, `es_end`, `r`] >> conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gnvs[]
QED

Resume rest_word_mixed_outcome[left_exempt]:
  qexists `marks` >> disj2_tac >>
  drule (REWRITE_RULE [ETA_AX] bop_first_exempt_cert) >> metis_tac[]
QED

Resume rest_word_mixed_outcome[left_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >> rename1 `expr_post _ _ _ _ e1 _ _ _ _ _ v1 _ t` >>
  qpat_x_assum `!left v1 mid t. _` drule_all >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    fs[loweringPostsTheory.expr_post_def] >>
  `~t.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_vv_sim_def]) >>
  disch_then (qspecl_then [`s1`, `sm`, `vv`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "right_normal"
      >> suspend "right_exit") >>
  suspend "right_exempt"
QED

Resume rest_word_mixed_outcome[right_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists `marks ++ marks'` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v1) _ _` (irule_at Any) >>
      BETA_TAC >> irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> Cases_on `exc` >> Cases_on `r` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[exprSimDefsTheory.expr_exit_def]
QED
Resume rest_word_mixed_outcome[right_exempt]:
  qexists `marks ++ marks'` >> disj2_tac >>
  irule_at Any rest_word_raw_second_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Resume rest_word_mixed_outcome[right_normal]:
  qpat_x_assum `(\res ee t'. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  qpat_x_assum `!right tv fin u. _` drule_all >> strip_tac >>
  `expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
     es sa ct s0 (last with gas_obs := []) v out q` by
    (irule rest_word_mixed_post >>
     qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `vv_post _ _ _ _ e2 _ _ _ _ _ _ _ q` (irule_at Any) >> simp[]) >>
  qexists `marks ++ marks' ++ suffix` >> disj1_tac >>
  irule rest_word_mixed_tail_summary >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise rest_word_mixed_outcome

(* A word-element array's value is described at a type of the same element
   and bound kind: the widening of an internal call's return type changes
   only a dynamic array's capacity. *)
Theorem rest_word_fits_word[local]:
  !t u. arg_type_fits t u /\ is_word_type u ==> t = u
Proof
  rpt strip_tac >>
  Cases_on `t` >> Cases_on `u` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, compileEnvTheory.is_word_type_def] >>
  rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
  Cases_on `b1` >> Cases_on `b2` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, compileEnvTheory.is_word_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
  Cases_on `d1` >> Cases_on `d2` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, compileEnvTheory.is_word_type_def]
QED

Theorem rest_word_widened_array_shape[local]:
  !tenv pt u bd.
    type_widens_to tenv pt (ArrayT u bd) /\ is_word_type u ==>
    ?pbd. pt = ArrayT u pbd /\
          case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m
Proof
  rpt strip_tac >>
  qpat_x_assum `type_widens_to _ _ _`
    (strip_assume_tac o REWRITE_RULE [vyperTypeSystemTheory.type_widens_to_def])
  >- (Cases_on `bd` >> gvs[]) >>
  `?t sb. pt = ArrayT t sb` by
    (Cases_on `pt` >> TRY (rename1 `BaseT b` >> Cases_on `b`) >>
     TRY (rename1 `BytesT d` >> Cases_on `d`) >>
     gvs[vyperTypeSystemTheory.arg_type_fits_def]) >>
  gvs[] >>
  `arg_type_fits t u` by
    (Cases_on `sb` >> Cases_on `bd` >> gvs[vyperTypeSystemTheory.arg_type_fits_def]) >>
  drule_all rest_word_fits_word >> strip_tac >> gvs[] >>
  Cases_on `sb` >> Cases_on `bd` >> gvs[vyperTypeSystemTheory.arg_type_fits_def]
QED

Theorem compile_rest_word_membership_sim:
  !nocalls ctx func cenv cx env ty ann bop e1 e2 bd es.
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
    (nocalls ==> int_calls_expr (Builtin ann (Bop bop) [e1;e2]) = []) /\
    (bop = In \/ bop = NotIn) /\
    is_word_type (expr_type e1) /\
    expr_type e2 = ArrayT (expr_type e1) bd /\
    (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    expr_sim_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv,t) /\
                        read_result cx tv s1 = (INL v,t1)) ==>
       expr_vv_case nocalls ctx func cenv cx e2) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all rest_word_nonliteral_dispatch >> disch_tac >>
  simp[exprSimDefsTheory.expr_sim_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def,
    exprBopLoweringTheory.compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 exprLoweringTheory.compile_expr_raw_def)),
    Q.INST [`et` |-> `expr_type e1`, `bd` |-> `bd`] rest_word_nonliteral_dispatch,
    exprBopLoweringTheory.lower_value_child_call] >>
  rpt (pairarg_tac >> gnvs[]) >>
  simp[exprBopLoweringTheory.as_stack_val_pair, exprLoweringTheory.unwrap_value_def,
    compileEnvTheory.comp_return_def] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ tailcomp` >>
  PairCases_on `tailcomp` >>
  simp[exprBopLoweringTheory.as_stack_val_pair] >> strip_tac >>
  gnvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def,
    compileEnvTheory.comp_bind_def, ETA_AX] >>
  qpat_x_assum `!ty st ret_ty e1' cenv' ce. _` kall_tac >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `cs_extends st2 sb` by suspend "tail_extends" >>
  suspend "operand_boundaries"
QED

Resume compile_rest_word_membership_sim[tail_extends]:
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `bd` >>
  simp[exprLoweringTheory.compile_var_array_membership_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[compileEnvTheory.comp_return_def] >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [exprSimBopRestWordLayoutTheory.rest_word_loop_factor_eq]) >>
  rename1 `rest_word_loop_prefix _ _ _ _ _ loopst = (h,cl)` >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_prefix_shape >>
  rewrite_tac[exprSimBopRestWordLayoutTheory.rest_word_loop_prefix_shape_def] >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_ptr_load_shape >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_suffix_shape >>
  rewrite_tac[exprSimBopRestWordLayoutTheory.rest_word_loop_suffix_shape_def] >> strip_tac >>
  `cs_extends loopst sb` by
    (simp[compileEnvTheory.cs_extends_def] >> qexists `TAKE 6 sb.cs_blocks` >> simp[]) >>
  qpat_assum `compile_ptr_load _ _ _ (vv_operand arr_vv) st2 = _`
    (mp_tac o MATCH_MP exprSimBopRestWordLayoutTheory.rest_word_ptr_load_shape) >> strip_tac >>
  drule_all rest_word_capacity_check_shape >> strip_tac >>
  `cs_extends st2 loopst` by
    simp[compileEnvTheory.cs_extends_def,
      rich_listTheory.IS_PREFIX_APPEND, listTheory.APPEND_ASSOC] >>
  metis_tac[compileEnvTheory.cs_extends_trans]
QED
Resume compile_rest_word_membership_sim[operand_boundaries]:
  `expr_body_pre cenv cx env e1 es` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     conj_tac >- fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     qexistsl [`ann`, `[e1; e2]`, `Bop bop`, `es`] >> simp[]) >>
  drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> strip_tac >>
  qpat_assum `compile_expr _ _ e2 _ = _`
    (mp_tac o MATCH_MP (CONJUNCT1 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  `cs_extends sa st2` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `cs_extends st1 sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sa st1 func /\ fn_has_code st1 st2 func /\ fn_has_code st2 sb func` by
    metis_tac[fragExecTheory.fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
  `local_ptrs_reserved cenv st1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `expr_sim ctx func cenv cx (expr_type e1) e1 es` by
    (fs[exprSimHypsDefsTheory.expr_sim_case_def,
      vyperTypeCallGraphTheory.int_calls_expr_def] >> metis_tac[]) >>
  irule rest_word_mixed_outcome >>
  qpat_assum `lower_value _ _ _ e1 _ = _` (irule_at Any) >>
  qexistsl [`arr_vv`, `st2`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit left s0.vs_gas_readings) =
       (INL v1, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e1
      (es with gas_obs := gas_explicit left s0.vs_gas_readings)` by simp[] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval] >>
  `expr_body_pre cenv cx env e2 (mid with gas_obs := [])` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ann`, `[e1; e2]`, `Bop bop`, `es`] >> simp[]) >>
  `expr_vv_case nocalls ctx func cenv cx e2` by
    (qpat_x_assum `(_ ==> expr_vv_case _ _ _ _ _ _)` irule >>
     drule (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL) >>
     strip_tac >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `expr_vv_case _ _ _ _ _ e2`
        (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_vv_case_def]) >>
      disch_then irule >> reverse conj_tac
      >- (qexists `env` >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `nocalls ==> _` mp_tac >>
      simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  conj_tac
  >- (irule exprSimHypsTheory.expr_body_pre_vv_gas_admissible >>
      qexistsl [`cenv`, `env`] >> gvs[]) >>
  conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] exprBopSimPropsTheory.bop_value_scopes_dom) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `eval_expr cx e2
     (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
       (INL tv, fin with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr cx e2) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e2
     (mid with gas_obs := gas_explicit right t.vs_gas_readings)` by gvs[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `?pbd. post_value_type cenv e2 = ArrayT (expr_type e1) pbd /\
         case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m` by
    (irule rest_word_widened_array_shape >> simp[] >>
     qexists `env.type_defs` >>
     qpat_assum `expr_type e2 = _` (SUBST1_TAC o SYM) >>
     irule exprSimHypsTheory.post_value_type_widens >>
     conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ e2 (mid with gas_obs := [])`
           (ACCEPT_TAC o cj 2 o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def])) >>
     qexistsl [`cx`, `mid with gas_obs := []`] >> first_assum ACCEPT_TAC) >>
  `vv_holds cenv cx (ArrayT (expr_type e1) pbd) tv arr_vv (fin with gas_obs := []) u` by
    (qpat_x_assum `post_value_type cenv e2 = _` (assume_tac o SYM) >>
     fs[loweringPostsTheory.vv_post_def]) >>
  drule exprSimBopRestWordBasicsTheory.rest_word_vv_read_suffix >>
  simp[] >> disch_then (qx_choose_then `v2` assume_tac) >>
  `value_has_type tvt v2` by metis_tac[] >>
  `?et. tvt = ArrayTV et bd /\
        evaluate_type (get_tenv cx) (expr_type e1) = SOME et` by
    (qpat_x_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  gnvs[] >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e2) = SOME (ArrayTV et pbd)` by
    (qpat_assum `expr_body_pre _ _ _ e2 _`
       (strip_assume_tac o MATCH_MP exprSimHypsTheory.post_type_evaluates) >>
     pop_assum mp_tac >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `?av. v2 = ArrayV av` by
    (Cases_on `v2` >> fs[vyperTypingTheory.value_has_type_def]) >>
  gnvs[] >>
  `vv_post ctx func cenv cx e2 (mid with gas_obs := []) st1 st2 t
      (fin with gas_obs := []) (Value (ArrayV av)) arr_vv u` by
    (qpat_assum `!tail. read_result _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     drule exprSimUnwrapPropsTheory.vv_post_read_result >>
     simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e1
      (es with gas_obs := gas_explicit left s0.vs_gas_readings)` by simp[] >>
  `value_has_type et v1` by
    (drule_all (REWRITE_RULE [ETA_AX] exprSimSourceTheory.expr_body_pre_word_value) >>
     strip_tac >> gvs[]) >>
  `eval_operand needle t = SOME (typed_val_to_w256 et v1)` by
    (qpat_x_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def] >>
     metis_tac[]) >>
  `eval_operand needle u = SOME (typed_val_to_w256 et v1)` by
    (Cases_on `needle` >>
     fs[venomStateTheory.eval_operand_def, loweringPostsTheory.vv_post_def] >>
     metis_tac[]) >>
  `!z. needle = Var z \/ vv_operand arr_vv = Var z ==> not_fresh_at st2 z` by
    (rpt strip_tac
     >- metis_tac[freshWritesTheory.not_fresh_at_mono]
     >> drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `(?w. eval_operand (vv_operand arr_vv) u = SOME w) /\
   (case vv_location arr_vv of NONE => LocMemory | SOME l => l) <> LocCalldata` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `arr_vv` >>
     simp[loweringPostsTheory.vv_holds_def, contextTheory.vv_operand_def,
          contextTheory.vv_location_def, loweringPostsTheory.expr_val_rel_def]
     >- metis_tac[] >>
     rename1 `p.ptr_location` >>
     Cases_on `p.ptr_location` >> simp[] >> metis_tac[]) >>
  `type_alloc_ok cenv (ArrayT (expr_type e1) bd)` by
    (`alloc_limits_expr cenv e2` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[]) >>
  `(case bd of Fixed n => n | Dynamic n => n) < dimword (:256)` by
    metis_tac[rest_word_array_alloc_bound] >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ right _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `?q. gas_marked_path F ctx func u 0 (OK q) /\
       q.vs_current_bb = sb.cs_current_bb /\
       q.vs_inst_idx = LENGTH sb.cs_current_insts /\
       vv_post ctx func cenv cx e2 (mid with gas_obs := []) st1 st2 t
         (fin with gas_obs := []) (Value (ArrayV av)) arr_vv q /\
       eval_operand op q = SOME (bool_to_word
         (if bop = In then evaluate_in_array (ArrayTV et bd) v1 av
          else ~evaluate_in_array (ArrayTV et bd) v1 av))` by
    (Cases_on `bd` >> gnvs[]
     >- (drule (Q.INST [`loc` |-> `(case vv_location vv of SOME l => l | NONE => LocMemory)`,
                        `memory` |-> `F`, `execctx` |-> `ctx`]
                  (SPEC_ALL exprSimBopRestWordTailTheory.rest_word_fixed_tail)) >>
         simp[] >> disch_then drule >> simp[] >> disch_then drule >>
         simp[] >> disch_then (qspec_then `v1` mp_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `?m. pbd = Dynamic m` (qx_choose_then `pcap` SUBST_ALL_TAC) >>
     drule (Q.INST [`loc` |-> `(case vv_location vv of SOME l => l | NONE => LocMemory)`,
                    `memory` |-> `F`, `execctx` |-> `ctx`]
              (SPEC_ALL exprSimBopRestWordTailTheory.rest_word_dynamic_tail)) >>
     simp[] >> disch_then drule >> simp[] >> disch_then drule >>
         simp[] >> disch_then (qspec_then `v1` mp_tac) >> simp[] >> metis_tac[]) >>
  `ann = BaseT BoolT` by
    (qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
     qpat_x_assum `bop = In \/ bop = NotIn` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.well_typed_builtin_app_def] >>
     Cases_on `bop` >> simp[vyperTypeSystemTheory.well_typed_binop_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `eval_operand op q = SOME (bool_to_word answer)` >>
  `!ee. bop_result cx ann bop [expr_type e1; ArrayT (expr_type e1) bd]
          v1 (ArrayV av) ee = INL (BoolV answer)` by
    (simp[exprBopSimDefsTheory.bop_result_def,
          vyperContextTheory.evaluate_builtin_def] >>
     Cases_on `bop = In` >>
     fs[Abbr `answer`, vyperValueOperationTheory.evaluate_binop_def,
        vyperValueOperationTheory.binop_negate_def]) >>
  qexistsl [`[]`, `fin`, `q`, `BoolV answer`] >>
  simp[gasSummaryTheory.gas_marked_exec_def] >>
  conj_tac
  >- (qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` assume_tac) >>
      drule exprSimUnwrapPropsTheory.vv_post_read_result >> simp[] >> metis_tac[]) >>
  simp[loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
       compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,
       venomExecSemanticsTheory.bool_to_word_def] >>
  Cases_on `answer` >> fs[venomExecSemanticsTheory.bool_to_word_def]
QED
Finalise compile_rest_word_membership_sim
