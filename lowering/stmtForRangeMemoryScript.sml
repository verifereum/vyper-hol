(* Memory-safe checked range fragments. Endpoint paths, checked entry and
   counted loop execution preserve allocation history and return-buffer frames. *)
Theory stmtForRangeMemory
Ancestors
  stmtSimDefs exprSimMemDefs stmtLowering compileEnv vyperInterpreter
  vyperState vyperTypeSystem stmtSimForRange stmtForRangeEndpointsMemory
  stmtForRangeChecksMemory stmtForRangeMemoryLoop stmtForRangeMemoryStart
  stmtLoweringMono exprLoweringProps stmtSimProps stmtSimForParts
  exprLowering loweringPosts emitHelperProps stmtSimForced fragExec
  bodyMemoryDefs exprSimWordArgs freshWrites vyperEvalPreservesScopes
  gasOutcome gasSummary vyperValue stmtSimForLoop venomInst stmtForRangeMemoryRound
  exprWordOperand exprSafeOperand exprSimDefs exprSimProps
  stmtForRangeCheckedStartMemory valueEncoding loweringSlice venomExecSemantics venomState

Theorem compile_for_range_checked_frag_active_mem:
  !P Q d (ctx, func, cx, lctx, RetQ, cenv, env, ty)
   id fty e1 e2 bound stmts es tyv.
    is_int_type fty /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\ bound < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tyv /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tyv /\
    expr_sim_mem ctx func cenv cx fty e1 es /\
    (!gs tv es1.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\ value_has_type tyv (IntV n1) /\
            expr_sim_mem ctx func cenv cx fty e2 es1 /\
            !gs2 tv2 es2.
              (do raw <- eval_expr cx e2; read_result cx raw od)
                (es1 with gas_obs := gs2) = (INL tv2, es2) ==>
              ?n2. tv2 = IntV n2 /\ value_has_type tyv (IntV n2) /\
                   P es2) /\
    (!gs n1 es1 n2 es2.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL (IntV n1), es1) /\
       (do raw <- eval_expr cx e2; read_result cx raw od) es1 =
         (INL (IntV n2), es2) /\
       n1 <= n2 /\ Num (n2 - n1) <= bound /\ 0 < Num (n2 - n1) ==> Q) /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    (!x t. FLOOKUP env.var_types x = SOME t ==>
           well_formed_type env.type_defs t) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    (!st0 c st1 ex inc ei n1 j.
       declare_local cenv id fty st0 = (c, st1) /\
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) ==>
       stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei n1 j gs r2 es2 sc rest.
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) =
         (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
Proof
  ntac 3 gen_tac >>
  CONV_TAC (RAND_CONV (fn tm =>
    let val v = variant (free_vars tm) (mk_var ("packed", fst (dom_rng (type_of tm))))
    in GSYM (ETA_CONV (mk_abs (v,mk_comb (tm,v)))) end)) >>
  qx_gen_tac `packed` >> PairCases_on `packed` >>
  simp[pairTheory.UNCURRY_DEF] >> rpt gen_tac >> strip_tac >>
  rename1 `stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty _) _ es` >>
  rw[stmt_frag_mem_def] >>
  fs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, pairTheory.pair_case_eq] >>
  Cases_on `compile_stmt cenv lctx ty (For id fty (Range e1 e2) bound stmts) sa` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `lower_value compile_expr cenv fty e1 sa` >>
  rename1 `_ = (op1,s1)` >>
  Cases_on `lower_value compile_expr cenv fty e2 s1` >>
  rename1 `_ = (op2,s2)` >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id` by
    (qpat_assum `lower_value _ _ _ e1 _ = _`
      (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
   s1.cs_next_id <= s2.cs_next_id` by (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 s2 = ((),r)` by
    (drule_all (SRULE [] compile_stmt_for_range_checked) >>
     disch_then (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  drule for_range_checked_parts >> disch_then (qspecl_then [`sa`,`func`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[cs_extends_trans]) >> strip_tac >>
  suspend "endpoints"
QED

Resume compile_for_range_checked_frag_active_mem[endpoints]:
  `eval_stmt cx (For id fty (Range e1 e2) bound stmts) =
   bind (bind (eval_expr cx e1) (read_result cx)) (\v1.
   bind (bind (eval_expr cx e2) (read_result cx)) (\v2.
   bind (lift_sum (get_range_limits v1 v2)) (\rl.
   bind (check (compatible_bound (Dynamic bound) (LENGTH
      (GENLIST (\j. IntV (FST rl + &j)) (SND rl)))) "For too long") (\u.
   eval_for cx tyv id stmts (GENLIST (\j. IntV (FST rl + &j)) (SND rl))))))` by
    (pure_once_rewrite_tac[evaluate_def] >>
     pure_once_rewrite_tac[evaluate_def] >>
     simp[lift_option_type_def, ignore_bind_def, bind_assoc, bind_return]) >>
  `fn_has_code sa s1 func` by
    (metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]) >>
  qpat_assum `eval_stmt _ _ = _` (fn th =>
    rule_assum_tac (REWRITE_RULE [th]) >> rewrite_tac[th]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >> goal_assum (drule_at Any)) >>
  irule for_expr_endpoint_outcome_mem >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `expr_exit _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `ex` >> Cases_on `r'` >>
      simp[stmt_exit_def, exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      simp[stmt_exit_def, exprSimDefsTheory.expr_exit_def]) >>
  qexistsl_tac [`cenv`,`op1`,`sa`,`s1`,`fty`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `expr_post _ _ _ _ e1 es sa s1 s0 ee1 v1 op1 t1` >>
  `?gs1. bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gs1) = (INL v1,ee1)` by
    (qpat_x_assum `!tail. ?gs. _ = (INL v1,_)`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee1.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_assum `!gs tv es1. bind (eval_expr cx e1) _ _ = _ ==> _`
    (qspecl_then [`gs1`,`v1`,`ee1`] mp_tac) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome T _ _ suffix (ee1,t1) _ _` >>
  `gas_admissible suffix (stmt_res_ok lctx) ee1` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!tail. ?gs. _ = (INL v1,_)`
       (qspec_then `gs` (qx_choose_then `gs0` assume_tac)) >>
     qpat_assum `gas_admissible (bind (bind (eval_expr cx e1) _) _) _ es`
       mp_tac >>
     pure_rewrite_tac[gasContextTheory.gas_admissible_def] >>
     disch_then (qspecl_then [`gs0`,`res`,`ee`] mp_tac) >>
     qpat_x_assum `suffix _ = _` mp_tac >>
     simp[bind_def, Abbr `suffix`]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok ee1` by
    (irule forced_then_admissible >> simp[Abbr `suffix`] >>
     goal_assum (drule_at Any)) >>
  `fn_has_code s1 s2 func` by
    (metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  `local_ptrs_reserved cenv s1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee1 t1` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  qunabbrev_tac `suffix` >>
  irule for_expr_endpoint_outcome_mem >> simp[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `expr_exit _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `ex` >> Cases_on `r'` >>
      simp[stmt_exit_def, exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      simp[stmt_exit_def, exprSimDefsTheory.expr_exit_def]) >>
  qexistsl_tac [`cenv`,`op2`,`s1`,`s2`,`fty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `expr_post _ _ _ _ e2 ee1 s1 s2 t1 ee2 v2 op2 t2` >>
  `?gs2. bind (eval_expr cx e2) (read_result cx)
     (ee1 with gas_obs := gs2) = (INL v2,ee2)` by
    (qpat_x_assum `!tail. ?gs. _ = (INL v2,_)`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee2.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_assum `!gs2 tv2 es2. bind (eval_expr cx e2) _ _ = _ ==> _`
    (qspecl_then [`gs2`,`v2`,`ee2`] mp_tac) >> simp[] >> strip_tac >>
  suspend "checked_tail"
QED

Resume compile_for_range_checked_frag_active_mem[checked_tail]:
  `?gs0. bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gs0) = (INL v1,ee1 with gas_obs := gs2)` by
    (qpat_x_assum `!tail. ?gs. _ = (INL v1,_)`
       (qspec_then `gs2` mp_tac) >> simp[]) >>
  `n1 <= n2 /\ Num (n2-n1) <= bound /\ 0 < Num (n2-n1) ==> Q` by
    (strip_tac >>
     qpat_x_assum `!gs n1 es1 n2 es2. _ ==> Q`
       (qspecl_then [`gs0`,`n1`,`ee1 with gas_obs := gs2`,`n2`,`ee2`] mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee2 t2 /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t2 = SOME w) /\
   (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
              FLOOKUP t2.vs_allocas aid = SOME ent)` by
    (qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `sa.cs_next_var <= s1.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[expr_post_def] >> rpt strip_tac >>
     metis_tac[not_fresh_at_mono]) >>
  `s0.vs_alloca_next <= t2.vs_alloca_next` by decide_tac >>
  `return_buf_frame d cenv s2 t2` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `ret_pc_ok cenv s2 t2` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `lookup_scopes id ee2.scopes = NONE` by
    (qpat_assum `bind (eval_expr cx e1) _ _ = (INL v1,ee1)` mp_tac >>
     qpat_assum `bind (eval_expr cx e2) _ _ = (INL v2,ee2)` mp_tac >>
     qpat_assum `lookup_scopes id es.scopes = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt disch_tac >>
     qpat_x_assum `bind (eval_expr cx e2) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
          forced_eval_expr_preserves_scopes_dom)) >>
     simp[] >> strip_tac >>
     qpat_x_assum `bind (eval_expr cx e1) _ _ = _`
       (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
          forced_eval_expr_preserves_scopes_dom)) >> simp[] >> strip_tac >>
     irule lookup_scopes_none_map_fdom >> qexists_tac `es.scopes` >> simp[] >>
     metis_tac[]) >>
  `(!x. op1 = Var x ==> not_fresh_at s1 x) /\ (!l. op1 <> Label l)` by
    (qpat_assum `lower_value _ _ _ e1 _ = _` mp_tac >>
     qpat_assum `well_typed_expr packed6 e1` mp_tac >>
     qpat_assum `!x t. FLOOKUP packed6.var_types x = SOME t ==> _` mp_tac >>
     qpat_assum `is_word_type (expr_type e1)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `packed6` mp_tac) >> metis_tac[]) >>
  `!x. op2 = Var x ==> not_fresh_at s2 x` by
    (qpat_assum `lower_value _ _ _ e2 _ = _` mp_tac >>
     qpat_assum `well_typed_expr packed6 e2` mp_tac >>
     qpat_assum `!x t. FLOOKUP packed6.var_types x = SOME t ==> _` mp_tac >>
     qpat_assum `is_word_type (expr_type e2)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `packed6` mp_tac) >> metis_tac[]) >>
  `eval_operand op1 t1 = SOME (i2w n1)` by
    (qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type e1) = SOME tyv` mp_tac >>
     qpat_assum `is_word_type (expr_type e1)` mp_tac >>
     qpat_assum `v1 = IntV n1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_post_def, expr_val_rel_def] >> rpt strip_tac >>
     simp[typed_val_to_w256_word_value,word_value_def,val_to_w256_def]) >>
  `eval_operand op2 t2 = SOME (i2w n2)` by
    (qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type e2) = SOME tyv` mp_tac >>
     qpat_assum `is_word_type (expr_type e2)` mp_tac >>
     qpat_assum `v2 = IntV n2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_post_def, expr_val_rel_def] >> rpt strip_tac >>
     simp[typed_val_to_w256_word_value,word_value_def,val_to_w256_def]) >>
  `!x w. not_fresh_at s1 x /\ lookup_var x t1 = SOME w ==>
         lookup_var x t2 = SOME w` by fs[expr_post_def] >>
  `eval_operand op1 t2 = SOME (i2w n1)` by
    (Cases_on `op1` >> gvs[eval_operand_def]) >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  qabbrev_tac `bad = (
    (if (if is_signed_type fty then SGT else GT) = SGT
     then word_gt (i2w n1 : bytes32) (i2w n2)
     else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) \/
    w2n (i2w n2 - i2w n1 : bytes32) > w2n (n2w bound : bytes32))` >>
  `(bad ==> ?t. gas_marked_path T ctx func t2 0 (Abort Revert_abort t)) /\
   (~bad ==> ?cc w. gas_path_mem ctx func t2 0 (OK cc) /\
     cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
     stmt_state_rel ctx func cenv cx ee2 cc /\
     lookup_var cv cc = SOME (i2w n1) /\ lookup_var ev cc = SOME (i2w n2) /\
     lookup_var p cc = SOME w /\
     FLOOKUP cc.vs_allocas s2.cs_next_id = SOME (w2n w,type_memory_bytes cenv fty) /\
     return_buf_frame d cenv s2 cc /\ ret_pc_ok cenv s2 cc /\
     alloca_history func cc /\ t2.vs_alloca_next <= cc.vs_alloca_next /\
     (!aid ent. FLOOKUP t2.vs_allocas aid = SOME ent ==>
                 FLOOKUP cc.vs_allocas aid = SOME ent) /\
     (!x. not_fresh_at s2 x ==> lookup_var x cc = lookup_var x t2))` by
    (qunabbrev_tac `bad` >> pure_rewrite_tac[DE_MORGAN_THM] >>
     irule (Q.INST [`cmp` |-> `if is_signed_type fty then SGT else GT`]
       (SPEC_ALL for_range_checked_start_mem)) >>
     simp[] >> reverse conj_tac
     >- (Cases_on `is_signed_type fty` >> simp[]) >>
     qexistsl_tac [`entry_lbl`,`g1`,`g2`,`s2.cs_next_id + 2`,`s2.cs_next_id + 1`,
       `op1`,`op2`,`rv`,`z1`,`z2`] >>
     simp[] >> conj_tac
     >- (qpat_assum `local_ptrs_reserved cenv s2` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> disch_tac >> rpt strip_tac >> gvs[] >>
         irule local_ptrs_reserved_fresh >> qexists_tac `s2` >> simp[]) >>
     conj_tac
     >- (qpat_assum `!x. op1 = Var x ==> _` mp_tac >>
         qpat_assum `!x. op2 = Var x ==> _` mp_tac >>
         qpat_assum `s1.cs_next_var <= s2.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[not_fresh_at_def] >> rpt strip_tac >>
         first_x_assum drule >> simp[]) >>
     conj_tac
     >- (POP_ASSUM_LIST (K all_tac) >> simp[not_fresh_at_def] >>
         rpt strip_tac >> gvs[]) >>
     qpat_assum `lookup_block s2.cs_current_bb _ = _`
       (mp_then Any mp_tac lookup_block_fn_insts) >> simp[]) >>
  `((if is_signed_type fty then word_gt (i2w n1 : bytes32) (i2w n2)
      else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) <=> n2 < n1) /\
   (n1 <= n2 ==> Num (n2-n1) < dimword (:256) /\
      w2n (i2w n2 - i2w n1 : bytes32) = Num (n2-n1))` by
    (qpat_assum `is_int_type fty` mp_tac >>
     qpat_assum `evaluate_type _ fty = SOME tyv` mp_tac >>
     qpat_assum `value_has_type tyv (IntV n1)` mp_tac >>
     qpat_assum `value_has_type tyv (IntV n2)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     irule range_end_words >> simp[] >>
     qexistsl_tac [`get_tenv cx`,`tyv`] >> simp[]) >>
  `bad <=> n2 < n1 \/ bound < Num (n2-n1)` by
    (qunabbrev_tac `bad` >>
     qpat_assum `(_ <=> n2 < n1)` mp_tac >>
     qpat_assum `n1 <= n2 ==> _` mp_tac >>
     qpat_assum `bound < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     Cases_on `is_signed_type fty` >> fs[] >>
     Cases_on `n1 <= n2` >> fs[] >> intLib.ARITH_TAC) >>
  Cases_on `n1 <= n2`
  >- suspend "valid_order"
  >> `bad` by (qpat_assum `bad <=> _` mp_tac >>
      qpat_assum `~(n1 <= n2)` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
      simp[GSYM integerTheory.INT_NOT_LE])
  >> qpat_x_assum `bad ==> _` drule >> strip_tac
  >> qpat_assum `gas_marked_path T ctx func t2 0 _` mp_tac
  >> qpat_assum `v2 = IntV n2` mp_tac
  >> qpat_assum `~(n1 <= n2)` mp_tac
  >> POP_ASSUM_LIST (K all_tac) >> rpt disch_tac
  >> simp[get_range_limits_def, lift_sum_def, bind_def, raise_def]
  >> rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac
  >> simp[gas_summary_at_def, gas_marked_exec_def]
  >> qexistsl_tac [`INR (Error (RuntimeError "no range"))`,`ee2`,
       `Abort Revert_abort t`]
  >> simp[bind_def, raise_def, exit_result_def, stmt_exit_def, expr_exit_def]
QED

Resume compile_for_range_checked_frag_active_mem[valid_order]:
  Cases_on `Num (n2-n1) <= bound`
  >- suspend "valid_bound"
  >> `bad` by (qpat_assum `bad <=> _` mp_tac >>
      qpat_assum `~(Num (n2-n1) <= bound)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[])
  >> qpat_x_assum `bad ==> _` drule >> strip_tac
  >> qpat_assum `gas_marked_path T ctx func t2 0 _` mp_tac
  >> qpat_assum `v2 = IntV n2` mp_tac
  >> qpat_assum `n1 <= n2` mp_tac
  >> qpat_assum `~(Num (n2-n1) <= bound)` mp_tac
  >> POP_ASSUM_LIST (K all_tac) >> rpt disch_tac
  >> simp[get_range_limits_def, lift_sum_def, bind_def, return_def,
       compatible_bound_def, check_def, assert_def]
  >> rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac
  >> simp[gas_summary_at_def, gas_marked_exec_def]
  >> qexistsl_tac [`INR (Error (RuntimeError "For too long"))`,`ee2`,
       `Abort Revert_abort t`]
  >> simp[bind_def, return_def, assert_def, raise_def,
       exit_result_def, stmt_exit_def, expr_exit_def]
QED

Resume compile_for_range_checked_frag_active_mem[valid_bound]:
  `~bad` by (qpat_assum `bad <=> _` mp_tac >>
    qpat_assum `n1 <= n2` mp_tac >>
    qpat_assum `Num (n2-n1) <= bound` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[integerTheory.INT_NOT_LT]) >>
  qpat_x_assum `~bad ==> _` drule >> strip_tac >>
  simp[get_range_limits_def, lift_sum_def, bind_def, return_def,
       compatible_bound_def, check_def, assert_def] >>
  simp[bind_def, return_def, assert_def] >>
  qabbrev_tac `aa = mk_inst s2.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv fty))] [p]` >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved bc sb0` by
    (drule_all declare_local_reserved >> strip_tac >>
     irule local_ptrs_reserved_next_var >>
     qexists_tac `s2 with cs_next_var := s2.cs_next_var + 1` >> simp[]) >>
  `s2.cs_next_var + 9 <= sj.cs_next_var` by
    (qpat_assum `!c lc sa sb. compile_stmts _ _ _ _ _ = _ ==> _`
       (qspecl_then [`bc`,`InLoop exit_lbl incr_lbl`,`sb0`,`sb1`] mp_tac) >> simp[]) >>
  `for_code func cenv bc ty stmts id tyv p (type_memory_bytes cenv fty) aa cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl (s2.cs_next_id + 12) (s2.cs_next_id + 13)
    (s2.cs_next_id + 14) bbb sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2)
    sb0 sb1 sj` by
    (simp[for_code_def, Abbr `aa`, mk_inst_def, block_is_terminated_def] >>
     simp[is_terminator_def, not_fresh_at_def] >>
     conj_tac
     >- (qpat_assum `lookup_block s2.cs_current_bb _ = _`
           (mp_then Any mp_tac lookup_block_fn_insts) >> simp[mk_inst_def]) >>
     reverse conj_tac
     >- (qpat_assum `is_int_type fty` mp_tac >>
         qpat_assum `evaluate_type _ fty = SOME tyv` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         Cases_on `fty` >> simp[] >> rename1 `BaseT bt` >>
         Cases_on `bt` >>
         simp[evaluate_type_def, AllCaseEqs(), type_memory_size_def] >>
         rpt strip_tac >> gvs[type_memory_size_def]) >>
     gen_tac >> rpt conj_tac >>
     irule local_ptrs_reserved_fresh >> qexists_tac `s2` >> simp[]) >>
  suspend "loop_ready"
QED

Resume compile_for_range_checked_frag_active_mem[loop_ready]:
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY :: scs) p` by
    (rpt strip_tac >> irule local_ptrs_reserved_not_live >> conj_tac
     >- (qexistsl_tac [`id`,`type_memory_bytes cenv fty`] >> simp[lookup_scopes_def]) >>
     qexists_tac `sb0` >> simp[]) >>
  `!x. not_fresh_at s2 x ==> x <> dv /\ x <> cv /\ x <> nv` by
    (map_every (fn q => qpat_assum q SUBST1_TAC) [`dv = _`,`cv = _`,`nv = _`] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  `!j. j < Num (n2-n1) ==> value_has_type tyv (IntV (n1 + &j))` by
    (qspecl_then [`tyv`,`n1`,`n2`] mp_tac range_value_has_type >> simp[]) >>
  `!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2-n1) ==>
    stmt_frag_mem d ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id, <|assignable := F; type := tyv;
        value := IntV (n1 + &j); popped := []|>)) :: ei.scopes)` by
    (rpt strip_tac >> `Q` by (first_x_assum irule >> simp[] >> decide_tac) >>
     qpat_x_assum `!st0 c st1 ex inc ei n1 j. _` irule >> simp[] >>
     qexistsl_tac [`s2`,`s2 with cs_next_var := s2.cs_next_var + 1`] >> simp[]) >>
  `gas_admissible
    (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))))
    (stmt_res_ok lctx) ee2` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!tail. ?gs. _ = (INL v2,_)`
       (qspec_then `gs` (qx_choose_then `gs0` assume_tac)) >>
     qpat_assum `gas_admissible (bind (bind (eval_expr cx e2) _) _) _ ee1` mp_tac >>
     pure_rewrite_tac[gasContextTheory.gas_admissible_def] >>
     disch_then (qspecl_then [`gs0`,`res`,`ee`] mp_tac) >>
     simp[bind_def, get_range_limits_def, lift_sum_def, return_def,
       compatible_bound_def, check_def, assert_def]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
    (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(0+j))) (Num (n2-n1)))) (ee2,cc)
    (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
      s.vs_inst_idx = 0 /\ ~s.vs_halted /\ stmt_state_rel ctx func cenv cx ee s /\
      return_buf_frame d cenv s2 s /\ alloca_history func s /\
      cc.vs_alloca_next <= s.vs_alloca_next /\
      (!x v. not_fresh_at s2 x /\ lookup_var x cc = SOME v ==> lookup_var x s = SOME v) /\
      (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP s.vs_allocas a = SOME b))
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)` by
    (irule for_loop_mem >> ntac 4 (conj_tac >- simp[]) >>
     conj_tac >- (qexists_tac `lctx` >> simp[]) >>
     ntac 3 (conj_tac >- simp[]) >>
     qexists_tac `P` >> qhdtm_assum `for_code` (irule_at Any) >>
     qexistsl_tac [`w`,`n2`] >> simp[Abbr `aa`, mk_inst_def] >>
     conj_tac >- (qpat_assum `ee2.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     rpt strip_tac >> `Q` by (first_x_assum irule >> simp[] >> decide_tac) >>
     qpat_x_assum `!ei n1 j gs r2 es2 sc rest. _` irule >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "finish_loop"
QED

Resume compile_for_range_checked_frag_active_mem[finish_loop]:
  `bind (return (n1,Num (n2-n1))) (\rl.
     bind (assert (SND rl <= bound) (Error (RuntimeError "For too long")))
       (\u. eval_for cx tyv id stmts
         (GENLIST (\j. IntV (FST rl + &j)) (SND rl)))) =
   eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1)))` by
    simp[FUN_EQ_THM, bind_def, return_def, assert_def] >>
  asm_rewrite_tac [] >>
  qpat_x_assum `gas_outcome T _ _ _ _ _ _` mp_tac >> simp[] >>
  disch_then (mp_then Any mp_tac for_outcome_zero_prefix_mem) >>
  disch_then (qspec_then `t2` mp_tac) >> simp[] >>
  disch_then (mp_then Any mp_tac for_outcome_consequence_mem) >>
  simp[] >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[stmt_lands_def, cenv_top_ext_def] >>
  conj_tac >- simp[block_is_terminated_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s2 x` by (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> decide_tac) >>
      first_x_assum irule >> simp[]) >>
  `return_buf_frame d cenv sa t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     rpt strip_tac >>
     `not_fresh_at s2 x` by (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> decide_tac) >>
     first_x_assum irule >> simp[]) >>
  Cases_on `d`
  >- (qpat_x_assum `return_buf_frame NONE _ _ _` mp_tac >>
      rewrite_tac[return_buf_frame_def]) >>
  rename1 `SOME desc` >> PairCases_on `desc` >>
  `sa.cs_next_var <= r.cs_next_var` by
    (drule (SIMP_RULE std_ss [cs_mono_def] (cj 1 compile_stmt_cs_mono)) >> simp[]) >>
  qpat_x_assum `return_buf_frame _ cenv sa t` mp_tac >>
  rewrite_tac[return_buf_frame_def] >> strip_tac >>
  qexistsl_tac [`x`,`slot_size`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule not_fresh_at_mono >> qexists_tac `sa` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise compile_for_range_checked_frag_active_mem
