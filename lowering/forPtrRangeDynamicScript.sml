Theory forPtrRangeDynamic
Ancestors forPtrRangeTail forPtrEndpointFrame forPtrForcedEndpoint
  exprWordOperand exprLoweringProps exprSimWordArgs stmtSimForRange
  stmtSimForParts stmtSimProps stmtSimDefs stmtLowering loweringPosts
  bodyPtrDefs stmtFragPtr gasSummaryComposePtr compileEnv finite_map list
  vyperInterpreter vyperState vyperValue vyperValueOperation
  venomState exprSimDefs fragExec fragGasPath fragGasPathPtr
  wordArgsPtr valueEncoding loweringSlice integer_word
Libs monadsyntax

Theorem compile_for_range_checked_frag_active_ptr:
  !P Q (d, ctx, PG, func, cx, lctx, RetQ, cenv, env, ty)
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
    expr_sim_ptr d ctx PG func cenv cx fty e1 es /\
    (!gs tv es1.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\ value_has_type tyv (IntV n1) /\
            expr_sim_ptr d ctx PG func cenv cx fty e2 es1 /\
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
       stmt_frag_ptr d ctx PG func cx (InLoop ex inc) RetQ c
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
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
Proof
  map_every qx_gen_tac [`P`,`Q`] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`d`,`ctx`,`PG`,`func`,`cx`,`lctx`,`RetQ`,`cenv`,`env`,`ty`] >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (For id fty (Range e1 e2) bound stmts) sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = ((),sb)` >>
  Cases_on `lower_value compile_expr cenv fty e1 sa` >>
  rename1 `_ = (op1,s1)` >>
  Cases_on `lower_value compile_expr cenv fty e2 s1` >>
  rename1 `_ = (op2,s2)` >>
  suspend "layout"
QED

Resume compile_for_range_checked_frag_active_ptr[layout]:
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   (!x. op1 = Var x ==> not_fresh_at s1 x) /\ (!l. op1 <> Label l)` by
    (qpat_assum `lower_value _ _ _ e1 _ = _`
       (mp_then Any mp_tac exprWordOperandTheory.lower_value_word_shape) >>
     disch_then (qspec_then `env` mp_tac) >> disch_then drule_all >> simp[]) >>
  `cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
   (!x. op2 = Var x ==> not_fresh_at s2 x) /\ (!l. op2 <> Label l)` by
    (qpat_assum `lower_value _ _ _ e2 _ = _`
       (mp_then Any mp_tac exprWordOperandTheory.lower_value_word_shape) >>
     disch_then (qspec_then `env` mp_tac) >> disch_then drule_all >> simp[]) >>
  `for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 s2 = ((),sb)` by
    metis_tac[compile_stmt_for_range_checked] >>
  `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
  `cs_extends s2 sb` by
    (drule_at (Pat `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`)
       for_range_checked_parts >>
     disch_then (qspecl_then [`sa`,`func`] mp_tac) >> simp[] >>
     metis_tac[]) >>
  `fn_has_code sa s2 func /\ fn_has_code s2 sb func` by
    (irule fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    (irule fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  suspend "endpoints"
QED

Resume compile_for_range_checked_frag_active_ptr[endpoints]:
  `eval_stmt cx (For id fty (Range e1 e2) bound stmts) =
   do v1 <- (do raw <- eval_expr cx e1; read_result cx raw od);
      v2 <- (do raw <- eval_expr cx e2; read_result cx raw od);
      rl <- lift_sum (get_range_limits v1 v2);
      check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
      eval_for cx tyv id stmts
        (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od` by
    (irule for_endpoint_stmt_source >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ es` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >> simp[SF ETA_ss] >>
  drule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ e1 _`)
    forced_endpoint_bind_outcome_ptr >>
  disch_then (drule_at (Pat `lower_value _ _ _ e1 sa = _`)) >>
  disch_then irule >> simp[SF ETA_ss] >> suspend "first_premises"
QED

Resume compile_for_range_checked_frag_active_ptr[first_premises]:
  conj_tac >- fs[ret_pc_ok_def] >>
  qexists_tac `lctx` >> reverse conj_tac >- fs[SF ETA_ss] >>
  rpt gen_tac >> strip_tac >> suspend "first_end"
QED

Resume compile_for_range_checked_frag_active_ptr[first_end]:
  qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ (OK t)` mp_tac >>
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  qpat_assum `!tail. _ = (_,mid with gas_obs := tail)`
    (qspec_then `[]` assume_tac) >>
  `?n1. v = IntV n1 /\ value_has_type tyv (IntV n1) /\
    expr_sim_ptr d ctx PG func cenv cx fty e2 (mid with gas_obs := []) /\
    (!gs2 tv2 es2. (do raw <- eval_expr cx e2; read_result cx raw od)
      (mid with gas_obs := gs2) = (INL tv2,es2) ==>
      ?n2. tv2 = IntV n2 /\ value_has_type tyv (IntV n2) /\ P es2)` by
    (qpat_x_assum `!gs tv es1. _` (drule o SRULE [SF ETA_ss]) >> simp[SF ETA_ss]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (simp[] >> drule expr_post_state >> simp[]) >>
  `~t.vs_halted` by
    (drule gas_path_ptr_erase >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ e2 _`)
    forced_endpoint_bind_outcome_ptr >>
  disch_then (drule_at (Pat `lower_value _ _ _ e2 s1 = _`)) >>
  disch_then irule >> simp[SF ETA_ss] >> suspend "second_premises"
QED

Resume compile_for_range_checked_frag_active_ptr[second_premises]:
  conj_tac
  >- (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (fs[ret_pc_ok_def] >> rpt strip_tac >>
      irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  reverse conj_tac >- simp[ghost_inv_gas_obs] >>
  qexists_tac `lctx` >> reverse conj_tac >- fs[SF ETA_ss] >>
  rpt gen_tac >> strip_tac >> suspend "second_end"
QED

Resume compile_for_range_checked_frag_active_ptr[second_end]:
  qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ (OK t')` mp_tac >>
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  qpat_assum `!tail. _ = (_,mid' with gas_obs := tail)`
    (qspec_then `[]` assume_tac) >>
  `?n2. v' = IntV n2 /\ value_has_type tyv (IntV n2) /\
    P (mid' with gas_obs := [])` by
    (qpat_x_assum `!gs2 tv2 es2. _` mp_tac >>
     qpat_x_assum `monad_bind _ _ _ = (INL v',_)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[SF ETA_ss] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by
    (simp[] >> qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac expr_post_state) >> simp[]) >>
  `~t'.vs_halted` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ _ _ t _ _ _ (OK t')`
       (mp_then Any mp_tac gas_path_ptr_erase) >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  suspend "operands"
QED

Resume compile_for_range_checked_frag_active_ptr[operands]:
  `eval_operand op1 t = SOME (i2w n1)` by
    (qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac expr_post_word_operand) >>
     simp[word_value_def, val_to_w256_def]) >>
  `eval_operand op2 t' = SOME (i2w n2)` by
    (qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac expr_post_word_operand) >>
     simp[word_value_def, val_to_w256_def]) >>
  `wb_frame cenv (mid with gas_obs := []) s1 t t'` by
    (qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac expr_post_frame) >> simp[]) >>
  `eval_operand op1 t' = SOME (i2w n1) /\ op_taint tn' op1 = op_taint tn op1` by
    (qpat_assum `wb_frame cenv _ s1 t t'` mp_tac >>
     qpat_assum `ghost_kept cenv _ s1 G tn t G' tn'` mp_tac >>
     qpat_assum `!x. op1 = Var x ==> _` mp_tac >>
     qpat_assum `!l. op1 <> Label l` mp_tac >>
     qpat_assum `eval_operand op1 t = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[word_operand_frame]) >>
  `op_prov G' op1 = op_prov G op1` by
    (irule ghost_kept_operand_prov >> goal_assum (drule_at Any) >> simp[]) >>
  `op_taint tn' op1 = {} /\ op_taint tn' op2 = {} /\
   op_prov G' op1 = NONE /\ op_prov G' op2 = NONE` by
    (qpat_x_assum `ptr_val_ok _ _ _ op1 _ _ _` mp_tac >>
     qpat_x_assum `ptr_val_ok _ _ _ op2 _ _ _` mp_tac >>
     simp[ptr_val_ok_def]) >>
  suspend "tail_entry"
QED

Resume compile_for_range_checked_frag_active_ptr[tail_entry]:
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `monad_bind _ _ _ = (INL v,_)`
       (mp_then Any mp_tac (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >>
     simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM mid'.scopes` by
    (qpat_assum `monad_bind _ _ _ = (INL v',_)`
       (mp_then Any mp_tac (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >>
     simp[]) >>
  `lookup_scopes id mid'.scopes = NONE` by
    metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom] >>
  `wb_frame cenv es sa s0 t` by
    (qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac expr_post_frame) >> simp[]) >>
  `ret_pc_ok cenv s1 t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  `ret_pc_ok cenv s2 t'` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`t`,`s1`] >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  suspend "tail_apply"
QED
Resume compile_for_range_checked_frag_active_ptr[tail_apply]:
  `n1 <= n2 /\ Num (n2-n1) <= bound /\ 0 < Num (n2-n1) ==> Q` by
    (qpat_assum `!gs n1 es1 n2 es2. _ ==> Q` mp_tac >>
     qpat_assum `!tail. _ = (_,mid with gas_obs := tail)`
       (qspec_then `gas_explicit marks' t.vs_gas_readings` mp_tac) >>
     qpat_assum `monad_bind _ _ _ = (INL v',_)` mp_tac >>
     qpat_assum `v = IntV n1` mp_tac >>
     qpat_assum `v' = IntV n2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[SF ETA_ss] >> metis_tac[]) >>
  `ghost_inv d cenv cx (mid' with gas_obs := []) G' tn' t'` by
    simp[ghost_inv_gas_obs] >>
  qpat_assum `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac for_range_checked_tail_outcome_ptr) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand op1 t' = _`)) >>
  disch_then (drule_at (Pat `eval_operand op2 t' = _`)) >>
  disch_then (mp_tac o Q.INST [`P` |-> `P`, `PG` |-> `PG`, `RetQ` |-> `RetQ`] o SPEC_ALL) >>
  impl_tac >- (simp[] >> suspend "tail_requirements") >>
  strip_tac >> suspend "tail_post"
QED
Resume compile_for_range_checked_frag_active_ptr[tail_requirements]:
  conj_tac
  >- (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s1 x \/ not_fresh_at s2 x` by metis_tac[] >>
      metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  conj_tac >- suspend "body_callback" >>
  conj_tac
  >- (rpt strip_tac >>
      `Q` by (first_x_assum irule >> simp[] >> decide_tac) >>
      `value_has_type tyv (IntV (n1 + &j))` by
        (drule_all range_value_has_type >> simp[]) >>
      qpat_x_assum `!ei n1 j gs r2 es2 sc rest. _` irule >>
      metis_tac[]) >>
  qpat_assum `gas_admissible _ _ mid'` mp_tac >>
  qpat_assum `v' = IntV n2` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED
Resume compile_for_range_checked_frag_active_ptr[body_callback]:
  rpt strip_tac >>
  `Q` by (first_x_assum irule >> simp[] >> decide_tac) >>
  `value_has_type tyv (IntV (n1 + &j))` by
    (drule_all range_value_has_type >> simp[]) >>
  `!ee sc gs. (ee with <|scopes := sc; gas_obs := gs|>) =
      ((ee with scopes := sc) with gas_obs := gs)` by
    simp[evaluation_state_component_equality] >>
  once_asm_rewrite_tac[] >>
  rewrite_tac[stmt_frag_ptr_initial_obs] >>
  qpat_x_assum `!st0 c st1 ex inc ei n1 j. _` irule >>
  simp[] >> qexists_tac `s2` >> simp[]
QED
Resume compile_for_range_checked_frag_active_ptr[tail_post]:
  qpat_x_assum `v' = IntV n2` SUBST_ALL_TAC >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac gas_outcome_ptr_conseq) >>
  disch_then irule >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> qexists_tac `cenv` >>
  simp[cenv_top_ext_refl] >>
  suspend "post_frame"
QED
Resume compile_for_range_checked_frag_active_ptr[post_frame]:
  `(!x w. not_fresh_at s1 x /\ lookup_var x t = SOME w ==>
      lookup_var x t'' = SOME w) /\
   (!x. not_fresh_at s1 x ==> FLOOKUP G'' x = FLOOKUP G x /\
      op_taint tn'' (Var x) = op_taint tn (Var x))` by
    (qpat_assum `wb_frame cenv _ s1 t t'` mp_tac >>
     qpat_assum `ghost_kept cenv _ s1 G tn t G' tn'` mp_tac >>
     qpat_assum `s1.cs_next_var <= s2.cs_next_var` mp_tac >>
     qpat_assum `!x w. not_fresh_at s2 x /\ _ ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at s2 x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 5 strip_tac >>
     irule for_endpoint_prefix_frame >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexists_tac `s2` >> simp[]) >>
  qpat_assum `wb_frame cenv es sa s0 t` mp_tac >>
  qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G tn` mp_tac >>
  qpat_assum `sa.cs_next_var <= s1.cs_next_var` mp_tac >>
  qpat_assum `!x w. not_fresh_at s1 x /\ _ ==> _` mp_tac >>
  qpat_assum `!x. not_fresh_at s1 x ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 5 strip_tac >>
  irule for_endpoint_prefix_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexists_tac `s1` >> simp[]
QED
Finalise compile_for_range_checked_frag_active_ptr
