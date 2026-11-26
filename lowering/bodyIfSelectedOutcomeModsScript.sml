(* Counted continuation of the forced Bool read in a linked If. *)
Theory bodyIfSelectedOutcomeMods
Ancestors
  bodyIfArmEntryMods bodyIfArmFinishMods gasOutcomeIfScopeMods gasOutcomeIfSuffixMods
  gasOutcomeFullZeroPrefixMods bodyPtrDefs exprSimDefs venomState vyperState

Theorem if_selected_outcome_mods:
  expr_type e = BaseT BoolT /\
  gas_admissible (eval_stmt cx (If e yes no)) (stmt_res_ok lctx) es /\
  mid.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs ++ tail) =
       (INL (BoolV b), mid with gas_obs := tail)) /\
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmts_env cenv lctx ty (if b then yes else no))
    (stmts_env (gas_shadow_env T cenv) lctx ty
       (if b then MAP gas_shadow_stmt yes else MAP gas_shadow_stmt no))
    (eval_stmts cx (if b then yes else no)) (mid with scopes := FEMPTY :: mid.scopes) /\
  stmts_env cenv lctx ty (if b then yes else no) entry = (cenvb,last) /\
  stmts_env (gas_shadow_env T cenv) lctx ty
    (if b then MAP gas_shadow_stmt yes else MAP gas_shadow_stmt no) sentry =
       (gas_shadow_env T cenvb,slast) /\
  gas_shadow_state entry sentry /\ gas_shadow_state last slast /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code entry last func /\ fn_has_code sentry slast shadow_func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> !bb. MEM bb func.fn_blocks ==>
     phi_prefix_length bb.bb_instructions = 0) /\
  emit_inst JNZ [op; Label tl; Label el] [] pre = ((),post) /\
  fn_has_code pre post func /\
  pre.cs_current_bb = cond.cs_current_bb /\ pre.cs_current_insts = cond.cs_current_insts /\
  entry.cs_current_bb = (if b then tl else el) /\ entry.cs_current_insts = [] /\
  sa.cs_next_var <= entry.cs_next_var /\ local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
  (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t /\
    t.vs_current_bb = cond.cs_current_bb /\ t.vs_inst_idx = LENGTH cond.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) (BoolV b) op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  sa.cs_next_id <= entry.cs_next_id /\ last.cs_next_var <= sb.cs_next_var /\
  (~block_is_terminated last ==>
   emit_inst JMP [Label xl] [] last = ((),after) /\ fn_has_code last after func /\
   sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (ignore_bind push_scope (finally (eval_stmts cx (if b then yes else no)) pop_scope))
    (mid,t,G1,tn1)
    (\H res ee G tn v. ?cf.
       stmt_lands lctx sb res v /\ ~v.vs_halted /\
       (res = INL () ==> ~block_is_terminated sb /\ cf = cenv) /\
       cenv_top_ext cenv cf ee.scopes /\ stmt_state_rel H ctx func cf cx ee v /\
       immutable_frame_mods func cf cx ee v /\ storage_well_formed_on cx ee (FST H) /\
       return_buf_frame d cf sb v /\ alloca_history func v /\ return_buf_sep d cf ee v /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\ s0.vs_alloca_next <= v.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d cf cx ee G tn v /\
       (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x v = SOME w) /\
       (!aid ba. FLOOKUP s0.vs_allocas aid = SOME ba ==> FLOOKUP v.vs_allocas aid = SOME ba) /\
       (!x. not_fresh_at sa x ==>
            FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv es sa s0 cf ee v /\
       (!aid off sz i.
          FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n ba sz'. local_region cenv es.scopes s0 n ba sz' ==>
                       off + sz <= ba \/ ba + sz' <= off) /\
          off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
       halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (mk_asm "condition") >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t /\
    t.vs_current_bb = cond.cs_current_bb /\ t.vs_inst_idx = LENGTH cond.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) (BoolV b) op G1 tn1 t` by
    (gen_tac >> disch_tac >> asm "condition" (qspec_then `H` mp_tac) >> simp[]) >>
  drule_all if_arm_entry_run_mods >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `~(jump_to (if b then tl else el) t).vs_halted` by simp[jump_to_def] >>
  drule_all_then assume_tac gas_outcome_full_mods_scope_cleanup >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`G1`, `jump_to (if b then tl else el) t`, `tn1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (ignore_bind _ _) _ _ _`
    (mp_then Any irule gas_outcome_full_mods_zero_suffix_mono) >>
  conj_tac >-
    (rpt gen_tac >> BETA_TAC >> strip_tac >> conj_tac
     >- (qx_gen_tac `tail` >> first_x_assum (qspec_then `tail` mp_tac) >>
         `(ee with scopes := sc :: ee.scopes) with gas_obs := tail =
          (ee with gas_obs := tail) with scopes := sc :: ee.scopes` by
           simp[evaluation_state_component_equality] >>
         pop_assum SUBST1_TAC >> simp[stmt_exit_ptr_def]) >>
     conj_tac
     >- fs[halt_exit_def, loweringStateRelDefsTheory.halt_rel_def,
           loweringStateRelDefsTheory.accounts_rel_def] >>
     first_assum ACCEPT_TAC) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL (BoolV b), mid)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => pure_rewrite_tac[listTheory.APPEND_NIL, th]) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (gen_tac >> disch_tac >> asm_x "condition" (qspec_then `H` mp_tac) >> simp[]) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all (CONV_RULE (DEPTH_CONV BETA_CONV) if_arm_finish_mods) >>
  disch_then MATCH_ACCEPT_TAC
QED
