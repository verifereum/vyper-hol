(* Memory-safe invocation of the range loop body. *)
Theory stmtForRangeMemoryLoop
Ancestors
  stmtForRangeMemoryEntry stmtForRangeMemoryRound bodyMemoryDefs stmtSimDeclGas
  gasExemptCert gasSummary gasOutcome gasContext stmtSimForRounds fragGasMode venomExecSemantics
  stmtSimForLoop stmtSimDefs stmtSimProps stmtLowering compileEnv loweringStateRelDefs
  loweringPosts exprLoweringProps vyperState allocaHistory
  stmtForRangeMemoryParts fragExec fragGasPathMem venomState venomInst memSafeRun
Libs
  monadsyntax

Theorem for_body_outcome_mem:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  st.cs_next_var <= sb0.cs_next_var /\
  ret_pc_ok cenv st cc /\ return_buf_frame d cenv st cc /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
  s2.vs_alloca_next = cc.vs_alloca_next /\ alloca_history func s2 /\
  ~s2.vs_halted /\ s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
  stmt_state_rel ctx func bc cx E s2 /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) E /\
  stmt_frag_mem d ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) E ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (E,s2)
    (\res ee t. ?cenv''.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\
        cenv'' = FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)) /\
      cenv_top_ext bc cenv'' ee.scopes /\ stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x s2 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
      s2.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `bc.ce_return_pc = cenv.ce_return_pc /\ bc.ce_return_buf = cenv.ce_return_buf` by
    (fs[for_code_def] >>
     qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `!x w. not_fresh_at st x /\ lookup_var x cc = SOME w ==>
         lookup_var x s2 = SOME w` by metis_tac[] >>
  `ret_pc_ok bc sb0 s2` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `cc`, `st`] >> simp[]) >>
  `return_buf_frame d bc sb0 s2` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `cc`, `st`] >> simp[]) >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sb0`, `sb1`, `s2`,
    `FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)`] mp_tac) >>
  impl_tac
  >- (fs[for_code_def, compile_stmts_env] >> metis_tac[pairTheory.PAIR]) >> simp[]
QED

Theorem for_body_original_frame_mem:
  return_buf_frame d cenv st cc /\ st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
  s2.vs_alloca_next = cc.vs_alloca_next /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x s2 = SOME w ==>
         lookup_var x t = SOME w) /\
  alloca_history func t /\ s2.vs_alloca_next <= t.vs_alloca_next ==>
  return_buf_frame d cenv st t /\ alloca_history func t /\
  cc.vs_alloca_next <= t.vs_alloca_next /\
  (!x w. not_fresh_at st x /\ lookup_var x cc = SOME w ==>
         lookup_var x t = SOME w)
Proof
  strip_tac >>
  `!x w. not_fresh_at st x /\ lookup_var x cc = SOME w ==>
         lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sb0 x` by (fs[not_fresh_at_def] >> decide_tac) >>
     metis_tac[]) >>
  simp[] >> irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `cc`, `st`] >> simp[]
QED

Theorem for_body_pop_mem:
  stmt_state_rel ctx func cbody cx es2 t /\
  cenv_top_ext bc cbody es2.scopes /\ es2.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  lookup_scopes id rest = NONE /\
  (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
  bc with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
            ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv ==>
  stmt_state_rel ctx func cenv cx (es2 with scopes := rest) t
Proof
  strip_tac >>
  `stmt_state_rel ctx func bc cx (es2 with scopes := rest) t` by
    (irule stmt_state_rel_pop_top_ext >> conj_tac
     >- (qexists_tac `sc` >> simp[]) >>
     qexists_tac `cbody` >> simp[]) >>
  irule stmt_state_rel_cenv_cong >> qexists_tac `bc` >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `n = id` >> gvs[]) >>
  qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

(* The body fallthrough emits one JMP; loop-control landings already
   occupy their destination.  No source or memory relation is unfolded. *)
Theorem for_body_route_mem:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb1) ==>
  ?u. gas_path_mem ctx func t 0 (OK u) /\
    u = (if res = INL () then jump_to incr_lbl t else t) /\
    u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    (res = INR BreakException ==> u.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==> u.vs_current_bb = incr_lbl)
Proof
  strip_tac >> Cases_on `res = INL ()`
  >- (gvs[stmt_lands_def] >>
      `?bb. lookup_block sb1.cs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH sb1.cs_current_insts) =
           SOME (mk_inst sb1.cs_next_id JMP [Label incr_lbl] [])` by
        (fs[for_code_def] >> drule_all fn_has_code_same_block >>
         simp[] >> strip_tac >> qexists_tac `bb` >>
         first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      conj_tac
      >- (irule for_range_jump_at_zero_path_mem >> simp[] >>
          simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
               memSafeRunTheory.inst_dload_in_section_def,
               venomExecProofsTheory.step_jmp_behavior] >>
          irule instMemFrontierTheory.below_frontier_no_ranges >> simp[]) >>
      simp[jump_to_def]) >>
  qexists_tac `t` >> gvs[stmt_lands_def] >>
  irule (cj 1 gas_path_mem_rules) >> simp[]
QED

Theorem for_body_scope_mem:
  eval_stmts cx stmts
    (ei with scopes := (FEMPTY |+ (id, entry)) :: ei.scopes) = (res, es2) /\
  lookup_scopes id ei.scopes = NONE /\ es2.scopes = sc :: rest ==>
  lookup_scopes id rest = NONE /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE)
Proof
  strip_tac >>
  `lookup_scopes id rest = NONE` by
    (drule_all vyperEvalPreservesScopesTheory.eval_stmts_preserves_tail_lookup_none >> simp[]) >>
  simp[] >> rpt strip_tac >> Cases_on `n = id` >- gvs[] >>
  drule vyperEvalPreservesScopesTheory.eval_stmts_new_in_head_not_in_tail >>
  disch_then (qspec_then `n` mp_tac) >> simp[]
QED

(* Landing transport consumes the normalized outer relation (for_body_pop_mem)
   and original frame (for_body_original_frame_mem), not the body compiler frame. *)
Theorem for_body_landing_mem:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb1) /\
  stmt_state_rel ctx func cenv cx ee t /\ return_buf_frame d cenv st t /\
  alloca_history func t /\ cc.vs_alloca_next <= t.vs_alloca_next /\
  (!x. not_fresh_at st x ==> x <> cv /\ x <> nv) /\
  (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==> lookup_var x t = SOME v) /\
  (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b) /\
  lookup_var cv t = SOME (i2w (n1 + &k)) /\
  lookup_var ev t = SOME (i2w n2) /\ lookup_var p t = SOME w ==>
  ?u. gas_path_mem ctx func t 0 (OK u) /\
    u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    stmt_state_rel ctx func cenv cx ee u /\ return_buf_frame d cenv st u /\
    alloca_history func u /\ cc.vs_alloca_next <= u.vs_alloca_next /\
    (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==> lookup_var x u = SOME v) /\
    (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP u.vs_allocas a = SOME b) /\
    (res = INR BreakException ==> u.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==> u.vs_current_bb = cond_lbl /\
       lookup_var cv u = SOME (i2w (n1 + &(k + 1))) /\
       lookup_var ev u = SOME (i2w n2) /\ lookup_var p u = SOME w)
Proof
  strip_tac >> drule_all for_body_route_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx ee u /\ return_buf_frame d cenv st u /\
   u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   (!x. lookup_var x u = lookup_var x t)` by
    (Cases_on `res = INL ()` >> gvs[] >>
     simp[stmt_state_rel_jump_to, return_buf_frame_jump_to] >>
     simp[jump_to_def, lookup_var_def]) >>
  qpat_x_assum `u = _` kall_tac >>
  `alloca_history func u` by (irule alloca_history_jump >> simp[] >> qexists_tac `t` >> simp[]) >>
  Cases_on `res = INR BreakException`
  >- (qexists_tac `u` >> simp[] >> metis_tac[]) >>
  `lookup_var cv u = SOME (i2w (n1 + &k))` by metis_tac[] >>
  `gas_path_mem ctx func u 0
    (OK (jump_to cond_lbl (update_var cv (i2w (n1 + &k) + 1w)
        (update_var nv (i2w (n1 + &k) + 1w) u))))` by
    (irule for_incr_zero_path_mem >> fs[for_code_def] >> metis_tac[]) >>
  qabbrev_tac `v = jump_to cond_lbl (update_var cv (i2w (n1 + &k) + 1w)
                    (update_var nv (i2w (n1 + &k) + 1w) u))` >>
  qexists_tac `v` >> conj_tac
  >- (drule_all gas_path_mem_then >> simp[Abbr `v`]) >>
  `!x z. not_fresh_at st x /\ lookup_var x t = SOME z ==> lookup_var x v = SOME z` by
    (rpt strip_tac >> simp[Abbr `v`, jump_to_def, update_var_def, lookup_var_def,
                           finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `res = INL ()` >> gvs[lookup_var_def]) >>
  `return_buf_frame d cenv st v` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `t`, `st`] >>
     simp[Abbr `v`, jump_to_def, update_var_def]) >>
  `alloca_history func v` by
    (irule alloca_history_jump >> simp[Abbr `v`, jump_to_def, update_var_def] >>
     qexists_tac `u` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee v` by
    (simp[Abbr `v`, stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
     fs[for_code_def] >> irule stmt_state_rel_update_var >> simp[]) >>
  simp[Abbr `v`, jump_to_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, stmtSimForPartsTheory.i2w_counter_suc] >>
  fs[for_code_def, lookup_var_def] >> metis_tac[]
QED

Theorem for_cert_start_gas_mem[local]:
  gas_exempt_cert T tops (ctx,func) source (es with gas_obs := gs,s)
    marks out endpoint <=>
  gas_exempt_cert T tops (ctx,func) source (es,s) marks out endpoint
Proof
  eq_tac >> strip_tac >> drule gas_exempt_cert_start_gas_obs
  >- (disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  disch_then (qspec_then `gs` mp_tac) >> simp[]
QED

Theorem for_outcome_start_gas_mem:
  gas_outcome T tops (ctx,func) source (es with gas_obs := gs,s) Q R <=>
  gas_outcome T tops (ctx,func) source (es,s) Q R
Proof
  simp[gas_outcome_def, gas_summary_at_def, gas_marked_exec_def,
       for_cert_start_gas_mem]
QED

Theorem for_frag_start_gas_mem:
  stmt_frag_mem d ctx func cx lc RetQ c m source (es with gas_obs := gs) <=>
  stmt_frag_mem d ctx func cx lc RetQ c m source es
Proof
  simp[stmt_frag_mem_def, for_outcome_start_gas_mem,
       stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_gas_obs,
       immutable_alloca_sep_def]
QED

Theorem for_iteration_mem:
  !d ctx func cenv bc cx lctx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv
   nv n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st vs.
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    return_buf_frame d cenv st cc /\ alloca_history func cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    stmt_frag_mem d ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (esk with <| scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes;
                   gas_obs := [] |>) /\
    gas_admissible (eval_for cx tyv id stmts (Value (IntV (n1 + &k)) :: vs))
      (stmt_res_ok lctx) esk ==>
    gas_outcome T (cx_tops cx) (ctx, func)
      (do push_scope_with_var id tyv (IntV (n1 + &k));
          finally
            (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
            pop_scope
       od) (esk, cc)
      (\res ee t. ?broke. res = INL broke /\
         t.vs_inst_idx = 0 /\ ~t.vs_halted /\
         stmt_state_rel ctx func cenv cx ee t /\
         return_buf_frame d cenv st t /\ alloca_history func t /\
         cc.vs_alloca_next <= t.vs_alloca_next /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x t = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP t.vs_allocas a = SOME b) /\
         (broke ==> t.vs_current_bb = exit_lbl) /\
         (~broke ==> t.vs_current_bb = cond_lbl /\
                     lookup_var cv t = SOME (i2w (n1 + &(k + 1))) /\
                     lookup_var ev t = SOME (i2w n2) /\
                     lookup_var p t = SOME w))
      (\res ee r. ?ex. res = INR ex /\
         !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  rpt gen_tac >> strip_tac >>
  `bc.ce_module_vars = cenv.ce_module_vars /\ bc.ce_module = cenv.ce_module /\
   bc.ce_is_ctor = cenv.ce_is_ctor /\ bc.ce_imm_alloca = cenv.ce_imm_alloca` by
    (fs[for_code_def] >>
     qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `?s2. s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\ ~s2.vs_halted /\
    stmt_state_rel ctx func bc cx
      (esk with scopes := (FEMPTY |+ (id, <|assignable := F; type := tyv;
         value := IntV (n1 + &k); popped := []|>)) :: esk.scopes) s2 /\
    (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
    s2.vs_allocas = cc.vs_allocas /\ s2.vs_alloca_next = cc.vs_alloca_next /\
    alloca_history func s2 /\ gas_path_mem ctx func cc 0 (OK s2)` by
    (qhdtm_assum `for_code` (strip_assume_tac o SRULE [for_code_def]) >>
     `not_local_ptr cenv esk.scopes dv` by metis_tac[] >>
     drule_all for_body_entry_mem >> simp[]) >>
  `!ei scs gs. ei with <|scopes := scs; gas_obs := gs|> =
     (ei with scopes := scs) with gas_obs := gs` by
    simp[evaluation_state_component_equality] >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[for_frag_start_gas_mem] >>
  first_assum (fn th => CHANGED_TAC (pure_rewrite_tac[th])) >>
  pure_rewrite_tac[for_frag_start_gas_mem] >>
  strip_tac >>
  qpat_x_assum `!ei scs gs. _` kall_tac >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl))
    (esk with scopes := (FEMPTY |+ (id, <|assignable := F; type := tyv;
      value := IntV (n1 + &k); popped := []|>)) :: esk.scopes)` by
    (drule for_round_body_admissible >> simp[]) >>
  `!x. not_fresh_at st x ==> x <> dv` by metis_tac[] >>
  drule_all for_body_outcome_mem >> strip_tac >>
  irule for_outcome_zero_prefix_mem >> qexists_tac `s2` >> simp[] >>
  irule for_round_outcome_mem >> conj_tac >- first_assum ACCEPT_TAC >>
  qhdtm_x_assum `gas_outcome` (irule_at Any) >>
  rpt gen_tac >> strip_tac >> suspend "landing"
QED

Resume for_iteration_mem[landing]:
  qpat_x_assum `(\res ee t. _) res ee t` mp_tac >>
  simp_tac bool_ss [boolTheory.BETA_THM] >> strip_tac >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_for _ _ _ _ _) _ _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_stmts _ _) _ _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ bc _ _ s2` kall_tac >>
  conj_tac >- fs[stmt_lands_def] >>
  `ee.scopes <> []` by
    (drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_len >>
     simp[] >> strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `ee.scopes` >- gvs[] >> rename1 `ee.scopes = sc :: rest` >>
  `lookup_scopes id rest = NONE /\
   (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE)` by
    (irule for_body_scope_mem >> qexistsl_tac
       [`cx`, `esk with gas_obs := gs`,
        `<|assignable := F; type := tyv; value := IntV (n1 + &k); popped := []|>`,
        `ee`, `res`, `stmts`] >> simp[] >>
     qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
     simp[evaluation_state_component_equality]) >>
  `stmt_state_rel ctx func cenv cx (ee with scopes := rest) t` by
    (irule for_body_pop_mem >> conj_tac
     >- (qexists_tac `sc` >> simp[]) >>
     qexistsl_tac [`bc`, `cenv''`, `id`] >> simp[] >> fs[for_code_def]) >>
  drule_all for_body_original_frame_mem >> strip_tac >>
  `lookup_var cv t = SOME (i2w (n1 + &k)) /\
   lookup_var ev t = SOME (i2w n2) /\ lookup_var p t = SOME w` by
    (qhdtm_assum `for_code` (strip_assume_tac o SRULE [for_code_def]) >>
     metis_tac[]) >>
  `!x. not_fresh_at st x ==> x <> cv /\ x <> nv` by metis_tac[] >>
  `!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b` by
    metis_tac[] >>
  `res = INL () ==> ~block_is_terminated sb1` by metis_tac[] >>
  drule_all for_body_landing_mem >> strip_tac >>
  qexists_tac `u` >> simp[]
QED
Finalise for_iteration_mem

Theorem for_loop_mem:
  !m d P ctx func cenv bc cx lctx RetQ ty stmts id tyv p sz ainst cv ev dv nv
   n1 n2 cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st k esk cc w.
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    (!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY :: scs) p) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    return_buf_frame d cenv st cc /\ alloca_history func cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (!ei j.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag_mem d ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==> P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    k + m = Num (n2 - n1) /\
    gas_admissible (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &(k + j)))) m))
      (stmt_res_ok lctx) esk /\
    P (esk with gas_obs := []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\ lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) ==>
    gas_outcome T (cx_tops cx) (ctx, func)
      (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &(k + j)))) m)) (esk, cc)
      (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
         s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel ctx func cenv cx ee s /\
         return_buf_frame d cenv st s /\ alloca_history func s /\
         cc.vs_alloca_next <= s.vs_alloca_next /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==> lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP s.vs_allocas a = SOME b))
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >>
  map_every qid_spec_tac [`w`, `cc`, `esk`, `k`, `m`] >>
  Induct_on `m` >> rpt gen_tac >> strip_tac
  >- suspend "zero" >> suspend "step"
QED

Resume for_loop_mem[zero]:
  gvs[] >> simp[Once vyperInterpreterTheory.evaluate_def] >>
  irule gas_outcome_return_path >>
  qexists_tac `jump_to exit_lbl (update_var dv 1w cc)` >>
  conj_tac >- suspend "zero_path" >> suspend "zero_post"
QED

Resume for_loop_mem[zero_path]:
  `!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
     lookup_var x (jump_to exit_lbl (update_var dv 1w cc)) = SOME v` by
    (rpt strip_tac >> simp[jump_to_def, update_var_def, lookup_var_def,
                          finite_mapTheory.FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `return_buf_frame d cenv st (jump_to exit_lbl (update_var dv 1w cc))` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `cc`, `st`] >>
     simp[jump_to_def, update_var_def]) >>
  `alloca_history func (jump_to exit_lbl (update_var dv 1w cc))` by
    (irule alloca_history_jump >> simp[jump_to_def, update_var_def] >>
     qexists_tac `cc` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (esk with gas_obs := [])
     (jump_to exit_lbl (update_var dv 1w cc))` by
    (simp[stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
     conj_tac >- fs[for_code_def] >>
     drule msg_gas_state_frame >>
     disch_then (qspecl_then [`cc.vs_gas_readings`, `cc.vs_inst_idx`, `[]`] mp_tac) >>
     simp[]) >>
  gvs[jump_to_def, update_var_def]
QED
Resume for_loop_mem[zero_post]:
  `n1 + &Num (n2 - n1) = n2` by intLib.ARITH_TAC >>
  simp[gas_marked_path_def] >>
  `gas_path_mem ctx func cc 0 (OK (jump_to exit_lbl (update_var dv 1w cc)))` suffices_by
    simp[gas_marked_path_def] >>
  `bool_to_word (i2w n2 = i2w n2) = (1w:bytes32)` by simp[bool_to_word_def] >>
  qhdtm_assum `for_code` (strip_assume_tac o SRULE [for_code_def]) >>
  drule for_cond_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `cc`, `i2w n2`, `i2w n2`] mp_tac) >>
  simp[bool_to_word_def]
QED
Resume for_loop_mem[step]:
  qpat_x_assum `!k esk cc w. for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ ==> _` (mk_asm "ih") >>
  qpat_x_assum `!ei j gs r2 es2 sc rest. _` (mk_asm "preserve") >>
  `k < Num (n2 - n1)` by decide_tac >>
  `GENLIST (\j. Value (IntV (n1 + &(k + j)))) (SUC m) =
     Value (IntV (n1 + &k)) :: GENLIST (\j. Value (IntV (n1 + &((k + 1) + j)))) m` by
    (simp[rich_listTheory.GENLIST_CONS] >>
     irule listTheory.GENLIST_CONG >> simp[combinTheory.o_DEF]) >>
  `stmt_frag_mem d ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
    (esk with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tyv; value := IntV (n1 + &k); popped := []|>)) :: esk.scopes;
                gas_obs := []|>)` by
    (asm_x "ih" kall_tac >>
     asm_x "preserve" kall_tac >>
     qpat_assum `!ei j. _ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _`
       (qspec_then `esk with gas_obs := []` mp_tac) >>
     disch_then (qspec_then `k` mp_tac) >>
     `!ei scs gs. (ei with gas_obs := gs) with scopes := scs =
        ei with <|scopes := scs; gas_obs := gs|>` by
       simp[evaluation_state_component_equality] >>
     qpat_x_assum `!ei j. _ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _` kall_tac >>
     impl_tac >- simp[] >> disch_tac >> gvs[]) >>
  `not_local_ptr bc (FEMPTY :: esk.scopes) p` by simp[] >>
  `gas_admissible (eval_for cx tyv id stmts
      (Value (IntV (n1 + &k)) :: GENLIST (\j. Value (IntV (n1 + &((k + 1) + j)))) m))
     (stmt_res_ok lctx) esk` by gvs[] >>
  drule_all for_iteration_mem >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome T tops cf source start Final Exit` >>
  qmatch_asmsub_abbrev_tac `gas_outcome T tops cf round start Step StepExit` >>
  qabbrev_tac `Done = (\ee t. Final (INL ()) ee t)` >>
  qabbrev_tac `Next = (\ee t. Step (INL F) ee t)` >>
  qabbrev_tac `R = (\ex ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)` >>
  `gas_outcome T tops cf source start
     (\res ee t. res = INL () /\ Done ee t)
     (\res ee r. ?ex. res = INR ex /\ R ex ee r)` suffices_by
    (strip_tac >> fs[Abbr `cf`, Abbr `start`] >>
     irule for_outcome_consequence_mem >>
     qhdtm_x_assum `gas_outcome` (irule_at Any) >>
     simp[Abbr `Done`, Abbr `Final`, Abbr `R`, Abbr `Exit`] >>
     rpt gen_tac >> strip_tac >> gvs[]) >>
  simp[Abbr `source`, Abbr `start`, Abbr `cf`, Abbr `tops`,
       eval_for_cons_value_round] >>
  irule gas_outcome_bool_round >>
  qexists_tac `Next` >> reverse conj_tac
  >- (irule for_outcome_consequence_mem >>
      qhdtm_x_assum `gas_outcome` (irule_at Any) >>
      conj_tac
      >- simp[Abbr `StepExit`, Abbr `R`] >>
      simp[Abbr `Step`, Abbr `Next`, Abbr `Done`, Abbr `Final`] >>
      rpt gen_tac >> strip_tac >> Cases_on `broke` >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  fs[Abbr `round`] >>
  drule for_round_false_source_mem >> strip_tac >>
  `P (mid with gas_obs := [])` by
    (asm_x "ih" kall_tac >>
     qpat_x_assum `!ei j. _ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _` kall_tac >>
     asm_x "preserve"
       (qspecl_then [`esk with gas_obs := []`, `k`, `gs`, `r2`, `es2`, `sc`, `rest`] mp_tac) >>
     `!ei scs gs. (ei with gas_obs := []) with <|scopes := scs; gas_obs := gs|> =
        ei with <|scopes := scs; gas_obs := gs|>` by
       simp[evaluation_state_component_equality] >>
     gvs[]) >>
  `lookup_scopes id rest = NONE` by
    (asm_x "ih" kall_tac >> asm_x "preserve" kall_tac >>
     irule (cj 1 for_body_scope_mem) >>
     qexistsl_tac [`cx`, `esk with gas_obs := gs`,
       `<|assignable := F; type := tyv; value := IntV (n1 + &k); popped := []|>`,
       `es2`, `r2`, `sc`, `stmts`] >> simp[] >>
     qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
     simp[evaluation_state_component_equality]) >>
  `lookup_scopes id mid.scopes = NONE` by
    (qpat_x_assum `(es2 with scopes := rest) = _` mp_tac >>
     simp[Once evaluation_state_component_equality] >> strip_tac >> gvs[]) >>
  `gas_admissible (eval_for cx tyv id stmts
       (GENLIST (\j. Value (IntV (n1 + &((k + 1) + j)))) m))
       (stmt_res_ok lctx) (mid with gas_obs := [])` by
    (asm_x "ih" kall_tac >> asm_x "preserve" kall_tac >>
     qpat_x_assum `gas_admissible _ _ esk` mp_tac >>
     rewrite_tac[eval_for_cons_value_round] >> disch_tac >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule_all gas_admissible_bind_tail >> simp[]) >>
  fs[Abbr `Next`, Abbr `Step`] >>
  `k + 1 + m = Num (n2 - n1)` by decide_tac >>
  `ret_pc_ok cenv st t` by
    (asm_x "ih" kall_tac >> asm_x "preserve" kall_tac >>
     fs[ret_pc_ok_def] >> metis_tac[]) >>
  asm_x "ih" (qspecl_then [`k + 1`, `mid with gas_obs := []`, `t`, `w`] mp_tac) >>
  (impl_tac
   >- (simp[] >> asm "preserve" ACCEPT_TAC)) >>
  disch_tac >>
  `GENLIST (\j. Value (IntV (n1 + &(k + 1 + j)))) m =
   GENLIST (\j. Value (IntV (n1 + &(j + (k + 1))))) m` by simp[arithmeticTheory.ADD_COMM] >>
  fs[] >>
  irule for_outcome_consequence_mem >>
  qpat_x_assum `gas_outcome _ _ _ (eval_for _ _ _ _ _) _ _ _` (irule_at Any) >>
  asm_x "preserve" kall_tac >>
  qpat_x_assum `!ei j. _ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _` kall_tac >>
  (conj_tac
   >- (simp[Abbr `Exit`, Abbr `R`] >> rpt gen_tac >> strip_tac >>
       Cases_on `res`
       >- (Cases_on `x` >> metis_tac[stmt_exit_loop_ctl]) >>
       metis_tac[])) >>
  simp[Abbr `Done`, Abbr `Final`] >>
  rpt gen_tac >> strip_tac >> gvs[]
QED
Finalise for_loop_mem
