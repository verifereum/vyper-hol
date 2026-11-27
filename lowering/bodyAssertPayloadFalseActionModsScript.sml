(* The false assertion edge enters the actual reached Raise fragment. *)
Theory bodyAssertPayloadFalseActionMods
Ancestors
  bodyFullPostsMods bodyFullShared bodyFullIfExpReach bodyAugGuardedPrefixMods
  gasOutcomeFullPostMods fragGasOriginPtr gasExplicitSites bodyForRangeScalarFrameMods
  stmtSimProps stmtSimDefs exprSimDefs exprLoweringProps loweringPosts
  loweringStateRelDefs bodyPtrDefs bodyMemoryDefs freshWrites compileEnv
  allocaHistory ptrDiscipline contextRawReachable unitTransformDefs fragExec
  gasShadow stmtLowering vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomExecSemantics venomState

Theorem assert_payload_false_action_mods:
  stmt_env cenv lctx ty (Raise rr) entry = (cenv,last) /\
  stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Raise rr)) sentry =
    (gas_shadow_env T cenv,slast) /\
  gas_shadow_state entry sentry /\ gas_shadow_state last slast /\
  fn_has_code entry last func /\ fn_has_code sentry slast shadow_func /\
  entry.cs_current_insts = [] /\ sa.cs_next_var <= entry.cs_next_var /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (BoolV F),mid with gas_obs := tail)) /\
  ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV F) op t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK t,G1,tn1)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK (jump_to entry.cs_current_bb t),G1,tn1)) /\
  gas_admissible (eval_stmt cx (Raise rr)) (stmt_res_ok lctx) mid /\
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise rr))
    (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Raise rr)))
    (eval_stmt cx (Raise rr)) mid /\
  (!ee res ee'. eval_stmt cx (Raise rr) ee = (res,ee') ==>
    res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (Raise rr)) (mid,t,G1,tn1) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  irule augassign_zero_prefix_guarded_mods >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G1`, `jump_to entry.cs_current_bb t`, `tn1`] >>
  rpt conj_tac
  >~ [`gas_origin_ptr_path _ _ [] _`]
  >- first_assum ACCEPT_TAC >>
  qpat_x_assum `stmt_frag_full_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_full_mods_def] >>
  disch_then (qspecl_then [`st0`, `entry`, `last`, `sentry`, `slast`,
    `jump_to entry.cs_current_bb t`, `G1`, `tn1`, `cenv`] mp_tac) >>
  (impl_tac >- suspend "entry") >>
  strip_tac >> irule gas_outcome_full_mods_post_source >>
  first_assum (irule_at Any) >> conj_tac
  >- suspend "non_normal" >> simp[]
QED

Resume assert_payload_false_action_mods[entry]:
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    ((qpat_assum `storage_trace_domain _ _ _` mp_tac >>
     simp[storage_trace_domain_def, Abbr `H0`] >> (metis_tac[storage_trace_domain_def, Abbr `H0`]))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (BoolV F),mid)` by
    (`mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!tail. bind _ _ _ = _`
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV) o Q.SPEC `[]`) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H0 es.storage_trace` by (drule_all valid_horizon_frame >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by (first_assum irule >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       expr_post_mods H _ _ _ _ e es sa cond s0 mid (BoolV F) op t /\ _`
       (qspec_then `H0`
          (drule_then (strip_assume_tac o
             REWRITE_RULE [expr_post_mods_def, expr_post_def]))) >>
     fs[]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       expr_post_mods H _ _ _ _ e es sa cond s0 mid (BoolV F) op t /\ _`
       (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o
       REWRITE_RULE [expr_post_mods_def, expr_post_def]) >>
     fs[locals_kept_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ (s0,G0,tn0) _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ (t,G1,tn1) [] _`
    (drule_then assume_tac) >>
  `return_buf_sep d cenv mid t` by
    (`!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t` by
       (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
          qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
            qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
              mp_tac (MATCH_MP return_buf_allocas_path
                (LIST_CONJ [path,frame,sep]))))) >>
        simp[]) >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> simp[] >>
     qexistsl_tac [`H0`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >> simp[]) >>
  `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK (jump_to entry.cs_current_bb t),G1,tn1)` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_append) >>
     simp[] >> disch_then drule >> simp[]) >>
  `!fn inst u. frag_reachable ctx func (jump_to entry.cs_current_bb t) fn inst u ==>
                 dalloca_fmp_headroom inst u` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks
       (OK (jump_to entry.cs_current_bb t),G1,tn1)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
         (fn no_phi =>
         qpat_assum `!fn inst u. frag_reachable ctx func s0 fn inst u ==> _`
           (fn safe =>
             ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
               (LIST_CONJ [path,no_phi,safe])))))) >>
  `ret_pc_ok cenv entry t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `return_buf_frame d cenv entry t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at entry x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `alloca_history func (jump_to entry.cs_current_bb t)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `t` >> simp[]) >>
  `(allocas_below_fmp (jump_to entry.cs_current_bb t) <=> allocas_below_fmp t)` by
    simp[allocas_below_fmp_def, jump_to_def] >>
  simp[return_buf_sep_jump, ret_pc_ok_jump_to, return_buf_frame_jump_to,
       block_is_terminated_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!fn inst u. frag_reachable _ _ (jump_to _ _) _ _ _ ==> _` drule >> simp[]) >>
  conj_tac >- suspend "linked_frame" >> simp[jump_to_def]
QED

Resume assert_payload_false_action_mods[linked_frame]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       expr_post_mods H _ _ _ _ e es sa cond s0 mid (BoolV F) op t /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o
    REWRITE_RULE [expr_post_mods_def, expr_post_def]) >>
  conj_tac >- simp[stmt_state_rel_jump_to] >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >>
      goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
      qexists_tac `entry` >> simp[jump_to_def, lookup_var_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at entry x` by
    (rpt strip_tac >>
     qpat_assum `ret_pc_ok cenv entry t`
       (drule_then (CONJUNCTS_THEN assume_tac) o REWRITE_RULE [ret_pc_ok_def]) >>
     first_assum ACCEPT_TAC) >>
  irule ghost_inv_at_mods_exterior_frame >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `entry` >> simp[jump_to_def, lookup_var_def]
QED

Resume assert_payload_false_action_mods[non_normal]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!tail. eval_stmt _ _ _ = _` (qspec_then `[]` assume_tac) >>
  qpat_assum `!ee res ee'. eval_stmt _ _ ee = _ ==> _` (drule_then strip_assume_tac) >>
  fs[stmt_lands_def]
QED

Finalise assert_payload_false_action_mods
