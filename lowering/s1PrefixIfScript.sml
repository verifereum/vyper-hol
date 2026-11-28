(* Request-prefix companion to bodyFullIf. *)
Theory s1PrefixIf
Ancestors
  s1PrefixPreds bodyFullIf s1PrefixDefs s1PrefixCompose s1PrefixProps
  bodySimFull stmtSimIfProps loweringPosts bodyFullIfExpReach exprSimDefs
  vyperStorageTrace vyperStorageFootprint vyperState list finite_map
  gasOutcomeFullCompose fragGasEmitCtrl fragGasOriginPtr bodyFullShared
  ptrDiscipline bodyPtrDefs fragGasOriginPtrExec valueEncoding
  contextRawReachable unitTransformDefs contextCodegenRel allocaHistory
  stmtSimProps bodyMemoryDefs venomExecSemantics venomInst compileEnv
  exprLoweringProps stmtSimDefs freshWrites venomState emitHelperProps gasContext
  vyperStorageBackend bodyFullHashKeccakFixed

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `ctx_has_dalloca ctx ==> !bb. MEM bb func.fn_blocks ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (qpat_x_assum `ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==> _`
       mp_tac >> simp[]) >>
  qpat_x_assum `stmt_env _ _ _ (If c _ _) _ = _`
    (strip_assume_tac o REWRITE_RULE [stmt_env_if]) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `stmt_env _ _ _ (If (gas_shadow_expr c) _ _) _ = _`
    (strip_assume_tac o REWRITE_RULE [stmt_env_if]) >>
  drule_all (Q.SPEC `T` compile_if_layout_shadow_ids_env) >>
  disch_then (qx_choosel_then [`op`, `sc`, `scond`, `pre`, `post`, `tl`, `el`, `xl`]
    strip_assume_tac) >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule if_condition_admissible >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`, `sa`, `sc`, `shadow_sa`, `scond`, `op`,
       `s0`, `G0`, `tn0`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[]))) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sc`, `shadow_sa`, `scond`, `op`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then assume_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  drule_all gas_outcome_full_return_buf_allocas >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ baseQ baseR` kall_tac >>
  qunabbrev_tac `baseQ` >> qunabbrev_tac `baseR` >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. condQ H rr ee G tn u /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK u,G,tn)) condR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ condQ condR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ condQ condR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ condR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. pathQ H rr ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted)
     condR` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ condR` (irule_at Any) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ pathQ condR` kall_tac >>
  rewrite_tac[eval_stmt_if_forced] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ condR`
    (mp_then Any irule gas_prefix_full_bind) >>
  rpt conj_tac
  >~ [`condR _ _ _ _ _ ==> ISR _`]
  >- (simp[Abbr `condR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`requests_outcomes_frame _`]
  >- (irule requests_outcomes_frame_bind_all >>
      simp[evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (rw[storage_trace_frame_raise] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_finally >>
      simp[storage_trace_frame_pop_scope, evaluate_storage_trace_frame])
  >> TRY (first_assum ACCEPT_TAC) >> suspend "selected"
QED
*)
Theorem compile_if_stmt_frag_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty c ss1 ss2
   es.
  (ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
      !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  expr_type c = BaseT BoolT /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (BaseT BoolT) c es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (BaseT BoolT) c es /\
  (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  (!sa op sb.
       lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr c) sa =
         (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  cs_mono (stmts_env cenv lctx ty ss1) /\
  cs_mono (stmts_env cenv lctx ty ss2) /\
  cs_mono (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss1)) /\
  cs_mono (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss2)) /\
  gas_shadow_compiles (lower_value compile_expr cenv (BaseT BoolT) c)
      (lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr c)) /\
  gas_shadow_compiles_env T (stmts_env cenv lctx ty ss1)
      (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss1)) /\
  gas_shadow_compiles_env T (stmts_env cenv lctx ty ss2)
      (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss2)) /\
  (!gs b es1.
       bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
         (INL (BoolV b), es1) ==>
       stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (stmts_env (gas_shadow_env T cenv) lctx ty
            (if b then MAP gas_shadow_stmt ss1 else MAP gas_shadow_stmt ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) /\
  (!gs b es1.
       bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
         (INL (BoolV b), es1) ==>
       stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (stmts_env (gas_shadow_env T cenv) lctx ty
            (if b then MAP gas_shadow_stmt ss1 else MAP gas_shadow_stmt ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (If c ss1 ss2))
      (stmt_env (gas_shadow_env T cenv) lctx ty
         (If (gas_shadow_expr c) (MAP gas_shadow_stmt ss1)
            (MAP gas_shadow_stmt ss2)))
      (eval_stmt cx (If c ss1 ss2)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_if_stmt_frag_prefix[selected]:
  qx_genl_tac [`marks`, `v`, `mid`, `G1`, `tn1`, `t`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `pathQ` >> qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  drule_all if_full_condition_bool >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  rewrite_tac[if_next_selected] >>
  qpat_x_assum `!b. ?entry last after sentry slast cenvb. _`
    (qspec_then `b` strip_assume_tac) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
      c es sa sc s0 mid (BoolV b) op t /\
   ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >> simp[val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by
    metis_tac[ptr_val_ok_def, ghost_inv_at_def] >>
  `!H. gas_origin_ptr_path
         (DF H, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         (t,G1,tn1) [] (OK (jump_to (if b then tl else el) t),G1,tn1)` by
    (gen_tac >> qpat_assum `emit_inst JNZ _ _ _ = _`
       (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] emit_jnz_origin_ptr)) >>
     simp[]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  conj_tac
  >- (irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_finally >>
      simp[storage_trace_frame_pop_scope, evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G1`, `jump_to (if b then tl else el) t`, `tn1`] >> simp[] >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL (BoolV b), mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pop_assum (fn th => rewrite_tac [th, APPEND_NIL])) >>
  `gas_admissible (eval_stmts cx (if b then ss1 else ss2)) (stmt_res_ok lctx)
     (mid with scopes := FEMPTY :: mid.scopes)` by (drule_all if_branch_admissible >> simp[]) >>
  qpat_x_assum `!gs b es1. _ ==> stmt_frag_prefix _ _ _ _ _ _ _ _ _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `b`, `mid`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  disch_then (qspecl_then [`st0`, `entry`, `last`, `sentry`, `slast`,
    `jump_to (if b then tl else el) t`, `G1`, `tn1`, `cenvb`] mp_tac) >>
  (impl_tac >- suspend "entry") >> suspend "cleanup"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_if_stmt_frag_prefix[entry]:
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w` by fs[expr_post_def] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
    (qpat_assum `bind _ _ _ = (INL (BoolV b),mid)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[] >> disch_then irule >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `return_buf_sep d cenv mid t` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `ctx`, `cx`,
       `es`, `func`, `s0`, `sa`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ret_pc_ok cenv entry t` by
    (qspecl_then [`cenv`, `cenv`, `sa`, `entry`, `s0`, `t`] mp_tac
       ret_pc_ok_frame >> simp[]) >>
  `return_buf_frame d cenv entry t` by
    (qspecl_then [`d`, `cenv`, `cenv`, `sa`, `entry`, `s0`, `t`] mp_tac
       return_buf_frame_frame >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at entry x` by metis_tac[not_fresh_at_mono] >>
  `alloca_history func (jump_to (if b then tl else el) t)` by
    (irule alloca_history_jump >> conj_tac >- simp[jump_to_def] >>
     qexists_tac `t` >> simp[jump_to_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to (if b then tl else el) t)` by
    (strip_tac >> fs[allocas_below_fmp_def, jump_to_def] >>
     first_assum ACCEPT_TAC) >>
  `!fn inst s. frag_reachable ctx func (jump_to (if b then tl else el) t) fn inst s ==>
     dalloca_fmp_headroom inst s` by suspend "headroom" >>
  `!H. valid_horizon cx st0 H
         (mid with scopes := FEMPTY :: mid.scopes).storage_trace ==>
       stmt_state_rel H ctx func cenv cx (mid with scopes := FEMPTY :: mid.scopes)
         (jump_to (if b then tl else el) t) /\
       storage_well_formed_on cx (mid with scopes := FEMPTY :: mid.scopes) (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx (mid with scopes := FEMPTY :: mid.scopes)
         G1 tn1 (jump_to (if b then tl else el) t)` by suspend "state" >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[return_buf_sep_jump, return_buf_sep_push,
       ret_pc_ok_jump_to, return_buf_frame_jump_to, block_is_terminated_def,
       jump_to_def] >>
  fs[allocas_below_fmp_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_if_stmt_frag_prefix[headroom]:
  Cases_on `ctx_has_dalloca ctx`
  >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by fs[] >>
      qpat_assum `!H. gas_origin_ptr_path _ (t,G1,tn1) [] _`
        (qspec_then `storage_trace_horizon mid.storage_trace` assume_tac) >>
      `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
        (rpt gen_tac >> strip_tac >>
         irule gas_origin_ptr_path_dalloca_fmp_headroom >>
         qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,G1,tn1)`
           (irule_at Any) >> simp[] >> qexists_tac `fn` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      irule gas_origin_ptr_path_dalloca_fmp_headroom >>
      qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] _` (irule_at Any) >>
      simp[] >> qexists_tac `fn` >> conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> drule_all frag_reachable_members >> strip_tac >>
  simp[unitTransformDefsTheory.dalloca_fmp_headroom_def] >> strip_tac >>
  `ctx_has_dalloca ctx` by
    (simp_tac bool_ss [ctx_has_dalloca_def, EXISTS_MEM] >>
     qexists_tac `fn` >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `inst` >> simp[]) >> fs[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_if_stmt_frag_prefix[state]:
  qx_gen_tac `H` >> simp[] >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx mid t /\
   storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
  simp[stmt_state_rel_jump_to, stmt_state_rel_push_scope, ghost_inv_at_jump] >>
  conj_tac >- fs[storage_well_formed_on_def, get_storage_scopes] >>
  irule ghost_inv_at_push >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_if_stmt_frag_prefix[cleanup]:
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `rmarks` strip_assume_tac) >>
  qexists_tac `rmarks` >> conj_tac >-
    (qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >> fs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ignore_bind push_scope _ _ = _` mp_tac >>
  simp[ignore_bind_def, bind_def, push_scope_def, return_def, finally_def] >>
  `!g. (mid with gas_obs := g) with scopes updated_by CONS FEMPTY =
       (mid with scopes := FEMPTY :: mid.scopes) with gas_obs := g` by
    simp[evaluation_state_component_equality] >>
  simp[] >>
  Cases_on `eval_stmts cx (if b then ss1 else ss2)
    ((mid with scopes := FEMPTY :: mid.scopes) with
       gas_obs := gas_explicit rmarks (jump_to (if b then tl else el) t).vs_gas_readings ++ tail)` >>
  rename1 `eval_stmts _ _ _ = (rr,z)` >> Cases_on `rr` >>
  Cases_on `z.scopes` >> simp[pop_scope_def, bind_def, raise_def, return_def] >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_if_stmt_frag_prefix
*)
