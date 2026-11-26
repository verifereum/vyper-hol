(* The return suffix consumes the one reached forced-expression outcome. *)
Theory bodySelectedForcedReturnMods
Ancestors
  bodyFullPostsMods stmtSimReturn augAssignFullRhsSaved
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  bodyForcedStorageFrameMods vyperStorageTrace vyperStorageFootprint
  gasShadow loweringPosts exprSimDefs

Theorem selected_forced_return_bind[local]:
  let R = \H res ee gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==>
      !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u)
  in
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) ChildQ
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
    (!H res mid G tn t. ChildQ H res mid G tn t ==> ?v. res = INL v) /\
    return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
    (!marks v mid G tn t.
      (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
      ~t.vs_halted /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==> ChildQ H (INL v) mid G tn t) /\
      (!bw capacity. d = SOME (bw,capacity) ==>
        allocas_from (w2n bw + capacity) t) ==>
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
        (raise (ReturnException v)) (mid,t,G,tn) (\H res ee G' tn' u. F) R) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (eval_stmt cx (Return (SOME e))) (es,s0,G0,tn0) Q R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
    bind (bind (eval_expr cx e) (read_result cx)) (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  drule_all gas_outcome_full_mods_return_buf_allocas >> strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ ChildQ _` kall_tac >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) (read_result _))`]
  >- simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_raise] >>
  qexists `\H res mid G tn t. ChildQ H res mid G tn t /\
    (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t) /\
    mid.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
      conj_tac >- simp[] >>
      BETA_TAC >> rpt gen_tac >> Cases_on `res` >- simp[expr_exit_def] >>
      strip_tac >> rename1 `expr_exit (INR exc) r` >>
      qexists `exc` >> conj_tac >- simp[] >>
      drule_all augassign_expr_exit_to_stmt_exit >> disch_then irule) >>
  suspend "reached"
QED

Resume selected_forced_return_bind[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H res mid G tn t. ChildQ H res mid G tn t ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl [`\H res ee G' tn' u. F`,
    `\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
        !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u)`] >>
  simp[] >>
  first_x_assum irule >> simp[] >> qexists `marks` >> simp[]
QED

Finalise selected_forced_return_bind

Theorem selected_forced_return_frag_with_entry_mods:
  let cfg = (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) in
  let C = \sa sm s0 op G0 tn0 H v mid G tn t.
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v op t /\
    expr_store_bound cx (post_value_type cenv e) v op t /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
  in
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
    (!sa sb sha shb ce' s0.
      stmt_env cenv lctx ty (Return (SOME e)) sa = (ce',sb) /\
      stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Return (SOME e))) sha =
        (gas_shadow_env T ce',shb) /\
      gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
      fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
      ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 ==>
      ?op sm shm.
        lower_value compile_expr cenv ty e sa = (op,sm) /\
        lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shm) /\
        gas_shadow_state sm shm /\
        fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\ P sa sb sha shb op sm shm) /\
    (!st0 sa sb sha shb op sm shm s0 G0 tn0 marks v mid G tn t.
      P sa sb sha shb op sm shm /\ lower_value compile_expr cenv ty e sa = (op,sm) /\
      ctx_inst_ids_distinct ctx /\ MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
      (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
      (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
      ~t.vs_halted /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==> C sa sm s0 op G0 tn0 H v mid G tn t) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
      (!bw capacity. d = SOME (bw,capacity) ==>
        allocas_from (w2n bw + capacity) t) ==>
      gas_outcome_full_mods cfg cenv.ce_modules cx st0 (raise (ReturnException v))
        (mid,t,G,tn) (\H res ee G' tn' u. F)
        (\H res ee gt r.
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
          halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==>
            !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u))) ==>
    stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Return (SOME e)))
      (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
      (eval_stmt cx (Return (SOME e))) es
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  pure_rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!sa sb sha shb ce' s0. _ ==> ?op sm shm. _`
    (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_stmt_def]) >>
  disch_then (drule_all_then strip_assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule_then ACCEPT_TAC return_forced_admissible) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (drule_all_then strip_assume_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  irule (SIMP_RULE bool_ss [LET_THM] selected_forced_return_bind) >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
  simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      first_x_assum irule >>
      qpat_assum `P sa sb shadow_sa shadow_sb op sm shm` (irule_at Any) >>
      simp[] >> qexistsl [`tn0`,`s0`,`marks`,`G0`] >>
      asm_rewrite_tac[] >>
      conj_tac
      >- (gen_tac >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
            (drule_then strip_assume_tac) >> simp[]) >>
      gen_tac >> disch_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
           simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
         qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
         `valid_horizon cx st0 H (mid with gas_obs := []).storage_trace` by simp[] >>
         drule_all valid_horizon_frame >> simp[]) >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >> qexists `v` >> simp[]
QED

Theorem selected_forced_return_frag_mods:
  let cfg = (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) in
  let C = \sa sm s0 op G0 tn0 H v mid G tn t.
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v op t /\
    expr_store_bound cx (post_value_type cenv e) v op t /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
  in
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
    (!sa sb sha shb ce'.
      stmt_env cenv lctx ty (Return (SOME e)) sa = (ce',sb) /\
      stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Return (SOME e))) sha =
        (gas_shadow_env T ce',shb) /\
      gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
      fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
      ~block_is_terminated sa ==>
      ?op sm shm.
        lower_value compile_expr cenv ty e sa = (op,sm) /\
        lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shm) /\
        gas_shadow_state sm shm /\
        fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\ P sa sb sha shb op sm shm) /\
    (!st0 sa sb sha shb op sm shm s0 G0 tn0 marks v mid G tn t.
      P sa sb sha shb op sm shm /\ lower_value compile_expr cenv ty e sa = (op,sm) /\
      ctx_inst_ids_distinct ctx /\ MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
      (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
      (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
      ~t.vs_halted /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==> C sa sm s0 op G0 tn0 H v mid G tn t) /\
      (!bw capacity. d = SOME (bw,capacity) ==>
        allocas_from (w2n bw + capacity) t) ==>
      gas_outcome_full_mods cfg cenv.ce_modules cx st0 (raise (ReturnException v))
        (mid,t,G,tn) (\H res ee G' tn' u. F)
        (\H res ee gt r.
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
          halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==>
            !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u))) ==>
    stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Return (SOME e)))
      (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
      (eval_stmt cx (Return (SOME e))) es
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  irule (SIMP_RULE bool_ss [LET_THM] selected_forced_return_frag_with_entry_mods) >>
  asm_rewrite_tac[] >> qexists `P` >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!sa sb sha shb ce'. _ ==> ?op sm shm. _` drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  qpat_assum `P sa sb sha shb op sm shm` (irule_at Any) >>
  asm_rewrite_tac[] >> qexistsl [`tn0`,`s0`,`marks`,`G0`] >> asm_rewrite_tac[]
QED
