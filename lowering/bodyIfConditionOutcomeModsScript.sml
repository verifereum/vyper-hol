(* The forced condition of a linked If, at the actual paired code slices. *)
Theory bodyIfConditionOutcomeMods
Ancestors
  bodyFullPostsMods bodyFullIfExpReach gasOutcomeFullPostMods gasOutcomeFullMods
  augAssignFullRhsSaved stmtSimIfProps stmtSimDefs exprSimDefs loweringPosts
  fragGasOriginPtr bodyPtrDefs compileEnv gasShadow gasContext
  exprLowering codegenRel fragExec venomExecSemantics venomInst
  vyperStorageFootprint vyperInterpreter vyperState

(* Only the normal endpoint is strengthened, using the very path that
   produced that endpoint. The bad-storage and exempt cases are unchanged. *)
Theorem condition_post_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!marks H res ee G' tn' t.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK t,G',tn') /\ Q H res ee G' tn' t ==>
    Q' H res ee G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >>
          qexists_tac `marks` >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem forced_condition_bool[local]:
  gas_admissible (eval_stmt cx (If e yes no)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  ?b. v = BoolV b
Proof
  strip_tac >> spose_not_then assume_tac >>
  `v <> BoolV T /\ v <> BoolV F` by metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >>
  disch_then (qspecl_then [`xs`,
    `INR (Error (TypeError "not BoolV"))`, `mid with gas_obs := []`] mp_tac) >>
  simp[stmt_res_ok_def] >>
  first_x_assum (qspec_then `[]` assume_tac) >> fs[] >>
  rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[bind_def] >> simp[raise_def]
QED

Theorem if_condition_outcome_mods:
  expr_type e = BaseT BoolT /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) e es /\
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op,cond) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
    (gas_shadow_expr e) shadow_sa = (op,scond) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state cond scond /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa cond func /\ fn_has_code shadow_sa scond shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\
  gas_admissible (eval_stmt cx (If e yes no)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid G tn t. ?b. res = INL (BoolV b) /\
      expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t /\
      expr_store_bound cx (post_value_type cenv e) (BoolV b) op t /\
      t.vs_current_bb = cond.cs_current_bb /\
      t.vs_inst_idx = LENGTH cond.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
      ptr_val_ok cx (post_value_type cenv e) (BoolV b) op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) t) /\
      mid.gas_obs = [] /\ ~t.vs_halted /\
      (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s))
    (\H res ee gt r. ?exc. res = INR exc /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR exc) gt r) /\
      halt_exit H cx ee (INR exc : unit + exception) r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  drule_then assume_tac if_condition_admissible >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_mods_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`cond`,`shadow_sa`,`scond`,`op`,
    `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  drule_all_then assume_tac gas_outcome_full_mods_return_buf_allocas >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. ?v. _) _`
    kall_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ condQ condR` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. condQ H res ee G tn t /\
    (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s)`,
    `condR`] >>
  rpt conj_tac
  >- (simp[Abbr `condQ`] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
      drule_all forced_condition_bool >> strip_tac >> gvs[] >>
      first_assum ACCEPT_TAC)
  >- (simp[Abbr `condR`] >> rpt gen_tac >> strip_tac >>
      Cases_on `res` >> gvs[] >>
      drule_all augassign_expr_exit_to_stmt_exit >> disch_then irule) >>
  irule condition_post_path >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ condQ condR` (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]
QED
