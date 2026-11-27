(* Select a payload assertion's continuation on the one reached Bool read. *)
Theory bodyAssertPayloadBindMods
Ancestors
  bodyAssertLandingMods bodyFullPostsMods bodyFullShadowBodyInv bodyFullShared
  bodyFullAssertReasonControl bodyFullAssertReasonSource reasonSourceProps
  bodyFullCustomErrorLayout bodyFullCustomErrorSource
  gasOutcomeFullBindPathMods gasOutcomeFullPostMods gasExemptCertMods
  gasShadow gasShadowState stmtSimAssertProps stmtSimDefs
  compileEnv exprLoweringProps exprSimDefs stmtSimProps loweringPosts bodyPtrDefs fragExec
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  fragGasEmitCtrl fragGasOriginPtrLoop stmtSimIfProps emitHelperProps valueEncoding
  venomExecSemantics venomInst venomState bodyMemoryDefs ptrDiscipline

(* Both payload compilers have the same control cuts. The Raise compiler
   remains opaque: the false continuation receives its actual boundaries. *)
Theorem assert_payload_layout[local]:
  ((?r. ak = AssertReason r /\ rr = RaiseReason r) \/
   (?err. ak = AssertCustomError err /\ rr = RaiseCustomError err)) /\
  stmt_env cenv lctx ty (Assert e ak) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Assert e ak))
    shadow_sa = (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?op s1 ok fl s3 s4 entry last t1 sentry slast.
    ce = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
      (gas_shadow_expr e) shadow_sa = (op,t1) /\
    gas_shadow_state s1 t1 /\ fn_has_code sa s1 func /\
    fn_has_code shadow_sa t1 shadow_func /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    fn_has_code s3 s4 func /\
    s3.cs_current_bb = s1.cs_current_bb /\ s3.cs_current_insts = s1.cs_current_insts /\
    stmt_env cenv lctx ty (Raise rr) entry = (cenv,last) /\
    stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Raise rr)) sentry =
      (gas_shadow_env T cenv,slast) /\
    fn_has_code entry last func /\ fn_has_code sentry slast shadow_func /\
    gas_shadow_state entry sentry /\ gas_shadow_state last slast /\
    entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
    sentry.cs_current_bb = fl /\ sentry.cs_current_insts = [] /\
    sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
    sa.cs_next_var <= entry.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  qpat_x_assum `(?r. _) \/ (?err. _)` strip_assume_tac >>
  gvs[] >> simp[gas_shadow_stmt_def, gas_shadow_assert_reason_def,
               gas_shadow_raise_reason_def] >> disch_tac
  >- (drule_all compile_assert_reason_layout_full >> strip_tac >>
      qexistsl_tac [`op`,`s1`,`s3`,`s4`,`entry`,`last`,`t1`,`sentry`,`slast`] >> simp[]) >>
  drule_all (SPEC T compile_assert_custom_layout_full) >> strip_tac >>
  qexistsl_tac [`op`,`s1`,`s3`,`s4`,`entry`,`last`,`t1`,`sentry`,`slast`] >> simp[]
QED

Theorem assert_payload_source[local]:
  ((?r. ak = AssertReason r /\ rr = RaiseReason r) \/
   (?err. ak = AssertCustomError err /\ rr = RaiseCustomError err)) /\
  gas_admissible (eval_stmt cx (Assert e ak)) (stmt_res_ok lctx) es ==>
  eval_stmt cx (Assert e ak) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then eval_stmt cx (Raise rr)
           else raise (Error (TypeError "not BoolV"))) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  (!xs v mid. (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := xs ++ tail) = (INL v,mid with gas_obs := tail)) ==>
     ?b. v = BoolV b) /\
  (!xs mid. (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := xs ++ tail) = (INL (BoolV F),mid with gas_obs := tail)) ==>
     gas_admissible (eval_stmt cx (Raise rr)) (stmt_res_ok lctx) (mid with gas_obs := []))
Proof
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac) >> gvs[]
  >- (simp[eval_assert_reason_bind] >> rpt conj_tac
      >- (irule assert_reason_expr_admissible >> goal_assum (drule_at Any))
      >- (rpt strip_tac >> drule_all assert_reason_condition_bool >> simp[]) >>
      rpt strip_tac >> drule_all assert_reason_raise_admissible >> simp[]) >>
  simp[eval_assert_custom_bind] >> rpt conj_tac
  >- (irule assert_custom_expr_admissible >> goal_assum (drule_at Any))
  >- (rpt strip_tac >> drule_all assert_custom_condition_bool >> simp[]) >>
  rpt strip_tac >> drule_all assert_custom_raise_admissible >> simp[]
QED

(* Notation for the outer statement post, textually matching stmt_frag_full_mods. *)
val assert_post =
  ``\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      immutable_frame_mods func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      return_buf_sep d cenv'' ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv'' ee t /\
      (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)``;

val assert_exit =
  ``\(H : (bool # 256 word # type_value) list # num list) res ee
      (gt : (string |-> num # num) # taint) r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)``;

Theorem compile_assert_payload_frag_full_from_false_action_mods:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e ak rr es.
    ((?r. ak = AssertReason r /\ rr = RaiseReason r) \/
     (?err. ak = AssertCustomError err /\ rr = RaiseCustomError err)) /\
    expr_type e = BaseT BoolT /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT BoolT) e es /\
    (!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 op s1 t1 entry last sentry slast
      marks mid G1 tn1 t.
      stmt_env cenv lctx ty (Assert e ak) sa = (cenv,sb) /\
      stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Assert e ak))
        shadow_sa = (gas_shadow_env T cenv,shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
      fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
      local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      ~block_is_terminated sa /\ gas_admissible (eval_stmt cx (Assert e ak)) (stmt_res_ok lctx) es /\
      return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
      alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
      lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
        (gas_shadow_expr e) shadow_sa = (op,t1) /\
      gas_shadow_state s1 t1 /\ fn_has_code sa s1 func /\ fn_has_code shadow_sa t1 shadow_func /\
      stmt_env cenv lctx ty (Raise rr) entry = (cenv,last) /\
      stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Raise rr)) sentry =
        (gas_shadow_env T cenv,slast) /\
      fn_has_code entry last func /\ fn_has_code sentry slast shadow_func /\
      gas_shadow_state entry sentry /\ gas_shadow_state last slast /\
      entry.cs_current_insts = [] /\ sentry.cs_current_insts = [] /\
      sa.cs_next_var <= entry.cs_next_var /\ mid.gas_obs = [] /\ ~t.vs_halted /\
      storage_trace_domain cx st0 mid.storage_trace /\
      gas_admissible (eval_stmt cx (Raise rr)) (stmt_res_ok lctx) mid /\
      (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL (BoolV F),mid with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
         expr_post_mods H ctx func cenv cx e es sa s1 s0 mid (BoolV F) op t /\
         expr_store_bound cx (post_value_type cenv e) (BoolV F) op t /\
         t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
         alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
         s0.vs_alloca_next <= t.vs_alloca_next /\
         ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
         ptr_val_ok cx (BaseT BoolT) (BoolV F) op G1 tn1 t /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
         (!bw capacity. d = SOME (bw, capacity) ==> allocas_from (w2n bw + capacity) t)) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (s0,G0,tn0) marks (OK t,G1,tn1)) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (t,G1,tn1) [] (OK (jump_to entry.cs_current_bb t),G1,tn1)) ==>
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cenv.ce_modules cx st0 (eval_stmt cx (Raise rr)) (mid,t,G1,tn1)
        ^assert_post ^assert_exit) ==>
    stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e ak))
      (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Assert e ak)))
      (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 op s1 t1 entry last sentry slast marks mid G1 tn1 t. _`
    (markerLib.mk_asm "false_action") >>
  pure_rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all assert_payload_layout >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  drule_all assert_payload_source >> strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_mods_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`t1`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all_then strip_assume_tac gas_outcome_full_mods_return_buf_allocas >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. ?v. _) _` kall_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ condQ condR` >>
  qpat_assum `eval_stmt _ _ = bind _ _` (PURE_REWRITE_TAC o single) >>
  irule gas_outcome_full_mods_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- rw[storage_trace_frame_raise, storage_trace_frame_return, evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn t. condQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`] >- suspend "selected" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `condR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  fs[stmt_exit_ptr_def, expr_exit_INR_type, halt_exit_def] >>
  Cases_on `r` >> gvs[expr_exit_def]
QED

Resume compile_assert_payload_frag_full_from_false_action_mods[selected]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qpat_assum `!xs v mid. _ ==> ?b. v = BoolV b` drule >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  `post_value_type cenv e = BaseT BoolT` by simp[post_value_type_word, is_word_type_def] >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_all if_condition_operand >> simp[val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by fs[ptr_val_ok_def, ghost_inv_at_mods_def] >>
  `!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) []
      (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) t),G1,tn1)` by
    (gen_tac >> irule emit_jnz_origin_ptr >> simp[] >>
     qexistsl_tac [`op`,`s3`,`s4`] >> simp[]) >>
  disj1_tac >> qexists_tac `BoolV b` >> Cases_on `b` >> simp[]
  >- suspend "true" >>
  suspend "false"
QED

Resume compile_assert_payload_frag_full_from_false_action_mods[true]:
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G1`,`mid`,`INL ()`,`jump_to sb.cs_current_bb t`,`tn1`] >>
  simp[return_def] >> qx_gen_tac `H` >> disch_tac >>
  conj_tac
  >- (qpat_assum `!H. gas_origin_ptr_path _ (t,G1,tn1) [] _`
        (qspec_then `H` mp_tac) >> fs[]) >>
  `mid with gas_obs := [] = mid` by fs[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = (res,st')`) mp_tac valid_horizon_frame)) >>
     simp[] >> disch_then irule >>
     conj_tac >- (irule storage_trace_frame_bind_all >>
       simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ((?v. _) /\ _) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11, EXISTS_REFL, UNWIND_THM2]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [expr_post_mods_def, expr_post_def, locals_kept_def]) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all assert_success_landing_mods >>
  qpat_assum `sb.cs_current_bb = _` (fn bb =>
    disch_then (qspec_then `lctx` (strip_assume_tac o SIMP_RULE (srw_ss()) [bb]))) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED

Resume compile_assert_payload_frag_full_from_false_action_mods[false]:
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `gas_admissible (eval_stmt cx (Raise rr)) (stmt_res_ok lctx) mid` by
    (qpat_assum `!xs mid. _ ==> gas_admissible _ _ _` drule >> simp[]) >>
  asm "false_action" irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `marks` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`entry`,`last`,`sentry`,`slast`] >> fs[]) >>
  qexistsl_tac [`shadow_sa`,`shadow_sb`,`t1`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ((?v. _) /\ _) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11, EXISTS_REFL, UNWIND_THM2]) >>
  fs[]
QED

Finalise compile_assert_payload_frag_full_from_false_action_mods
