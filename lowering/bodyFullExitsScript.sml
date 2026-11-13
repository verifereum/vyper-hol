(*
 * The exits of the full body induction (bodySimFullMain) that compile to
 * no operand of their own, over the finite-horizon joint judgment: break,
 * continue, bare and unreachable raise, and the unreachable assertion.
 * Each target path is one zero-GAS jump, abort, or the condition's joint
 * path followed by them; the target endpoint is fixed before the horizon,
 * and the posts are read at every horizon valid for the final trace.
 *
 * TOP-LEVEL:
 *   compile_raise_abort_path, compile_assert_cond_path
 *     -- the exit fragments' target paths
 *   compile_loop_jump_frag_full -- break and continue
 *   compile_raise_frag_full     -- bare and unreachable raise
 *   compile_assert_frag_full    -- bare and unreachable assertion
 *)
Theory bodyFullExits
Ancestors
  bodyFullShared bodyFullPreds bodySimFull gasOutcomeFullCompose
  gasOutcomeFull fragGasEmitCtrl fragGasOriginPtr fragGasOrigin
  gasShadowState gasShadow bodyPtrDefs bodyMemoryDefs
  stmtSimAssertProps stmtSimIfProps stmtSimProps stmtSimDefs exprSimDefs
  loweringPosts gasExemptCert fragGasPathPtr fragExec ptrDiscipline gasContext
  emitHelper emitHelperProps exprLoweringProps stmtLowering exprLowering
  compileEnv allocaHistory vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState vyperValue venomExecSemantics venomInst
  venomState list
Libs
  monadsyntax

val _ = Parse.hide "body";

(* ===== The exit fragments' target paths ===== *)

(* A raise with no reason runs its one abort instruction. *)
Theorem compile_raise_abort_path:
  (rk = RaiseBare \/ rk = RaiseUnreachable) /\
  stmt_env cenv lctx ty (Raise rk) sa = (cenv', sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
        (Abort (if rk = RaiseBare then Revert_abort else ExHalt_abort) t,
         G, tn)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  fs[markerTheory.Abbrev_def] >>
  `?t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s =
       Abort (if opc = REVERT then Revert_abort else ExHalt_abort) t` by
    (gvs[] >> metis_tac[step_revert_zero, step_invalid]) >>
  gvs[] >> qexists_tac `t` >>
  irule emit_abort_origin_ptr >> simp[] >> metis_tac[])
QED

(* After an assertion's condition, its JNZ jumps to the continuation block
   on true and reaches the abort on false. *)
Theorem compile_assert_cond_path:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  stmt_env cenv lctx ty (Assert e ak) sa = (cenv', sb) /\
  fn_has_code sa sb func /\
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op, s1) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo t /\
  eval_operand op t = SOME (if b then 1w else 0w) /\ op_taint tn op = {} /\
  t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t.vs_halted ==>
  (b ==> gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (t, G, tn) []
           (OK (jump_to sb.cs_current_bb t), G, tn)) /\
  (~b ==> ?u. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
                (t, G, tn) []
                (Abort (if ak = AssertBare then Revert_abort else ExHalt_abort)
                   u, G, tn))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  qpat_x_assum `stmt_env _ _ _ _ _ = _`
    (mp_then Any mp_tac compile_assert_parts) >> simp[] >> strip_tac >>
  gvs[] >>
  `cs_extends sa s1` by metis_tac[compile_expr_grows] >>
  qpat_assum `cs_extends sa s1`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (t, G, tn) []
     (OK (jump_to (if b then sb.cs_current_bb else s5.cs_current_bb) t),
      G, tn)` by
    (irule emit_jnz_origin_ptr >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  conj_tac >- (strip_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `emit_inst opc ops [] s5` >>
  `?u. step_inst_base (mk_inst s5.cs_next_id opc ops [])
         (jump_to s5.cs_current_bb t) =
       Abort (if opc = REVERT then Revert_abort else ExHalt_abort) u` by
    (simp[Abbr `opc`, Abbr `ops`] >>
     metis_tac[step_revert_zero, step_invalid]) >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
     (jump_to s5.cs_current_bb t, G, tn) []
     (Abort (if opc = REVERT then Revert_abort else ExHalt_abort) u, G, tn)` by
    (irule emit_abort_origin_ptr >>
     simp[jump_to_def, Abbr `opc`, Abbr `ops`] >>
     fs[allocas_from_def, jump_to_def] >> metis_tac[]) >>
  qexists_tac `u` >> fs[Abbr `opc`] >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL])
QED

(* ===== Break and continue ===== *)

Theorem compile_loop_jump_frag_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty st es.
    (st = Break \/ st = Continue) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty st) (stmt_env cenv lctx ty st)
      (eval_stmt cx st) es
Proof
  rpt gen_tac >> disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lctx`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `es.gas_obs` mp_tac) >>
      simp[Once evaluate_def, raise_def, stmt_res_ok_def]) >>
  rename1 `InLoop ex inc` >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx st` >>
  qabbrev_tac `lbl = if st = Break then ex else inc` >>
  qabbrev_tac `exc = if st = Break then BreakException
                     else ContinueException` >>
  `eval_stmt cx st = raise exc` by
    (gvs[Abbr `exc`, Abbr `st`] >> simp[FUN_EQ_THM, Once evaluate_def]) >>
  `cenv' = cenv /\ emit_inst JMP [Label lbl] [] sa = ((), sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
     gvs[Abbr `lbl`, Abbr `st`] >>
     simp[stmt_env_def, declare_stmt_local_def, comp_ignore_bind_def,
          comp_bind_def, compile_stmt_def, comp_return_def] >>
     pairarg_tac >> simp[]) >>
  drule emit_inst_extends >> strip_tac >>
  `return_buf_frame d cenv sb s0` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[]) >>
  `alloca_history func (jump_to lbl s0)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> metis_tac[]) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INR exc`, `jump_to lbl s0`, `tn0`] >>
  simp[raise_def] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s0` by fs[ghost_inv_at_def] >>
  conj_tac >- (irule emit_jmp_origin_ptr >> simp[] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) (jump_to lbl s0)`
    by (simp[stmt_state_rel_jump_to] >> drule msg_gas_state_frame >>
        disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
          mp_tac) >>
        simp[NoAsms]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (`(es with gas_obs := []).accounts = es.accounts /\
      (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
     metis_tac[storage_well_formed_on_backends]) >>
  qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, ghost_inv_at_jump_to,
       return_buf_frame_jump_to] >>
  gvs[Abbr `lbl`, Abbr `exc`, Abbr `st`, jump_to_def, lookup_var_def])
QED

(* ===== Raise with no reason ===== *)

Theorem compile_raise_frag_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise rk)) (stmt_env cenv lctx ty (Raise rk))
      (eval_stmt cx (Raise rk)) es
Proof
  rpt gen_tac >> disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  fs[markerTheory.Abbrev_def] >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx (Raise rk)` >>
  `?msg. !st. eval_stmt cx (Raise rk) st = (INR (AssertException msg), st) /\
              (opc = INVALID ==> msg = "UNREACHABLE")` by
    simp[Abbr `rk`, Once evaluate_def, raise_def] >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s0 = Abort a t /\
         expr_exit (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (gvs[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid]) >>
  irule gas_outcome_full_exit >>
  qexistsl_tac [`G0`, `es`, `Abort a t`, `INR (AssertException msg)`, `tn0`] >>
  simp[exit_result_def] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s0` by fs[ghost_inv_at_def] >>
  conj_tac >- (irule emit_abort_origin_ptr >> simp[] >> metis_tac[]) >>
  gvs[stmt_exit_ptr_def])
QED

(* ===== Assertion with no reason ===== *)

(* The assertion's suffix after the condition compiles alike on both sides,
   so the shadow condition ends at the same operand and a shadow state. *)
Theorem assert_shadow_prefix[local]:
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (s4.cs_current_bb,s5) /\
  emit_inst opc ops [] s5 = ((),s6) /\
  new_block ok s6 = (s6.cs_current_bb,sb) /\
  fresh_label "assert_ok" t1 = (ok',t2) /\
  fresh_label "assert_fail" t2 = (fl',t3) /\
  emit_inst JNZ [op'; Label ok'; Label fl'] [] t3 = ((),t4) /\
  new_block fl' t4 = (t4.cs_current_bb,t5) /\
  emit_inst opc ops [] t5 = ((),t6) /\
  new_block ok' t6 = (t6.cs_current_bb,tb) /\
  gas_shadow_state sb tb ==>
  op' = op /\ gas_shadow_state s1 t1
Proof
  simp[fresh_label_def, emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
       new_block_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  fs[gas_shadow_state_def, gas_shadow_block_def] >>
  fs[gas_shadow_inst_def, mk_inst_def]
QED

(* An admissible assertion's condition that ends normally is a boolean. *)
Theorem assert_full_condition_bool[local]:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  gas_admissible (eval_stmt cx (Assert e ak)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  ?b. v = BoolV b
Proof
  strip_tac >>
  Cases_on `eval_stmt cx (Assert e ak) (es with gas_obs := xs)` >>
  drule_all gas_admissible_result >> strip_tac >>
  drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
  disch_then (qspec_then `lctx` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
  gvs[bind_def]
QED

Theorem compile_assert_frag_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (BaseT BoolT) e es ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e ak))
      (stmt_env cenv lctx ty (Assert (gas_shadow_expr e) ak))
      (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Assert e _) _ = _`
    (mp_then Any mp_tac compile_assert_parts) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Assert (gas_shadow_expr e) _) _ = _`
    (mp_then Any mp_tac compile_assert_parts) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`op'`, `t1`, `ok'`, `t2`, `fl'`, `t3`, `t4`,
    `t5`, `t6`] strip_assume_tac) >>
  drule_all assert_shadow_prefix >> strip_tac >>
  qpat_x_assum `op' = op` SUBST_ALL_TAC >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `cs_extends sa s1 /\ cs_extends shadow_sa t1` by
    metis_tac[compile_expr_grows] >>
  qpat_assum `cs_extends sa s1`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_assum `cs_extends shadow_sa t1`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  (* the condition, on the assertion's own input block *)
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `t1`, `op`, `s0`,
    `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  `eval_stmt cx (Assert e ak) =
     bind (bind (eval_expr cx e) (read_result cx))
       (\v. if v = BoolV T then return ()
            else if v = BoolV F then
              raise (AssertException
                (if ak = AssertBare then "" else "UNREACHABLE"))
            else raise (Error (TypeError "not BoolV")))` by
    (irule eval_assert_bind >> first_assum ACCEPT_TAC) >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> RULE_ASSUM_TAC BETA_RULE >>
      BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- rw[storage_trace_frame_raise, storage_trace_frame_return] >>
  qexists_tac `\H res ee G' tn' t. condQ H res ee G' tn' t /\ ~t.vs_halted /\
                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `condR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_frag_full[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  (* the condition's H-free facts, at the trace's own horizon *)
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  drule_all assert_full_condition_bool >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  qexists_tac `BoolV b` >> conj_tac >- simp[] >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  `op_taint tn1 op = {} /\ allocas_from lo t` by
    metis_tac[ptr_val_ok_def, ghost_inv_at_def] >>
  (* the JNZ to the continuation or the failure block *)
  `!D. gas_origin_ptr_path
         (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         (t, G1, tn1) [] (OK (jump_to (if b then ok else fl) t), G1, tn1)` by
    (gen_tac >>
     qpat_assum `emit_inst JNZ [op; _; _] _ s3 = _`
       (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            emit_jnz_origin_ptr)) >>
     fs[]) >>
  Cases_on `b` >> BETA_TAC >> simp[]
  >- suspend "true" >>
  suspend "false"
QED

Resume compile_assert_frag_full[true]:
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G1`, `mid`, `INL ()`, `jump_to ok t`, `tn1`] >>
  simp[return_def] >> qx_gen_tac `H` >> strip_tac >>
  conj_tac >- (first_x_assum (qspec_then `DF H` mp_tac) >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
     imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
     imp_res_tac emit_inst_extends >> gvs[] >> decide_tac) >>
  `v = BoolV T` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac assert_success_post_mem) >> simp[] >>
  disch_then (qspecl_then [`sb`, `lctx`, `d`] mp_tac) >> simp[] >>
  strip_tac >> gvs[ghost_inv_at_jump, ghost_kept_at_def]
QED

Resume compile_assert_frag_full[false]:
  qabbrev_tac `opc = if ak = AssertBare then REVERT else INVALID` >>
  qabbrev_tac `ops = if ak = AssertBare then [Lit 0w; Lit 0w] else []` >>
  qabbrev_tac `msg = if ak = AssertBare then "" else "UNREACHABLE"` >>
  `?a u. step_inst_base (mk_inst s5.cs_next_id opc ops [])
           (jump_to fl t) = Abort a u /\
         expr_exit (INR (AssertException msg) : unit + exception)
           (Abort a u)` by
    (qpat_x_assum `ak = _ \/ _` strip_assume_tac >>
     simp[Abbr `opc`, Abbr `ops`, Abbr `msg`, expr_exit_def] >>
     metis_tac[step_revert_zero, step_invalid]) >>
  `!D. gas_origin_ptr_path
         (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         (t, G1, tn1) [] (Abort a u, G1, tn1)` by
    (gen_tac >>
     `gas_origin_ptr_path
        (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (jump_to fl t, G1, tn1) [] (Abort a u, G1, tn1)` by
       (qpat_assum `emit_inst opc ops [] s5 = _`
          (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                               emit_abort_origin_ptr)) >>
        qpat_x_assum `ak = _ \/ _` strip_assume_tac >>
        gvs[Abbr `opc`, Abbr `ops`, allocas_from_def, jump_to_def] >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `D` mp_tac) >>
     simp[] >> strip_tac >>
     drule gas_origin_ptr_path_append >> simp[] >>
     disch_then drule >> simp[]) >>
  irule gas_outcome_full_exit >>
  qexistsl_tac [`G1`, `mid`, `Abort a u`, `INR (AssertException msg)`,
    `tn1`] >>
  simp[raise_def, exit_result_def, stmt_exit_ptr_def]
QED

Finalise compile_assert_frag_full
