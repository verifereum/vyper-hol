(* Counted memory-safe raise and assert with a reason that is not a string
   literal: the reason's fragment (expr_vv_sim_mem), whose exceptions exit,
   then the encoder, which a premise takes from the reason's post to its
   REVERT.  Each kind of compiled reason discharges that premise on its own. *)
Theory stmtReasonVvMemory
Ancestors
  stmtReasonLitAssertMemory stmtReasonLitFragMemory stmtReasonMemory
  stmtSimReasonExpr exprSimMemorySource exprSimUnwrapProps stmtSimDeclGas
  stmtLoweringMono
  exprSimMemDefs bodyMemoryDefs fragGasPathMem instMemFrontier
  stmtSimDefs stmtSimProps stmtSimIfProps stmtSimAssertProps exprSimDefs
  exprSimProps loweringPosts gasOutcome gasSummary gasSummaryCompose
  gasContext gasCount gasExemptCert fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue
  vyperEvalPreservesScopes vyperExprNoControl vyperValueOperation
  vyperStatePreservation venomExecSemantics venomExecProofs venomInst
  venomState integer_word vyperAST context allocaHistory
Libs
  monadsyntax intLib

(* ===== Compiler and gas boundaries ===== *)

Theorem revert_reason_grows:
  !cenv vv mt M sa sb.
    compile_revert_with_reason cenv vv mt M sa = ((), sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cenv`, `vv`, `mt`, `M`, `sa`] mp_tac
    (cj 4 ci_mono_stmt_helpers) >>
  asm_simp_tac (srw_ss()) [ci_mono_def]
QED

(* A source state's read of a reason's value succeeds, whatever form the
   lowering left it in. *)
Theorem vv_post_read_ok:
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv s ==>
  ?v. read_result cx tv ee = (INL v, ee)
Proof
  Cases_on `vv` >> simp[vv_post_def, vv_holds_def] >> strip_tac
  >- metis_tac[] >>
  Cases_on `p.ptr_location` >> gvs[storage_holds_def, immutable_holds_def] >>
  metis_tac[]
QED

(* A zero-read prefix to a counted outcome, in either gas mode. *)
Theorem gas_outcome_zero_prefix_any:
  gas_marked_path memory ctx func s0 0 (OK s1) /\
  gas_outcome memory tops (ctx,func) source (es,s1) Q R ==>
  gas_outcome memory tops (ctx,func) source (es,s0) Q R
Proof
  strip_tac >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_at_def, gas_marked_exec_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  `gas_marked_exec memory (ctx,func) (return ()) (es with gas_obs := [],s0) []
     (INL ()) (es with gas_obs := []) (OK s1)` by
    simp[gas_marked_exec_def, return_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` assume_tac >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. ignore_bind source (return ())`,
    `marks`, `err`, `ee`, `leaf`, `finish'`] mp_tac) >>
  simp_tac (srw_ss()) [bind_return] >>
  disch_then (fn th => first_assum (assume_tac o MATCH_MP th)) >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `es.gas_obs` mp_tac) >>
  `(es with gas_obs := es.gas_obs) = es` by
    simp[evaluation_state_component_equality] >>
  simp_tac (srw_ss()) [] >> asm_rewrite_tac[]
QED

(* A counted value action followed by a continuation whose every normal
   start has a counted outcome. *)
Theorem gas_outcome_bind_value:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0) Qa Ra /\
  (!marks res mid t.
     gas_marked_exec memory (ctx,func) a (es,s0) marks res mid (OK t) /\
     Qa res (mid with gas_obs := []) t ==>
     ?v. res = INL v /\
         gas_outcome memory tops (ctx,func) (k v) (mid with gas_obs := [], t)
           Q R) /\
  (!res ee r. exit_result r /\ Ra res ee r ==>
     ?ex. res = INR ex /\ R (INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ a _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- (rpt BasicProvers.VAR_EQ_TAC >>
          first_x_assum drule_all >> strip_tac >>
          rpt BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `gas_outcome _ _ _ (k _) _ _ _` mp_tac >>
          rewrite_tac[gas_outcome_def] >>
          disch_then (qx_choose_then `right` strip_assume_tac)
          >- (qexists_tac `left ++ right` >> disj1_tac >>
              qpat_x_assum `gas_summary_at _ _ _ (k _) _ _ _`
                (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
              rewrite_tac[gas_summary_at_def] >>
              rename1 `gas_marked_exec _ _ (k v) _ right rr fin rq` >>
              qexistsl_tac [`rr`, `fin`, `rq`] >>
              (conj_tac
               >- (irule gas_marked_exec_bind_normal >>
                   qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
               simp[])) >>
          qexists_tac `left ++ right` >> disj2_tac >>
          rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
          qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
          simp[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_bind_value >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[GSYM ignore_bind_def]) >>
      first_x_assum drule_all >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      qexists_tac `left` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      simp[]) >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

(* ===== Raise ===== *)

Theorem eval_raise_reason_eq:
  !cx se.
    eval_stmt cx (Raise (RaiseReason se)) =
    do tv <- eval_expr cx se; v <- read_result cx tv;
       s <- lift_option_type (dest_StringV v) "not StringV";
       raise (AssertException s) od
Proof
  simp[Once evaluate_def]
QED

Theorem raise_reason_expr_admissible:
  gas_admissible (eval_stmt cx (Raise (RaiseReason se))) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx se) expr_vv_res_ok es
Proof
  strip_tac >> irule forced_expr_admissible_raw >>
  pure_rewrite_tac[gas_admissible_def] >> rpt gen_tac >> disch_tac >>
  Cases_on `eval_stmt cx (Raise (RaiseReason se)) (es with gas_obs := gs)` >>
  drule_all gas_admissible_result >> strip_tac >>
  drule_all eval_raise_reason_cases >> strip_tac >>
  qpat_x_assum `_ = (r1, _)`
    (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  gvs[]
QED

Theorem raise_reason_exempt:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx se) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Raise (RaiseReason se))) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> rewrite_tac[eval_raise_reason_eq] >>
  pure_rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >>
  fs[ignore_bind_def]
QED

Theorem raise_reason_source:
  (!tail. eval_expr cx se (es with gas_obs := G ++ tail) =
          (INL tv, ee with gas_obs := tail)) /\
  read_result cx tv (ee with gas_obs := []) =
    (INL (StringV str), ee with gas_obs := []) ==>
  !tail. eval_stmt cx (Raise (RaiseReason se)) (es with gas_obs := G ++ tail) =
         (INR (AssertException str), ee with gas_obs := tail)
Proof
  rpt strip_tac >> drule read_result_gas_obs >>
  disch_then (qspec_then `tail` mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  rewrite_tac[eval_raise_reason_eq] >>
  asm_simp_tac (srw_ss()) [bind_def, lift_option_type_def, dest_StringV_def, return_def,
                           raise_def]
QED

Theorem raise_reason_read_string:
  gas_admissible (eval_stmt cx (Raise (RaiseReason se))) (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx se (es with gas_obs := G ++ tail) =
          (INL tv, ee with gas_obs := tail)) /\
  read_result cx tv (ee with gas_obs := []) = (INL v, ee with gas_obs := []) ==>
  ?str. v = StringV str
Proof
  rpt strip_tac >>
  Cases_on `eval_stmt cx (Raise (RaiseReason se)) (es with gas_obs := G)` >>
  drule_all gas_admissible_result >> strip_tac >>
  drule_all eval_raise_reason_cases >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >> fs[] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [bind_def] >> strip_tac >> gvs[]
QED

(* The reason's fragment, from any state at its start, then the encoder to
   its REVERT. *)
Theorem raise_reason_vv_outcome:
  !ctx func cx lctx RetQ cenv se es s sa vv sm sb Q.
    expr_vv_sim_mem ctx func cenv cx (expr_type se) se es /\
    (!es sa vv sm sb s0 ee tv t str.
       compile_expr cenv (expr_type se) se sa = (vv, sm) /\
       compile_revert_with_reason cenv vv (expr_type se)
         (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
       fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\
       vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
       vv_store_bound cx (expr_type se) (lowered_value_type cenv se) ee tv vv t /\
       read_result cx tv ee = (INL (StringV str), ee) /\
       ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
       ?u. gas_path_mem ctx func t 0 (Abort Revert_abort u)) /\
    compile_expr cenv (expr_type se) se sa = (vv, sm) /\
    compile_revert_with_reason cenv vv (expr_type se)
      (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_stmt cx (Raise (RaiseReason se))) (stmt_res_ok lctx) es /\
    stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx,func) (eval_stmt cx (Raise (RaiseReason se)))
      (es, s) Q (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[revert_reason_grows] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx se) expr_vv_res_ok es` by
    metis_tac[raise_reason_expr_admissible] >>
  qpat_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [gas_summary_at_def])
      >- suspend "normal" >>
      suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule raise_reason_exempt >> first_assum ACCEPT_TAC
QED

Resume raise_reason_vv_outcome[normal]:
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  qpat_x_assum `gas_marked_path _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) [gas_marked_path_def]) >>
  `~t.vs_halted` by metis_tac[gas_path_mem_exec, gas_path_normal] >>
  drule vv_post_read_ok >> strip_tac >>
  `?str. v = StringV str` by
    (irule raise_reason_read_string >> metis_tac[]) >>
  qpat_x_assum `v = StringV str` SUBST_ALL_TAC >>
  first_x_assum (qspecl_then [`es`, `sa`, `vv`, `sm`, `sb`, `s`,
    `es_end with gas_obs := []`, `tv`, `t`, `str`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `u` assume_tac) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (AssertException str)`, `es_end`, `Abort Revert_abort u`] >>
  conj_tac
  >- (rewrite_tac[gas_marked_exec_def] >> conj_tac
      >- (drule_all raise_reason_source >> disch_then ACCEPT_TAC) >>
      simp_tac (srw_ss()) [gas_marked_path_def] >>
      metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj2_tac >>
  simp_tac (srw_ss()) [exit_result_def, stmt_exit_def, expr_exit_def]
QED

Resume raise_reason_vv_outcome[exception]:
  rewrite_tac[gas_summary_at_def] >>
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
      gen_tac >> rewrite_tac[eval_raise_reason_eq] >>
      asm_simp_tac (srw_ss()) [bind_def]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Finalise raise_reason_vv_outcome

Theorem compile_raise_reason_vv_frag_mem:
  !d ctx func cx lctx RetQ cenv ty se es.
    (!ml str. se <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim_mem ctx func cenv cx (expr_type se) se es /\
    (!es sa vv sm sb s0 ee tv t str.
       compile_expr cenv (expr_type se) se sa = (vv, sm) /\
       compile_revert_with_reason cenv vv (expr_type se)
         (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
       fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\
       vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
       vv_store_bound cx (expr_type se) (lowered_value_type cenv se) ee tv vv t /\
       read_result cx tv ee = (INL (StringV str), ee) /\
       ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
       ?u. gas_path_mem ctx func t 0 (Abort Revert_abort u)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason se)))
      (eval_stmt cx (Raise (RaiseReason se))) es
Proof
  rpt gen_tac >> strip_tac >>
  `compile_reason_message cenv se = compile_expr cenv (expr_type se) se` by
    metis_tac[compile_reason_message_expr] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [stmt_env_def, declare_stmt_local_def,
    compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    LET_THM] >>
  Cases_on `compile_expr cenv (expr_type se) se sa` >>
  rename1 `compile_expr _ _ _ sa = (vv, sm)` >>
  asm_simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `compile_revert_with_reason cenv vv MT MS sm` >>
  Cases_on `compile_revert_with_reason cenv vv MT MS sm` >>
  rename1 `compile_revert_with_reason _ _ _ _ sm = (u, sc)` >> Cases_on `u` >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `sc = sb` SUBST_ALL_TAC >>
  qunabbrev_tac `MT` >> qunabbrev_tac `MS` >>
  qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `se`, `es`, `s0`,
               `sa`, `vv`, `sm`, `sb`] mp_tac raise_reason_vv_outcome >>
  disch_then (fn th => irule (SPEC_ALL th)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ===== Assert ===== *)

(* A false condition runs the reason as raise does. *)
Theorem eval_assert_reason_bind:
  !cx e se.
    eval_stmt cx (Assert e (AssertReason se)) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then eval_stmt cx (Raise (RaiseReason se))
           else raise (Error (TypeError "not BoolV")))
Proof
  rpt gen_tac >> rewrite_tac[eval_raise_reason_eq] >>
  simp_tac (srw_ss()) [FUN_EQ_THM] >> gen_tac >>
  simp_tac (srw_ss()) [Once evaluate_def] >>
  simp[eval_expr_switch_forced] >>
  simp[bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx v st` >>
  Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >> simp[bind_def]
QED

Theorem assert_reason_expr_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertReason se))) (stmt_res_ok lctx)
    es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def] >>
     Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[eval_assert_reason_bind, bind_def] >>
  fs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def] >>
  metis_tac[]
QED

Theorem assert_reason_raise_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertReason se))) (stmt_res_ok lctx)
    es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := G ++ tail) =
          (INL (BoolV F), mid with gas_obs := tail)) ==>
  gas_admissible (eval_stmt cx (Raise (RaiseReason se))) (stmt_res_ok lctx)
    (mid with gas_obs := [])
Proof
  rw[gas_admissible_def] >>
  first_x_assum (qspecl_then [`G ++ gs`, `res`, `ee`] irule) >>
  qexistsl_tac [`G`, `ee`, `gs`] >>
  rewrite_tac[eval_assert_reason_bind] >> pure_once_rewrite_tac[bind_def] >>
  asm_simp_tac (srw_ss()) []
QED

Theorem assert_ok_return_outcome[local]:
  gas_marked_path memory ctx func s 0 (OK t) /\
  Q (INL ()) (es with gas_obs := []) t ==>
  gas_outcome memory tops (ctx,func) (return ()) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es`, `OK t`] >>
  simp[gas_marked_exec_def, return_def]
QED

Theorem compile_assert_reason_parts:
  compile_reason_message cenv se = compile_expr cenv (expr_type se) se /\
  stmt_env cenv lctx ty (Assert e (AssertReason se)) sa = (cenv',sb) ==>
  ?op s1 ok s2 fl s3 s4 s5 vv sm s6.
    cenv' = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,s5) /\
    compile_expr cenv (expr_type se) se s5 = (vv,sm) /\
    compile_revert_with_reason cenv vv (expr_type se)
      (type_memory_bytes cenv (expr_type se)) sm = ((),s6) /\
    new_block ok s6 = (s6.cs_current_bb,sb)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [stmt_env_def, declare_stmt_local_def,
    compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    LET_THM] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op,s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok,s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl,s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u,s4)` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (x5,s5)` >> simp[] >>
  Cases_on `compile_expr cenv (expr_type se) se s5` >>
  rename1 `_ = (vv,sm)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_revert_with_reason cenv vv MT MS sm` >>
  Cases_on `compile_revert_with_reason cenv vv MT MS sm` >>
  rename1 `_ = (u6,s6)` >> simp[] >>
  Cases_on `new_block ok s6` >> rename1 `_ = (x7,s7)` >>
  simp[] >> strip_tac >>
  gvs[Abbr `MT`, Abbr `MS`] >>
  imp_res_tac new_block_props >> gvs[]
QED

(* The condition's fragment and its JNZ; the ok edge lands, the fail edge
   runs raise_reason_vv_outcome. *)
Theorem compile_assert_reason_vv_frag_mem:
  !d ctx func cx lctx RetQ cenv ty e se es.
    (!ml str. se <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) /\
    (!gs es1.
       (do raw <- eval_expr cx e; read_result cx raw od)
         (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
       expr_vv_sim_mem ctx func cenv cx (expr_type se) se es1) /\
    (!es sa vv sm sb s0 ee tv t str.
       compile_expr cenv (expr_type se) se sa = (vv, sm) /\
       compile_revert_with_reason cenv vv (expr_type se)
         (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
       fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\
       vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
       vv_store_bound cx (expr_type se) (lowered_value_type cenv se) ee tv vv t /\
       read_result cx tv ee = (INL (StringV str), ee) /\
       ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
       ?u. gas_path_mem ctx func t 0 (Abort Revert_abort u)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason se)))
      (eval_stmt cx (Assert e (AssertReason se))) es
Proof
  rpt gen_tac >> strip_tac >>
  `compile_reason_message cenv se = compile_expr cenv (expr_type se) se` by
    metis_tac[compile_reason_message_expr] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_assert_reason_parts >> strip_tac >> gvs[] >>
  `cs_extends sa s1` by metis_tac[] >>
  `cs_extends s5 sm /\ s5.cs_next_var <= sm.cs_next_var` by
    metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sm s6 /\ sm.cs_next_var <= s6.cs_next_var` by
    metis_tac[revert_reason_grows] >>
  `cs_extends s5 s6` by metis_tac[cs_extends_trans] >>
  drule_all assert_lit_compiler_code >> strip_tac >>
  `sa.cs_next_var <= s5.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
     imp_res_tac emit_inst_extends >> gvs[] >> decide_tac) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (imp_res_tac new_block_props >> gvs[] >> decide_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_reason_expr_admissible] >>
  qpat_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
  rewrite_tac[eval_assert_reason_bind] >>
  irule gas_outcome_bind_value >>
  first_assum (irule_at (Pos last)) >>
  conj_tac >- suspend "normal" >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_reason_vv_frag_mem[normal]:
  rpt gen_tac >> BETA_TAC >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  qpat_x_assum `gas_marked_path _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) [gas_marked_path_def]) >>
  `~t.vs_halted` by metis_tac[gas_path_mem_exec, gas_path_normal] >>
  `?b. v = BoolV b` by
    (spose_not_then assume_tac >>
     `v <> BoolV T /\ v <> BoolV F` by metis_tac[] >>
     qpat_x_assum `gas_admissible (eval_stmt _ _) _ _` mp_tac >>
     rewrite_tac[gas_admissible_def] >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,
       `INR (Error (TypeError "not BoolV"))`, `mid with gas_obs := []`] mp_tac) >>
     simp[stmt_res_ok_def] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[] >> rewrite_tac[eval_assert_reason_bind] >>
     pure_once_rewrite_tac[bind_def] >> asm_simp_tac (srw_ss()) [raise_def]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `gas_path_mem ctx func t 0
     (OK (jump_to (if b then sb.cs_current_bb else s5.cs_current_bb) t))` by
    (imp_res_tac emit_inst_extends >>
     irule assert_jnz_zero_path_mem >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!sa op sb. lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  Cases_on `b`
  >- suspend "true"
  >> suspend "false"
QED

Resume compile_assert_reason_vv_frag_mem[true]:
  gvs[] >>
  irule assert_ok_return_outcome >>
  qexists_tac `jump_to sb.cs_current_bb t` >>
  simp[gas_marked_path_def] >>
  drule_all assert_success_post_mem >> simp[]
QED

Resume compile_assert_reason_vv_frag_mem[false]:
  gvs[] >>
  irule gas_outcome_zero_prefix_any >>
  qexists_tac `jump_to s5.cs_current_bb t` >>
  conj_tac >- simp[gas_marked_path_def] >>
  `expr_vv_sim_mem ctx func cenv cx (expr_type se) se (mid with gas_obs := [])` by
    (qpat_x_assum `!gs es1. _` (qspecl_then
       [`gas_explicit marks s0.vs_gas_readings`, `mid with gas_obs := []`]
       mp_tac) >>
     impl_tac
     >- (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >>
         simp_tac (srw_ss()) [listTheory.APPEND_NIL]) >>
     disch_then ACCEPT_TAC) >>
  `gas_admissible (eval_stmt cx (Raise (RaiseReason se))) (stmt_res_ok lctx)
     (mid with gas_obs := [])` by
    (irule assert_reason_raise_admissible >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := [])
     (jump_to s5.cs_current_bb t)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     rewrite_tac[stmt_state_rel_jump_to] >> metis_tac[]) >>
  `alloca_history func (jump_to s5.cs_current_bb t)` by
    fs[allocaHistoryTheory.alloca_history_def, jump_to_def] >>
  `local_ptrs_reserved cenv s5` by metis_tac[local_ptrs_reserved_next_var] >>
  qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `se`,
               `mid with gas_obs := []`, `jump_to s5.cs_current_bb t`,
               `s5`, `vv`, `sm`, `s6`] mp_tac raise_reason_vv_outcome >>
  disch_then (fn th => irule (SPEC_ALL th)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[jump_to_def] >> NO_TAC) >>
  rpt strip_tac >> first_x_assum (drule_all_then ACCEPT_TAC)
QED

Finalise compile_assert_reason_vv_frag_mem
