(*
 * Statement simulation: Raise and Assert with a reason that is not a
 * string literal (#637)
 *
 * The reason is lowered with compile_expr (compile_reason_message's
 * fallback) and its value_vv handed to the Error(string) encoder of
 * compile_revert_with_reason, whose unwrap_value emits no code when the
 * value is on the stack or a string in memory (reason_vv).  The encoder
 * runs to its REVERT from any state where that operand is defined
 * (stmtSimReason's certificate), so the reason's fragment ends either in
 * an exit of its own or at the encoder with the operand defined.
 *
 * TOP-LEVEL:
 *   reason_vv_ok                    — the reason's value_vv as the encoder needs
 *   compile_raise_reason_path_frag  — raise with a reason, given the
 *                                     encoder's counted path
 *   compile_raise_reason_frag       — raise with a reason
 *   compile_assert_reason_frag      — assert with a reason
 *
 * Helper: compile_reason_message_expr, reason_ds,
 *   reason_expr_revert_extends, eval_raise_reason_cases
 *)

Theory stmtSimReasonExpr
Ancestors
  exprSimUnwrapProps exprSimMemorySource
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  exprSimUnwrap loweringSlice
  stmtSimIfProps stmtSimReason gasOutcome gasSummary gasSummaryCompose
  gasContext gasExemptCert gasCount fragGasPath fragGasMode
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv
  vyperInterpreter vyperState vyperValue vyperExprNoControl
  vyperStatePreservation
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The reason's value ===== *)

(* A reason other than a string literal is lowered by compile_expr. *)
Theorem compile_reason_message_expr:
  !cenv r.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) ==>
    compile_reason_message cenv r = compile_expr cenv (expr_type r) r
Proof
  rpt strip_tac >> Cases_on `r` >> simp[compile_reason_message_def] >>
  rename1 `Literal t l` >> Cases_on `l` >> simp[compile_reason_message_def] >>
  Cases_on `t` >> gvs[compile_reason_message_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[compile_reason_message_def]
QED

(* The reason's value_vv hands the encoder an operand of its own that is not
   a label. *)
Definition reason_vv_ok_def:
  reason_vv_ok vv <=> ?op. reason_vv vv = SOME op /\ !l. op <> Label l
End

(* The variables the encoder needs defined for a message operand. *)
Definition reason_ds_def:
  reason_ds (Var x) = [x] /\
  reason_ds (Lit w) = [] /\
  reason_ds (Label l) = []
End

Theorem vv_holds_reason_vv[local]:
  !cenv cx t tv vv es s op.
    vv_holds cenv cx t tv vv es s /\ reason_vv vv = SOME op ==>
    ?w. eval_operand op s = SOME w
Proof
  Cases_on `vv` >> rw[vv_holds_def, reason_vv_def] >>
  gvs[expr_val_rel_def] >> metis_tac[]
QED

(* The reason's code and the encoder only append. *)
Theorem reason_expr_revert_extends_any[local]:
  !cenv r sa vv sm rty msz sb.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) ==>
    cs_extends sa sb
Proof
  rpt strip_tac >> drule compile_expr_extends >> strip_tac >>
  drule compile_revert_reason_split_certificate >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

Theorem reason_expr_revert_extends:
  !cenv r sa vv sm rty msz sb.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_vv_ok vv ==>
    cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >> gvs[reason_vv_ok_def] >>
  drule compile_expr_extends >> strip_tac >>
  `reason_operand (reason_ds op) op` by
    (Cases_on `op` >> gvs[reason_ds_def, reason_operand_def]) >>
  drule_all compile_revert_reason_certificate >> strip_tac >>
  `cs_extends sm sb` by
    (simp[cs_extends_def] >> qexists `[]` >>
     gvs[same_blocks_def] >>
     metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC]) >>
  metis_tac[cs_extends_trans]
QED

(* ===== The source ===== *)

(* Raise inspects the forced result, not the captured expression result:
   a value or PlaceR may read as a string, and either evaluation or the
   read may fail.  Type errors remain outside stmt_frag's outcomes. *)
Theorem eval_raise_reason_cases:
  !cx r es res es' lctx.
    eval_stmt cx (Raise (RaiseReason r)) es = (res, es') /\
    stmt_res_ok lctx res ==>
    ?r1. (do raw <- eval_expr cx r; read_result cx raw od) es = (r1, es') /\
         expr_res_ok r1 /\
         ((?str. r1 = INL (StringV str) /\
                 res = INR (AssertException str)) \/
          (?ex. r1 = INR ex /\ res = INR ex))
Proof
  rpt gen_tac >>
  `eval_stmt cx (Raise (RaiseReason r)) es =
   bind (do raw <- eval_expr cx r; read_result cx raw od)
     (\v. do str <- lift_option_type (dest_StringV v) "not StringV";
             raise (AssertException str) od) es` by
    (simp[Once evaluate_def, bind_def] >>
     Cases_on `eval_expr cx r es` >> rename1 `_ = (raw, est)` >>
     Cases_on `raw` >> simp[] >>
     rename1 `read_result cx captured est` >>
     Cases_on `read_result cx captured est` >>
     rename1 `_ = (forced, esf)` >> Cases_on `forced` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `(do raw <- eval_expr cx r; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >> simp[bind_def] >>
  Cases_on `r1` >> simp[]
  >- (rename1 `dest_StringV v` >> Cases_on `v` >>
      simp[dest_StringV_def, lift_option_type_def, raise_def, return_def,
           stmt_res_ok_def] >> rw[expr_res_ok_def]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
  simp[bind_def] >> Cases_on `eval_expr cx r es` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem expr_res_ok_revert[local]:
  !ex t. expr_res_ok (INR ex : value + exception) ==>
         expr_exit (INR ex : unit + exception) (Abort Revert_abort t)
Proof
  rw[expr_res_ok_def] >> simp[expr_exit_def]
QED

(* The exits of a raise with a reason, as the reason's outcome gives them. *)
Theorem raise_reason_exits:
  !r1 res RetQ es'.
    expr_res_ok r1 /\
    ((?str. r1 = INL (StringV str) /\
            res = INR (AssertException str)) \/
     (?ex. r1 = INR ex /\ res = INR ex)) ==>
    (!rr. expr_exit r1 rr ==> stmt_exit RetQ es' res rr) /\
    (!t. stmt_exit RetQ es' res (Abort Revert_abort t))
Proof
  rpt gen_tac >> strip_tac >> gvs[stmt_exit_def, expr_exit_def] >>
  `expr_res_ok (INR ex : value + exception)` by simp[] >>
  simp[expr_res_ok_revert] >> rpt strip_tac >> disj1_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
                      expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

Theorem compile_raise_reason_parts[local]:
  !cenv lctx ty r sa cenv' sb.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    stmt_env cenv lctx ty (Raise (RaiseReason r)) sa = (cenv', sb) ==>
    cenv' = cenv /\
    ?vv sm. compile_expr cenv (expr_type r) r sa = (vv, sm) /\
      compile_revert_with_reason cenv vv (expr_type r)
        (type_memory_bytes cenv (expr_type r)) sm = ((), sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_reason_message_expr >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type r) r sa` >>
  rename1 `_ = (vv, sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv vv (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm` >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raise_reason_compiler_code[local]:
  !cenv r sa vv sm sb func.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv (expr_type r)
      (type_memory_bytes cenv (expr_type r)) sm = ((), sb) /\
    fn_has_code sa sb func ==>
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  rpt strip_tac >> drule compile_expr_extends >> strip_tac >>
  drule compile_revert_reason_split_certificate >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem eval_raise_reason_bind[local]:
  eval_stmt cx (Raise (RaiseReason r)) =
  bind (eval_expr cx r)
    (\tv. do v <- read_result cx tv;
             str <- lift_option_type (dest_StringV v) "not StringV";
             raise (AssertException str) od)
Proof
  simp[FUN_EQ_THM, Once evaluate_def, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx r x` >> rename1 `_ = (raw, ee)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem raise_reason_raw_admissible[local]:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx r) expr_vv_res_ok es
Proof
  strip_tac >> irule forced_expr_admissible_raw >>
  simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `eval_stmt cx (Raise (RaiseReason r)) (es with gas_obs := gs)` >>
  rename1 `_ = (res, esf)` >> simp[] >> strip_tac >>
  drule_all eval_raise_reason_cases >> strip_tac >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >> gvs[]
QED

Theorem raise_reason_raw_exempt[local]:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx r) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Raise (RaiseReason r))) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx (Raise (RaiseReason r))) (return ()) =
   bind (eval_expr cx r)
     (\tv. ignore_bind
       (do v <- read_result cx tv;
           str <- lift_option_type (dest_StringV v) "not StringV";
           (raise (AssertException str) : evaluation_state -> unit evaluation_result)
        od) (return ()))` by
    (rewrite_tac[eval_raise_reason_bind] >>
     simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx r x` >>
     qmatch_asmsub_rename_tac `eval_expr cx r x = (captured, est)` >>
     Cases_on `captured` >> simp[bind_def]) >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem reason_vv_read_success[local]:
  vv_holds cenv cx ty tv vv ee t ==>
  ?v. read_result cx tv ee = (INL v, ee)
Proof
  Cases_on `vv` >> simp[vv_holds_def] >> rpt strip_tac
  >- metis_tac[] >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]
QED

Theorem raise_reason_continuation[local]:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es /\
  gas_marked_exec F (ctx,func) (eval_expr cx r)
    (es,s0) marks (INL tv) ee (OK t) /\
  vv_post ctx func cenv cx r es sa sm s0 (ee with gas_obs := []) tv vv t ==>
  ?str. !tail.
    (do v <- read_result cx tv;
        msg <- lift_option_type (dest_StringV v) "not StringV";
        raise (AssertException msg) od)
      (ee with gas_obs := tail) =
    (INR (AssertException str) : unit + exception, ee with gas_obs := tail)
Proof
  rpt strip_tac >>
  `?v. read_result cx tv (ee with gas_obs := []) =
       (INL v, ee with gas_obs := [])` by
    (irule reason_vv_read_success >> gvs[vv_post_def] >> metis_tac[]) >>
  drule read_result_gas_obs >> simp[] >> strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  fs[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ []` mp_tac) >>
  simp[eval_raise_reason_bind, bind_def] >>
  Cases_on `v` >>
  simp[dest_StringV_def, lift_option_type_def, raise_def, return_def,
       stmt_res_ok_def] >>
  strip_tac >> rename1 `StringV str` >> qexists_tac `str` >>
  simp[bind_def, dest_StringV_def,
    lift_option_type_def, raise_def, return_def]
QED

Theorem raise_reason_counted_success[local]:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es /\
  gas_marked_exec F (ctx,func) (eval_expr cx r)
    (es,s0) marks (INL tv) ee (OK t) /\
  vv_post ctx func cenv cx r es sa sm s0 (ee with gas_obs := []) tv vv t /\
  gas_path ctx func t 0 (Abort Revert_abort u) ==>
  ?str. gas_marked_exec F (ctx,func) (eval_stmt cx (Raise (RaiseReason r)))
    (es,s0) marks (INR (AssertException str)) ee (Abort Revert_abort u) /\
    !tail. stmt_exit RetQ (ee with gas_obs := tail)
      (INR (AssertException str)) (Abort Revert_abort u)
Proof
  rpt strip_tac >> drule_all raise_reason_continuation >> strip_tac >>
  qexists_tac `str` >> conj_tac
  >- (rewrite_tac[eval_raise_reason_bind] >>
      once_rewrite_tac[GSYM APPEND_NIL] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`ee`, `t`, `tv`] >> simp[] >>
      simp[gas_marked_exec_def, gas_marked_path_def]) >>
  simp[stmt_exit_def, expr_exit_def]
QED

Theorem raise_reason_counted_exception[local]:
  gas_marked_exec F (ctx,func) (eval_expr cx r)
    (es,s0) marks (INR ex) ee rr /\
  expr_exit (INR ex : eval_result + exception) rr ==>
  gas_marked_exec F (ctx,func) (eval_stmt cx (Raise (RaiseReason r)))
    (es,s0) marks (INR ex) ee rr /\
  !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr
Proof
  strip_tac >> conj_tac
  >- (rewrite_tac[eval_raise_reason_bind] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[stmt_exit_def] >> gen_tac >> disj1_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:eval_result``] expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

(* ===== raise ===== *)

(* raise r, for a reason r that is not a string literal: r's counted
   judgment, then the Error(string) encoder and its REVERT, which reads no
   gas.  The encoder's path is a premise over r's success post, so each
   form of r's value (on the stack or in memory, in storage, in code)
   supplies its own. *)
Theorem compile_raise_reason_path_frag:
  !ctx func cx lctx RetQ cenv ty r es.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sm sb s0 ee tv t.
       compile_expr cenv (expr_type r) r sa = (vv, sm) /\
       compile_revert_with_reason cenv vv (expr_type r)
         (type_memory_bytes cenv (expr_type r)) sm = ((), sb) /\
       fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
       vv_post ctx func cenv cx r es sa sm s0 ee tv vv t /\ ~t.vs_halted /\
       t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
       ?u. gas_path ctx func t 0 (Abort Revert_abort u)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_raise_reason_parts >> strip_tac >> gvs[] >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  drule raise_reason_raw_admissible >> strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res ee rr. _` strip_assume_tac >> gvs[]
      >- (`~t.vs_halted` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def, gas_marked_path_def] >>
             metis_tac[gas_path_normal]) >>
          first_x_assum (drule_all_then strip_assume_tac) >>
          drule_all raise_reason_counted_success >>
          disch_then (qspec_then `RetQ` strip_assume_tac) >>
          qexists_tac `marks` >> disj1_tac >>
          qexistsl_tac [`INR (AssertException str)`, `es_end`,
                       `Abort Revert_abort u`] >> simp[exit_result_def]) >>
      Cases_on `res` >> gvs[] >>
      drule_all raise_reason_counted_exception >>
      disch_then (qspec_then `RetQ` strip_assume_tac) >>
      qexists_tac `marks` >> disj1_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qpat_x_assum `?err ee leaf finish. _` strip_assume_tac >>
  drule raise_reason_raw_exempt >> metis_tac[]
QED

(* The encoder's path for a value on the stack or a string in memory. *)
Theorem reason_vv_revert_path[local]:
  !ctx func cenv cx r es sa vv sm sb s0 ee tv t.
    reason_vv_ok vv /\
    compile_revert_with_reason cenv vv (expr_type r)
      (type_memory_bytes cenv (expr_type r)) sm = ((), sb) /\
    fn_has_code sm sb func /\
    vv_post ctx func cenv cx r es sa sm s0 ee tv vv t /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func t 0 (Abort Revert_abort u)
Proof
  rpt strip_tac >> gvs[reason_vv_ok_def, vv_post_def] >>
  drule_all vv_holds_reason_vv >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `vv`, `op`, `expr_type r`,
               `type_memory_bytes cenv (expr_type r)`, `sm`, `sb`,
               `reason_ds op`, `t`] mp_tac compile_revert_reason_path >>
  impl_tac
  >- (Cases_on `op` >>
      gvs[reason_ds_def, reason_operand_def, reason_known_def,
          eval_operand_def]) >>
  simp[]
QED

(* raise r, for a reason r that is not a string literal and whose value
   compile_expr hands out on the stack or in memory. *)
Theorem compile_raise_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r)))
      (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  rpt strip_tac >> irule compile_raise_reason_path_frag >> simp[] >>
  rpt strip_tac >> irule reason_vv_revert_path >> metis_tac[]
QED

(* ===== assert ===== *)

(* A false condition runs the reason as raise does, from the state after
   the condition. *)
Theorem eval_assert_reason_false:
  !cx e r es es1.
    (do raw <- eval_expr cx e; read_result cx raw od) es =
      (INL (BoolV F), es1) ==>
    eval_stmt cx (Assert e (AssertReason r)) es =
    eval_stmt cx (Raise (RaiseReason r)) es1
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC [evaluate_def] >>
  simp[eval_expr_switch_forced]
QED

(* assert e, r for a reason r as compile_raise_reason_frag has it: its
   fail block is that raise, judged where the condition reads false. *)
Theorem compile_assert_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1. (do raw <- eval_expr cx e; read_result cx raw od)
                (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
              expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  rpt strip_tac >> irule compile_assert_reason_frag_general >> simp[] >>
  rpt strip_tac >> irule compile_raise_reason_frag >> simp[] >>
  metis_tac[]
QED

val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "REASON_EXPR_FORCE_AUDIT OK\n"
     else (fn (_:string) => print "closure gate skipped
") "reason expression inherited admission"
  end) [compile_reason_message_expr, reason_expr_revert_extends,
        eval_raise_reason_cases, compile_raise_reason_path_frag,
        compile_raise_reason_frag, compile_assert_reason_frag];
