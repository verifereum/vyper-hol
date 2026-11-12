(* Raw expression/source boundary for reason-bearing reverts. *)
Theory reasonRaiseContinuationPtr
Ancestors bodyPtrDefs stmtSimProps stmtSimDefs exprSimDefs loweringPosts
  exprSimMemorySource exprSimUnwrapProps exprSimUnwrap stmtSimReason
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  stmtSimIfProps gasOutcome gasSummary gasSummaryCompose gasSummaryComposePtr
  gasContext gasExemptCert gasCount fragGasPath fragGasPathPtr fragGasSeqPtr fragGasMode
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv vyperInterpreter vyperState vyperValue vyperExprNoControl
  vyperStatePreservation venomExecSemantics venomInst venomState
Libs monadsyntax

Theorem compile_reason_message_expr:
  (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) ==>
  compile_reason_message cenv r = compile_expr cenv (expr_type r) r
Proof
  rpt strip_tac >> Cases_on `r` >> simp[compile_reason_message_def] >>
  rename1 `Literal t l` >> Cases_on `l` >> simp[compile_reason_message_def] >>
  Cases_on `t` >> gvs[compile_reason_message_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[compile_reason_message_def]
QED

Theorem compile_raise_reason_parts[local]:
  (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
  stmt_env cenv lctx ty (Raise (RaiseReason r)) sa = (cenv', sb) ==>
  cenv' = cenv /\
  ?vv sm. compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv (expr_type r)
      (type_memory_bytes cenv (expr_type r)) sm = ((), sb)
Proof
  strip_tac >> drule compile_reason_message_expr >> strip_tac >>
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

Theorem eval_raise_reason_bind:
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

Theorem eval_raise_reason_cases:
  eval_stmt cx (Raise (RaiseReason r)) es = (res, es') /\
  stmt_res_ok lctx res ==>
  ?r1. (do raw <- eval_expr cx r; read_result cx raw od) es = (r1, es') /\
    expr_res_ok r1 /\
    ((?str. r1 = INL (StringV str) /\ res = INR (AssertException str)) \/
     (?ex. r1 = INR ex /\ res = INR ex))
Proof
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

Theorem raise_reason_raw_admissible:
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

Theorem raise_reason_raw_exempt:
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

Theorem reason_vv_read_success:
  vv_holds cenv cx ty tv vv ee t ==>
  ?v. read_result cx tv ee = (INL v, ee)
Proof
  Cases_on `vv` >> simp[vv_holds_def] >> rpt strip_tac
  >- metis_tac[] >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]
QED

Theorem raise_reason_raw_string:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx r
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL tv, ee with gas_obs := tail)) /\
  vv_post ctx func cenv cx r es sa sm s0 (ee with gas_obs := []) tv vv t ==>
  ?str. read_result cx tv (ee with gas_obs := []) =
      (INL (StringV str), ee with gas_obs := []) /\
    !tail. (do v <- read_result cx tv;
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
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` assume_tac) >> fs[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ []` mp_tac) >>
  simp[eval_raise_reason_bind, bind_def] >>
  Cases_on `v` >>
  simp[dest_StringV_def, lift_option_type_def, raise_def, return_def,
       stmt_res_ok_def] >>
  strip_tac >> rename1 `StringV str` >> qexists_tac `str` >>
  simp[bind_def, dest_StringV_def, lift_option_type_def, raise_def, return_def]
QED

Theorem compile_raise_reason_path_frag_ptr:
 (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
 expr_vv_sim_ptr d ctx PG func cenv cx (expr_type r) r es /\
 (!sa vv sm sb s0 ee tv t G tn str.
   compile_expr cenv (expr_type r) r sa = (vv,sm) /\
   compile_revert_with_reason cenv vv (expr_type r) (type_memory_bytes cenv (expr_type r)) sm = ((),sb) /\
   fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
   ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ fn_inst_ids_distinct func /\
   vv_post ctx func cenv cx r es sa sm s0 ee tv vv t /\
   ghost_inv d cenv cx ee G tn t /\ ptr_vv_ok cx (post_value_type cenv r) tv vv ee G tn t /\
   read_result cx tv ee = (INL (StringV str),ee) /\
   (?gin gout. eval_expr cx r (es with gas_obs := gin) =
     (INL tv, ee with gas_obs := gout)) /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
   ?Gf tnf u. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf (Abort Revert_abort u)) ==>
 stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
   (stmt_env cenv lctx ty (Raise (RaiseReason r)))
   (eval_stmt cx (Raise (RaiseReason r))) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_raise_reason_parts >> strip_tac >> gvs[] >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  drule raise_reason_raw_admissible >> strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`, `G0`, `tn0`] mp_tac) >> simp[] >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res es_end G tn r. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  qpat_x_assum `?err ee leaf finish. _` strip_assume_tac >>
  drule raise_reason_raw_exempt >> metis_tac[]
QED

Resume compile_raise_reason_path_frag_ptr[normal]:
  markerLib.RESUME_TAC >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  drule_all raise_reason_raw_string >> strip_tac >>
  `?gin gout. eval_expr cx r (es with gas_obs := gin) =
     (INL tv, (es_end with gas_obs := []) with gas_obs := gout)` by
    (qexistsl_tac [`gas_explicit marks s0.vs_gas_readings ++ []`, `[]`] >>
     simp[]) >>
  qpat_x_assum `!sa' vv' sm' sb' s0' ee tv t G tn str. _`
    (drule_all_then strip_assume_tac o SRULE [PULL_EXISTS]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR (AssertException str)`, `es_end`, `Gf`, `tnf`,
                `Abort Revert_abort u`] >>
  conj_tac
  >- (gen_tac >> rewrite_tac[eval_raise_reason_bind] >> simp[Once bind_def]) >>
  conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def]
QED

Resume compile_raise_reason_path_frag_ptr[exception]:
  markerLib.RESUME_TAC >>
  Cases_on `res` >- fs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r''`] >>
  conj_tac
  >- (gen_tac >> rewrite_tac[eval_raise_reason_bind] >> simp[Once bind_def]) >>
  conj_tac >- simp[] >>
  disj2_tac >> simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type]
QED

Finalise compile_raise_reason_path_frag_ptr
