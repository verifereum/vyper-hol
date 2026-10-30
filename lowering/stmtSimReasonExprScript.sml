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
 *   reason_vv_ok                — the reason's value_vv as the encoder needs
 *   compile_raise_reason_frag   — raise with a reason
 *   compile_assert_reason_frag  — assert with a reason
 *
 * Helper: compile_reason_message_expr, reason_ds,
 *   reason_expr_revert_extends, reason_expr_revert_frag,
 *   eval_raise_reason_cases
 *)

Theory stmtSimReasonExpr
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim exprSimUnwrap loweringSlice
  stmtSim stmtSimIf stmtSimReason
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

(* The forced reason may fail either while evaluating or while reading a
   captured place.  compile_expr's judgment remains at the raw boundary;
   its successful postcondition supplies the encoder's defined operand.
   A failed read is still covered by the statement's revert exit. *)
Theorem reason_expr_revert_frag_general:
  !ctx func cenv cx r es res1 es1 sa vv sm sb s0 R P.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    cs_extends sm sb /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    eval_expr cx r es = (res1, es1) /\ expr_vv_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\
    (!tv s. vv_holds cenv cx (expr_type r) tv vv es1 s ==> P s) /\
    frag_exec ctx sm sb P (\s. F) R ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. F) R
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `res1`, `es1`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> qexistsl_tac [`P`, `sm`] >> simp[] >>
  irule frag_exec_conseq >>
  qpat_x_assum `frag_exec ctx sa sm _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[vv_post_def]
QED

(* The reason's fragment, then the encoder and its REVERT: preserve the
   reason's own expr_exit (including HaltException).  Only a value reaches
   the encoder, so only that outcome needs to admit its REVERT. *)
Theorem reason_expr_revert_frag:
  !ctx func cenv cx r es res1 es1 sa vv sm rty msz sb s0 R.
    compile_expr cenv (expr_type r) r sa = (vv, sm) /\
    compile_revert_with_reason cenv vv rty msz sm = ((), sb) /\
    reason_vv_ok vv /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (do raw <- eval_expr cx r; read_result cx raw od) es = (res1, es1) /\
    expr_res_ok res1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!rr. expr_exit res1 rr ==> R rr) /\
    (!tv t. res1 = INL tv ==> R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. F) R
Proof
  rpt gen_tac >> strip_tac >> gvs[reason_vv_ok_def] >>
  drule compile_expr_extends >> strip_tac >>
  `reason_operand (reason_ds op) op` by
    (Cases_on `op` >> gvs[reason_ds_def, reason_operand_def]) >>
  qspecl_then [`ctx`, `cenv`, `vv`, `op`, `rty`, `msz`, `sm`, `sb`,
               `reason_ds op`, `\rr. T`] mp_tac compile_revert_reason_frag >>
  impl_tac >- simp[] >> disch_then (assume_tac o cj 2) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  Cases_on `eval_expr cx r es` >> rename1 `_ = (raw, est)` >>
  `est = es1` by
    (qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[read_result_state]) >> gvs[] >>
  `expr_vv_res_ok raw` by
    (qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `raw` >> simp[] >> strip_tac >>
     gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
     rename1 `read_result cx captured es1` >> Cases_on `captured` >>
     gvs[expr_vv_res_ok_def, read_result_def, raise_def, expr_res_ok_def]) >>
  `!rr. expr_exit raw rr ==> R rr` by
    (rpt strip_tac >> Cases_on `raw` >> gvs[] >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> strip_tac >> gvs[] >>
     metis_tac[expr_exit_exception_transport]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `raw`, `es1`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  `!tv s. raw = INL tv /\
          vv_post func cenv cx r es sa sm s0 es1 tv vv s ==>
          ?v. res1 = INL v` by
    (rpt strip_tac >> gvs[vv_post_def] >>
     Cases_on `vv` >> gvs[reason_vv_def, vv_holds_def] >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> metis_tac[]) >>
  reverse (Cases_on `?tv. res1 = INL tv`)
  >- (irule frag_exec_exit_prefix >> qexists_tac `sm` >> simp[] >>
      irule frag_exec_conseq >>
      qpat_x_assum `frag_exec ctx sa sm _ _ _` (irule_at Any) >>
      simp[] >> metis_tac[]) >>
  qspecl_then [`ctx`, `cenv`, `vv`, `op`, `rty`, `msz`, `sm`, `sb`,
               `reason_ds op`, `R`] mp_tac compile_revert_reason_frag >>
  impl_tac >- metis_tac[] >> strip_tac >>
  irule frag_exec_seq >> qexistsl [`reason_known (reason_ds op)`, `sm`] >>
  simp[] >>
  irule frag_exec_conseq >>
  qpat_x_assum `frag_exec ctx sa sm _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[vv_post_def] >>
  drule_all vv_holds_reason_vv >> strip_tac >>
  Cases_on `op` >> gvs[reason_known_def, reason_ds_def, eval_operand_def]
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

(* An exception propagates its own exit unchanged; only a returned string
   becomes an assertion and admits the encoder's REVERT. *)
Theorem raise_reason_exits:
  !r1 res RetQ es'.
    expr_res_ok r1 /\
    ((?str. r1 = INL (StringV str) /\
            res = INR (AssertException str)) \/
     (?ex. r1 = INR ex /\ res = INR ex)) ==>
    (!rr. expr_exit r1 rr ==> stmt_exit RetQ es' res rr) /\
    (!tv t. r1 = INL tv ==> stmt_exit RetQ es' res (Abort Revert_abort t))
Proof
  rpt gen_tac >> strip_tac >> gvs[stmt_exit_def, expr_exit_def] >>
  rpt strip_tac >> disj1_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
                      expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

(* ===== raise ===== *)

(* raise r, for a reason r that is not a string literal and whose value
   compile_expr hands out on the stack or in memory: r's fragment, whose
   errors exit, then the Error(string) encoder and its REVERT. *)
Theorem compile_raise_reason_frag:
  !ctx func cx lctx RetQ cenv ty r es res es'.
    eval_stmt cx (Raise (RaiseReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_vv_sim ctx func cenv cx (expr_type r) r es /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise (RaiseReason r))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  `compile_reason_message cenv r = compile_expr cenv (expr_type r) r` by
    metis_tac[compile_reason_message_expr] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qpat_assum `compile_reason_message _ _ = _` (fn th => rewrite_tac[th]) >>
  Cases_on `compile_expr cenv (expr_type r) r sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >>
  Cases_on `compile_revert_with_reason cenv vv (expr_type r)
              (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `_ = (u, sf)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code sa sfin func` >>
  drule_all eval_raise_reason_cases >> disch_then (qx_choose_then `r1` assume_tac) >>
  qspecl_then [`r1`, `res`, `RetQ`, `es'`] mp_tac raise_reason_exits >>
  impl_tac >- fs[] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `r`, `es`, `r1`, `es'`, `sa`,
               `vv`, `sm`, `expr_type r`,
               `type_memory_bytes cenv (expr_type r)`, `sfin`, `s0`,
               `stmt_exit RetQ es' res`] mp_tac reason_expr_revert_frag >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `s0`] mp_tac) >> simp[]
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

(* assert e, r for a reason r as compile_raise_reason_frag has it: the
   condition and a JNZ to the ok block, where the code ends, and a fail
   block with r's fragment, the encoder and its REVERT.  r's judgment is
   at the source state after a false condition. *)
Theorem compile_assert_reason_frag:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    eval_stmt cx (Assert e (AssertReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
             (INL (BoolV F), es1) ==>
           expr_vv_sim ctx func cenv cx (expr_type r) r es1) /\
    (!sa vv sb. compile_expr cenv (expr_type r) r sa = (vv, sb) ==>
                reason_vv_ok vv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >>
  `compile_reason_message cenv r = compile_expr cenv (expr_type r) r` by
    metis_tac[compile_reason_message_expr] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qpat_assum `compile_reason_message _ _ = _` (fn th => rewrite_tac[th]) >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op, s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok, s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl, s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u4, s4)` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (x5, s5)` >> simp[] >>
  Cases_on `compile_expr cenv (expr_type r) r s5` >>
  rename1 `compile_expr _ _ _ s5 = (vv, sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv vv (expr_type r)
              (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `compile_revert_with_reason _ _ _ _ sm = (u, s6)` >>
  Cases_on `u` >> simp[] >>
  Cases_on `new_block ok s6` >> rename1 `new_block ok s6 = (x7, s7)` >>
  simp[] >> strip_tac >> gvs[] >> suspend "control"
QED

Resume compile_assert_reason_frag[control]:
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  imp_res_tac emit_inst_extends >>
  `reason_vv_ok vv` by metis_tac[] >>
  `cs_extends s5 s6` by metis_tac[reason_expr_revert_extends] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s6 s7` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s4 s5 func /\
   fn_has_code s5 s6 func` by
    metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
              cs_extends_refl] >>
  `lookup_block s4.cs_current_bb func.fn_blocks =
     SOME <| bb_label := s4.cs_current_bb;
             bb_instructions := s4.cs_current_insts |>` by
    metis_tac[fn_has_code_new_block] >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
           (INL (BoolV F), es1) ==>
         eval_stmt cx (Raise (RaiseReason r)) es1 = (res, es')` by
    metis_tac[eval_assert_reason_false] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def, eval_expr_switch_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >> simp[] >> strip_tac >>
  `expr_res_ok r1 /\ !v. r1 = INL v ==> ?b. v = BoolV b` by
    (Cases_on `r1` >> gvs[]
     >- (rename1 `INL plain` >>
         Cases_on `?b. plain = BoolV b` >> gvs[expr_res_ok_def] >>
         `plain <> BoolV T /\ plain <> BoolV F` by metis_tac[] >>
         gvs[raise_def, stmt_res_ok_def]) >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e es` >>
     rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     imp_res_tac read_result_no_control >>
     imp_res_tac (cj 1 eval_expr_no_control) >>
     gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  `s3.cs_current_bb = s1.cs_current_bb /\
   s3.cs_current_insts = s1.cs_current_insts` by metis_tac[] >>
  drule_all cond_jump_frag >> strip_tac
  >- (Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def]
      >- (disj1_tac >> rename1 `stmt_state_rel func cenv cx es' sv` >>
          qexists_tac `jump_to s7.cs_current_bb sv` >>
          gvs[stmt_lands_def, stmt_state_rel_jump_to, cenv_top_ext_refl,
              block_is_terminated_def] >>
          simp[jump_to_def, lookup_var_def] >> fs[lookup_var_def, jump_to_def]) >>
      suspend "abort") >>
  disj2_tac >> qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >>
  disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_reason_frag[abort]:
  disj2_tac >> rename1 `stmt_state_rel func cenv cx es1 sv` >>
  `eval_stmt cx (Raise (RaiseReason r)) es1 = (res, es')` by
    (first_x_assum irule >> simp[]) >>
  drule_all eval_raise_reason_cases >> disch_then (qx_choose_then `rr` assume_tac) >>
  qspecl_then [`rr`, `res`, `RetQ`, `es'`] mp_tac raise_reason_exits >>
  impl_tac >- fs[] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `r`, `es1`, `rr`, `es'`, `s5`,
               `vv`, `sm`, `expr_type r`,
               `type_memory_bytes cenv (expr_type r)`, `s6`, `jump_to s5.cs_current_bb sv`,
               `stmt_exit RetQ es' res`] mp_tac reason_expr_revert_frag >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qpat_x_assum `frag_exec _ s5 s6 _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `jump_to s5.cs_current_bb sv`] mp_tac) >>
  impl_tac >- simp[jump_to_def, stmt_state_rel_jump_to] >> strip_tac >>
  qpat_x_assum
    `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
    (qspec_then `fuel` mp_tac) >>
  impl_tac >- metis_tac[exit_result_not_error] >>
  disch_then (qx_choose_then `f0` strip_assume_tac) >>
  qexists_tac `f0` >> gvs[]
QED

Finalise compile_assert_reason_frag

(* Check the public forced boundary and both reason-expression consumers. *)
Theorem compile_assert_reason_frag_general:
  !ctx func cx lctx RetQ cenv ty e r es res es'.
    eval_stmt cx (Assert e (AssertReason r)) es = (res, es') /\
    (!ml str. r <> Literal (BaseT (StringT ml)) (StringL str)) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!es1 sa vv sm sb s0.
       (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (BoolV F), es1) /\
       compile_expr cenv (expr_type r) r sa = (vv, sm) /\
       compile_revert_with_reason cenv vv (expr_type r)
         (type_memory_bytes cenv (expr_type r)) sm = ((), sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\ stmt_res_ok lctx res ==>
       frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es1 s)
         (\s. F) (stmt_exit RetQ es' res)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >>
  `compile_reason_message cenv r = compile_expr cenv (expr_type r) r` by
    metis_tac[compile_reason_message_expr] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qpat_assum `compile_reason_message _ _ = _` (fn th => rewrite_tac[th]) >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op, s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok, s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl, s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u4, s4)` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (x5, s5)` >> simp[] >>
  Cases_on `compile_expr cenv (expr_type r) r s5` >>
  rename1 `compile_expr _ _ _ s5 = (vv, sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv vv (expr_type r)
              (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `compile_revert_with_reason _ _ _ _ sm = (u, s6)` >>
  Cases_on `u` >> simp[] >>
  Cases_on `new_block ok s6` >> rename1 `new_block ok s6 = (x7, s7)` >>
  simp[] >> strip_tac >> gvs[] >> suspend "control"
QED

Resume compile_assert_reason_frag_general[control]:
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  imp_res_tac emit_inst_extends >>
  `cs_extends s5 s6` by metis_tac[reason_expr_revert_extends_any] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s6 s7` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s4 s5 func /\
   fn_has_code s5 s6 func` by
    metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
              cs_extends_refl] >>
  `lookup_block s4.cs_current_bb func.fn_blocks =
     SOME <| bb_label := s4.cs_current_bb;
             bb_instructions := s4.cs_current_insts |>` by
    metis_tac[fn_has_code_new_block] >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def, eval_expr_switch_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >> simp[] >> strip_tac >>
  `expr_res_ok r1 /\ !v. r1 = INL v ==> ?b. v = BoolV b` by
    (Cases_on `r1` >> gvs[]
     >- (rename1 `INL plain` >>
         Cases_on `?b. plain = BoolV b` >> gvs[expr_res_ok_def] >>
         `plain <> BoolV T /\ plain <> BoolV F` by metis_tac[] >>
         gvs[raise_def, stmt_res_ok_def]) >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e es` >>
     rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     imp_res_tac read_result_no_control >>
     imp_res_tac (cj 1 eval_expr_no_control) >>
     gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  `s3.cs_current_bb = s1.cs_current_bb /\
   s3.cs_current_insts = s1.cs_current_insts` by metis_tac[] >>
  drule_all cond_jump_frag >> strip_tac
  >- (Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def]
      >- (disj1_tac >> rename1 `stmt_state_rel func cenv cx es' sv` >>
          qexists_tac `jump_to s7.cs_current_bb sv` >>
          gvs[stmt_lands_def, stmt_state_rel_jump_to, cenv_top_ext_refl,
              block_is_terminated_def] >>
          simp[jump_to_def, lookup_var_def] >> fs[lookup_var_def, jump_to_def]) >>
      suspend "abort") >>
  disj2_tac >> qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >>
  disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_reason_frag_general[abort]:
  disj2_tac >> rename1 `stmt_state_rel func cenv cx es1 sv` >>
  `frag_exec ctx s5 s6
     (\s. s = jump_to s5.cs_current_bb sv /\ stmt_state_rel func cenv cx es1 s)
     (\s. F) (stmt_exit RetQ es' res)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `frag_exec _ s5 s6 _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `jump_to s5.cs_current_bb sv`] mp_tac) >>
  impl_tac >- simp[jump_to_def, stmt_state_rel_jump_to] >> strip_tac >>
  qpat_x_assum
    `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
    (qspec_then `fuel` mp_tac) >>
  impl_tac >- metis_tac[exit_result_not_error] >>
  disch_then (qx_choose_then `f0` strip_assume_tac) >>
  qexists_tac `f0` >> gvs[]
QED

Finalise compile_assert_reason_frag_general


val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "REASON_EXPR_FORCE_AUDIT OK\n"
     else raise Fail "reason expression inherited admission"
  end) [compile_reason_message_expr, reason_expr_revert_extends,
        reason_expr_revert_frag, eval_raise_reason_cases,
        compile_raise_reason_frag, compile_assert_reason_frag];
