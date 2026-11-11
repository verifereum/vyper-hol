(* Pure source forcing and compiler decomposition for conditional statements. *)
Theory stmtSimIfProps
Ancestors
  gasExemptCert gasSummary gasSummaryCompose gasOutcome gasContext fragGasPath gasCount
  stmtSimDefs stmtSimProps exprSimDefs loweringPosts list rich_list finite_map pred_set
  fragExec localPtrsProps loweringSlice
  stmtLowering exprLowering compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

Theorem eval_expr_switch_forced:
  !cx e es kt kf.
    bind (eval_expr cx e) (\raw. switch_BoolV cx raw kt kf) es =
    (case (do raw <- eval_expr cx e; read_result cx raw od) es of
       (INR ex, s) => (INR ex, s)
     | (INL v, s) => if v = BoolV T then kt s
                    else if v = BoolV F then kf s
                    else raise (Error (TypeError "not BoolV")) s)
Proof
  rpt gen_tac >> simp[switch_BoolV_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, est)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `eval_expr cx e es = (INL captured, est)` >>
  Cases_on `read_result cx captured est` >> rename1 `_ = (forced, esf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem eval_assert_forced_parts:
  !cx e ak es res es'.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    eval_stmt cx (Assert e ak) es = (res, es') ==>
    ?r s. (do raw <- eval_expr cx e; read_result cx raw od) es = (r,s) /\
      (case r of INR ex => (INR ex,s)
       | INL v => if v = BoolV T then (INL (),s)
                  else if v = BoolV F then
                    (INR (AssertException
                      (if ak = AssertBare then "" else "UNREACHABLE")),s)
                  else (INR (Error (TypeError "not BoolV")),s)) = (res,es')
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, eval_expr_switch_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (forced,sf)` >>
  simp[return_def, raise_def] >> Cases_on `forced` >> simp[]
QED

Theorem eval_assert_forced_ok:
  !cx e ak es res es' lctx.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    eval_stmt cx (Assert e ak) es = (res, es') /\
    stmt_res_ok lctx res ==>
    ?r s. (do raw <- eval_expr cx e; read_result cx raw od) es = (r,s) /\
      expr_res_ok r /\ (!v. r = INL v ==> ?b. v = BoolV b) /\
      (case r of INR ex => (INR ex,s)
       | INL v => if v = BoolV T then (INL (),s)
                  else if v = BoolV F then
                    (INR (AssertException
                      (if ak = AssertBare then "" else "UNREACHABLE")),s)
                  else (INR (Error (TypeError "not BoolV")),s)) = (res,es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_at Any eval_assert_forced_parts >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!exc. r = INR exc ==> no_control_exc exc` by
    (rpt strip_tac >> gvs[] >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e es` >>
     rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  qexistsl_tac [`r`,`s`] >> simp[] >>
  Cases_on `r` >> gvs[expr_res_ok_def, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[stmt_res_ok_def, no_control_exc_def] >> metis_tac[]
QED




Theorem eval_stmt_if_all:
  !cx c ss1 ss2 es res es'.
    eval_stmt cx (If c ss1 ss2) es = (res, es') ==>
    ?r1 es1. (do result <- eval_expr cx c; read_result cx result od) es = (r1, es1) /\
      ((?ex. r1 = INR ex /\ res = INR ex /\ es' = es1) \/
       (?tv. r1 = INL tv /\ (!b. tv <> BoolV b) /\
             ?m. res = INR (Error (TypeError m))) \/
       (?b es2 sc rest. r1 = INL (BoolV b) /\
          eval_stmts cx (if b then ss1 else ss2)
            (es1 with scopes := FEMPTY :: es1.scopes) = (res, es2) /\
          es2.scopes = sc :: rest /\ es' = es2 with scopes := rest /\
          !n. n IN FDOM sc ==> lookup_scopes n rest = NONE))
Proof
  rpt gen_tac >>
  `!x. x with scopes updated_by CONS FEMPTY =
       x with scopes := FEMPTY :: x.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       finally_def, return_def] >>
  Cases_on `eval_expr cx c es` >> rename1 `eval_expr cx c es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `switch_BoolV cx raw` >>
  Cases_on `read_result cx raw es1` >> rename1 `_ = (forced, esF)` >>
  `esF = es1` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `forced`
  >- (rename1 `read_result cx raw es1 = (INL tv, es1)` >>
      simp[switch_BoolV_def, bind_def, read_result_empty_scope] >>
      Cases_on `?b. tv = BoolV b`
  >- (
    gvs[] >>
    qabbrev_tac `esA = es1 with scopes := FEMPTY :: es1.scopes` >>
    Cases_on `eval_stmts cx (if b then ss1 else ss2) esA` >>
    rename1 `_ = (r2, es2)` >>
    `(if BoolV b = BoolV T then eval_stmts cx ss1
      else if BoolV b = BoolV F then eval_stmts cx ss2
      else raise (Error (TypeError "not BoolV"))) esA = (r2, es2)` by
      (Cases_on `b` >> gvs[]) >>
    `es2.scopes <> []` by
      (drule eval_stmts_preserves_scopes_dom >>
       simp[preserves_scopes_dom_def, Abbr `esA`]) >>
    Cases_on `es2.scopes` >> gvs[] >> rename1 `es2.scopes = top2 :: rest2` >>
    `!id. id IN FDOM top2 ==> lookup_scopes id rest2 = NONE` by
      (rpt strip_tac >> drule eval_stmts_new_in_head_not_in_tail >>
       simp[Abbr `esA`]) >>
    Cases_on `r2` >> simp[pop_scope_def, return_def, raise_def]) >>
  `tv <> BoolV T /\ tv <> BoolV F` by metis_tac[] >>
  simp[raise_def, pop_scope_def, return_def] >>
  strip_tac >> disj1_tac >> gvs[] >> metis_tac[]) >>
  simp[switch_BoolV_def, bind_def, read_result_empty_scope,
       raise_def, pop_scope_def, return_def]
QED

(* Force the captured condition before entering the fresh lexical frame. *)
Theorem eval_stmt_if_forced:
  eval_stmt cx (If c ss1 ss2) =
  bind (bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then
           ignore_bind push_scope (finally (eval_stmts cx ss1) pop_scope)
         else if v = BoolV F then
           ignore_bind push_scope (finally (eval_stmts cx ss2) pop_scope)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  `!st. st with scopes updated_by CONS FEMPTY =
        st with scopes := FEMPTY :: st.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       return_def] >>
  Cases_on `eval_expr cx c x` >> rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `switch_BoolV cx captured` >>
  Cases_on `read_result cx captured st` >> rename1 `_ = (forced, sf)` >>
  `sf = st` by metis_tac[read_result_state] >> gvs[] >>
  simp[switch_BoolV_def, bind_def, read_result_empty_scope,
       finally_def, pop_scope_def, return_def] >>
  Cases_on `forced` >> simp[raise_def] >>
  rpt IF_CASES_TAC >>
  simp[ignore_bind_def, bind_def, push_scope_def, return_def, finally_def,
       read_result_empty_scope, raise_def, pop_scope_def]
QED

Theorem eval_stmt_if_condition_cert:
  !memory tops ctx func cx c ss1 ss2 es s0 marks err ee leaf finish.
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx c) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finish) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (If c ss1 ss2)) (return ()))
    (es,s0) marks (err,ee) (leaf,finish)
Proof
  rpt strip_tac >> rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem if_push_scope_marked:
  ~s0.vs_halted ==>
  gas_marked_exec memory (ctx,func) push_scope (es,s0) [] (INL ())
    (es with scopes := FEMPTY :: es.scopes) (OK s0)
Proof
  strip_tac >> simp[gas_marked_exec_def, push_scope_def, return_def,
                    evaluation_state_component_equality] >>
  irule fragGasModeTheory.gas_marked_path_from_mem >>
  simp[fragGasPathMemTheory.gas_path_mem_rules]
QED

Theorem eval_stmt_if_scoped_cert:
  !memory tops ctx func cx ss es s0 marks err ee leaf finish top rest.
  gas_marked_exec memory (ctx,func) push_scope
    (es,s0) [] (INL ()) (es with scopes := FEMPTY :: es.scopes) (OK s0) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmts cx ss) (return ()))
    ((es with scopes := FEMPTY :: es.scopes) with gas_obs := [],s0)
    marks (err,ee) (leaf,finish) /\
  ee.scopes = top :: rest ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (ignore_bind push_scope
       (finally (eval_stmts cx ss) pop_scope)) (return ()))
    (es,s0) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt strip_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  drule gas_exempt_cert_bind_unit >> simp[] >>
  disch_then irule >>
  rewrite_tac[GSYM ignore_bind_def, ignore_bind_finally_unit] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
  simp[pop_scope_def, return_def] >>
  gvs[evaluation_state_component_equality]
QED

Theorem if_branch_cert_scopes:
  !memory tops ctx func cx ss es s0 marks err ee leaf finish.
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmts cx ss) (return ()))
    (es with scopes := FEMPTY :: es.scopes,s0)
    marks (err,ee) (leaf,finish) ==>
  ?top rest. ee.scopes = top :: rest
Proof
  rpt strip_tac >> drule gas_exempt_cert_execution >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def] >>
  Cases_on `eval_stmts cx ss
    ((es with scopes := FEMPTY :: es.scopes) with gas_obs :=
       gas_explicit marks s0.vs_gas_readings)` >>
  rename1 `_ = (res,st)` >> Cases_on `res` >>
  simp[return_def] >> strip_tac >> gvs[] >>
  drule eval_stmts_preserves_scopes_dom >>
  simp[preserves_scopes_dom_def] >>
  Cases_on `ee.scopes` >> simp[]
QED

Theorem eval_stmt_if_branch_cert:
  !memory tops ctx func cx c ss1 ss2 es s0 left b mid t right err ee
     leaf finish top rest.
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx c) (read_result cx))
    (es,s0) left (INL (BoolV b)) mid (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmts cx (if b then ss1 else ss2)) (return ()))
    ((mid with scopes := FEMPTY :: mid.scopes) with gas_obs := [],t)
    right (err,ee) (leaf,finish) /\
  ee.scopes = top :: rest ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (If c ss1 ss2)) (return ()))
    (es,s0) (left ++ right) (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt strip_tac >> rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  drule gas_exempt_cert_bind_value >>
  disch_then irule >>
  Cases_on `b` >> simp[GSYM ignore_bind_def] >>
  irule eval_stmt_if_scoped_cert >>
  simp[if_push_scope_marked] >>
  gvs[evaluation_state_component_equality]
QED

Theorem if_condition_admissible:
  gas_admissible (eval_stmt cx (If c ss1 ss2)) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def] >>
     Cases_on `eval_expr cx c (es with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[eval_stmt_if_forced, bind_def] >>
  fs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def] >>
  metis_tac[]
QED

Theorem eval_stmt_if_selected:
  bind (eval_expr cx c) (read_result cx) es = (INL (BoolV b),mid) /\
  eval_stmts cx (if b then ss1 else ss2)
    (mid with scopes := FEMPTY :: mid.scopes) = (res,ee) ==>
  eval_stmt cx (If c ss1 ss2) es =
    (res,ee with scopes := TL ee.scopes)
Proof
  strip_tac >>
  `ee.scopes <> []` by
    (drule eval_stmts_preserves_scopes_dom >>
     simp[preserves_scopes_dom_def]) >>
  simp[eval_stmt_if_forced, bind_def] >>
  Cases_on `b` >>
  fs[ignore_bind_def, push_scope_def, return_def, bind_def, finally_def] >>
  `!st. st with scopes updated_by CONS FEMPTY =
        st with scopes := FEMPTY :: st.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[] >> Cases_on `res` >> Cases_on `ee.scopes` >>
  gvs[pop_scope_def, return_def, raise_def]
QED

Theorem if_branch_admissible:
  gas_admissible (eval_stmt cx (If c ss1 ss2)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV b),mid with gas_obs := tail)) ==>
  gas_admissible (eval_stmts cx (if b then ss1 else ss2)) (stmt_res_ok lctx)
    (mid with scopes := FEMPTY :: mid.scopes)
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  `eval_stmt cx (If c ss1 ss2) (es with gas_obs := xs ++ gs) =
     (res,ee with scopes := TL ee.scopes)` by
    (irule eval_stmt_if_selected >> qexistsl_tac [`b`, `mid with gas_obs := gs`] >>
     simp[] >> gvs[evaluation_state_component_equality]) >>
  metis_tac[]
QED

Theorem eval_stmt_if_selected_tails:
  (!tail. bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := xs ++ tail) =
     (INL (BoolV b),mid with gas_obs := tail)) /\
  (!tail. eval_stmts cx (if b then ss1 else ss2)
     ((mid with scopes := FEMPTY :: mid.scopes) with gas_obs := ys ++ tail) =
     (res,ee with gas_obs := tail)) ==>
  !tail. eval_stmt cx (If c ss1 ss2)
    (es with gas_obs := (xs ++ ys) ++ tail) =
    (res,(ee with scopes := TL ee.scopes) with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `!tail. bind _ _ _ = _`
    (qspec_then `ys ++ tail` assume_tac) >>
  drule eval_stmt_if_selected >>
  disch_then (qspecl_then [`ss2`, `ss1`, `res`, `ee with gas_obs := tail`] mp_tac) >>
  simp[APPEND_ASSOC] >>
  gvs[evaluation_state_component_equality]
QED

Theorem compile_if_parts_all:
  !cenv lctx ty c ss1 ss2 st st'.
    compile_stmt cenv lctx ty (If c ss1 ss2) st = ((), st') ==>
    ?cond_op s1 s4 s5 s6 s7 s8 s9 s10 s11 then_lbl else_lbl exit_lbl x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      cs_extends s1 s4 /\ s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      s4.cs_next_var = s1.cs_next_var /\
      emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [] s4 =
        ((), s5) /\
      new_block then_lbl s5 = (x5, s6) /\
      compile_stmts cenv lctx ty ss1 s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label exit_lbl] [] s7 = ((), s8)) /\
      new_block else_lbl s8 = (x8, s9) /\
      compile_stmts cenv lctx ty ss2 s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label exit_lbl] [] s10 = ((), s11)) /\
      (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
       ?x11. new_block exit_lbl s11 = (x11, st')) /\
      (block_is_terminated s7 /\ block_is_terminated s10 ==> st' = s11)
Proof
  rpt gen_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_get_def,
       emit_jmp_if_not_terminated_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  (fn (asl, w) =>
     MAP_EVERY (fn v => Cases_on `^v`)
       (filter (fn v => type_of v = oneSyntax.one_ty)
          (free_varsl (w :: asl))) (asl, w)) >>
  rename1 `fresh_label "then" s1 = (then_lbl, s2)` >>
  rename1 `fresh_label "else" s2 = (else_lbl, s3)` >>
  rename1 `fresh_label "if_exit" s3 = (exit_lbl, s4)` >>
  rename1 `emit_inst JNZ _ _ s4 = ((), s5)` >>
  rename1 `new_block then_lbl s5 = (x5, s6)` >>
  rename1 `compile_stmts _ _ _ ss1 s6 = ((), s7)` >>
  rename1 `new_block else_lbl s8 = (x8, s9)` >>
  rename1 `compile_stmts _ _ _ ss2 s9 = ((), s10)` >>
  strip_tac >>
  rename1 `(if block_is_terminated s10 then _ else _) s10 = ((), s11)` >>
  qexistsl_tac [`s4`, `s5`, `s6`, `s7`, `s8`, `s9`, `s10`, `s11`,
                `then_lbl`, `else_lbl`, `exit_lbl`, `x5`, `x8`] >>
  imp_res_tac fresh_label_props >>
  `cs_extends s1 s4` by
    metis_tac[cs_extends_fresh_label, cs_extends_trans] >>
  rpt conj_tac >> fs[] >>
  TRY (Cases_on `block_is_terminated s7` >> fs[comp_return_def] >> NO_TAC) >>
  TRY (Cases_on `block_is_terminated s10` >> fs[comp_return_def] >> NO_TAC) >>
  rpt strip_tac >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[]
QED


Theorem if_optional_jump_extends:
  (if block_is_terminated sa then sb = sa
   else emit_inst JMP [Label lbl] [] sa = ((),sb)) ==>
  cs_extends sa sb /\ sa.cs_next_var = sb.cs_next_var
Proof
  Cases_on `block_is_terminated sa` >> simp[] >> strip_tac
  >- simp[cs_extends_refl] >>
  drule emit_inst_extends >> strip_tac >>
  metis_tac[cs_appends_emit_helpers, cs_appends_def]
QED

Theorem if_branch_compiler_mono:
  cs_mono (stmts_env cenv lctx ty ss) /\
  compile_stmts cenv lctx ty ss sa = ((),sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  simp[compile_stmts_env, cs_mono_def] >> strip_tac >>
  Cases_on `stmts_env cenv lctx ty ss sa` >> gvs[] >> metis_tac[]
QED

Theorem compile_if_code_layout:
  compile_stmt cenv lctx ty (If c ss1 ss2) sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!sx op sy. lower_value compile_expr cenv (BaseT BoolT) c sx = (op,sy) ==>
    cs_extends sx sy /\ sx.cs_next_var <= sy.cs_next_var) /\
  cs_mono (stmts_env cenv lctx ty ss1) /\
  cs_mono (stmts_env cenv lctx ty ss2) ==>
  ?op cond pre post tl el xl.
    lower_value compile_expr cenv (BaseT BoolT) c sa = (op,cond) /\
    fn_has_code sa cond func /\ cs_extends sa cond /\
    sa.cs_next_var <= cond.cs_next_var /\
    pre.cs_current_bb = cond.cs_current_bb /\
    pre.cs_current_insts = cond.cs_current_insts /\
    emit_inst JNZ [op; Label tl; Label el] [] pre = ((),post) /\
    fn_has_code pre post func /\
    (!b. ?entry last after.
      compile_stmts cenv lctx ty (if b then ss1 else ss2) entry = ((),last) /\
      entry.cs_current_bb = (if b then tl else el) /\
      entry.cs_current_insts = [] /\
      cs_extends sa entry /\ sa.cs_next_var <= entry.cs_next_var /\
      cs_extends entry last /\ cs_extends last sb /\
      fn_has_code entry last func /\ fn_has_code last after func /\
      (if block_is_terminated last then after = last
       else emit_inst JMP [Label xl] [] last = ((),after)) /\
      (~block_is_terminated last ==>
        sb.cs_current_bb = xl /\ sb.cs_current_insts = []))
Proof
  strip_tac >> drule compile_if_parts_all >> strip_tac >>
  imp_res_tac new_block_props >>
  imp_res_tac if_branch_compiler_mono >>
  imp_res_tac if_optional_jump_extends >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by metis_tac[] >>
  `cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s8 s9` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `cs_extends s11 sb` by
    (Cases_on `block_is_terminated s7 /\ block_is_terminated s10`
     >- (fs[] >> simp[cs_extends_refl]) >>
     `?x11. new_block exit_lbl s11 = (x11,sb)` by metis_tac[] >>
     metis_tac[cs_extends_new_block]) >>
  `cs_extends sa s4 /\ cs_extends sa s6 /\ cs_extends sa s9 /\
   cs_extends s7 sb /\ cs_extends s10 sb /\ cs_extends s1 sb /\
   cs_extends s5 sb /\ cs_extends s8 sb /\
   cs_extends sa s7 /\ cs_extends sa s10` by metis_tac[cs_extends_trans] >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var` by
    (imp_res_tac emit_inst_extends >> fs[] >> decide_tac) >>
  qexistsl_tac [`cond_op`, `s1`, `s4`, `s5`, `then_lbl`, `else_lbl`, `exit_lbl`] >>
  simp[] >> conj_tac
  >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
  conj_tac
  >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
  gen_tac >> Cases_on `b` >> simp[]
  >- (qexistsl_tac [`s6`, `s7`, `s8`] >> simp[] >>
      conj_tac >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
      conj_tac >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
      strip_tac >>
      `?x11. new_block exit_lbl s11 = (x11,sb)` by metis_tac[] >>
      imp_res_tac new_block_props >> fs[]) >>
  qexistsl_tac [`s9`, `s10`, `s11`] >> simp[] >>
  conj_tac >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
  conj_tac >- (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
  strip_tac >>
  `?x11. new_block exit_lbl s11 = (x11,sb)` by metis_tac[] >>
  imp_res_tac new_block_props >> fs[]
QED

Theorem if_condition_operand:
  expr_type c = BaseT BoolT /\
  expr_post ctx func cenv cx c es sa sb s0 mid (BoolV b) op s ==>
  eval_operand op s = SOME (val_to_w256 (BoolV b))
Proof
  strip_tac >> gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
       valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def]
QED

Theorem if_branch_post_pop:
  stmt_post ctx func cx lctx cenv cenv' sa sb s0 res ee t /\
  ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  stmt_post ctx func cx lctx cenv cenv sa sb s0 res
    (ee with scopes := rest) t
Proof
  rewrite_tac[stmt_post_def] >> strip_tac >>
  qexists_tac `cenv` >> simp[cenv_top_ext_refl] >>
  irule stmt_state_rel_pop_top_ext >>
  conj_tac >- (qexists_tac `sc` >> simp[]) >>
  qexists_tac `cenv''` >> simp[]
QED

Theorem if_branch_marked_scopes:
  gas_marked_exec memory (ctx,func) (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0) marks res ee r ==>
  ?sc rest. ee.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE)
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  drule eval_stmts_preserves_scopes_dom >>
  simp[preserves_scopes_dom_def] >> strip_tac >>
  Cases_on `ee.scopes` >> gvs[] >>
  rpt strip_tac >> drule eval_stmts_new_in_head_not_in_tail >>
  simp[]
QED

Theorem if_branch_marked_cleanup:
  gas_marked_exec memory (ctx,func) (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0) marks res ee r /\
  ~s0.vs_halted /\ ee.scopes = sc :: rest ==>
  gas_marked_exec memory (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    (es,s0) marks res (ee with scopes := rest) r
Proof
  strip_tac >>
  `gas_marked_exec memory (ctx,func) (finally (eval_stmts cx ss) pop_scope)
     (es with scopes := FEMPTY :: es.scopes,s0) marks res
     (ee with scopes := rest) r` by
    (irule gas_marked_exec_finally >> qexists_tac `ee` >>
     simp[pop_scope_def, return_def, evaluation_state_component_equality]) >>
  `!st. st with scopes updated_by CONS FEMPTY =
         st with scopes := FEMPTY :: st.scopes` by
    simp[evaluation_state_component_equality] >>
  gvs[gas_marked_exec_def] >> gen_tac >>
  simp[ignore_bind_def, bind_def, push_scope_def, return_def]
QED

Theorem if_branch_outcome_cleanup:
  gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0)
    (stmt_post ctx func cx lctx cenv cenv' sa sb s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\
  es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      drule if_branch_marked_scopes >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `ee with scopes := rest`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup >> simp[] >> metis_tac[]) >>
      disj1_tac >> qexists_tac `t` >> simp[] >>
      irule if_branch_post_pop >> simp[] >> metis_tac[])
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      drule if_branch_marked_scopes >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `ee with scopes := rest`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup >> simp[] >> metis_tac[]) >>
      disj2_tac >> gvs[stmt_exit_def] ) >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  drule if_branch_cert_scopes >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `fin`] >>
  irule eval_stmt_if_scoped_cert >>
  simp[if_push_scope_marked] >>
  `es with <|scopes := FEMPTY :: es.scopes; gas_obs := []|> =
   es with scopes := FEMPTY :: es.scopes` by
    simp[evaluation_state_component_equality] >> simp[]
QED

Theorem if_branch_post_to_exit:
  stmt_post ctx func cx lctx cenv cenv sa last s0 res ee t /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  ?u. gas_path ctx func t 0 (OK u) /\
      stmt_post ctx func cx lctx cenv cenv sa sb s0 res ee u
Proof
  strip_tac >> Cases_on `res = INL ()`
  >- (gvs[] >>
      `~block_is_terminated last` by fs[stmt_post_def] >>
      `t.vs_current_bb = last.cs_current_bb /\
       t.vs_inst_idx = LENGTH last.cs_current_insts /\ ~t.vs_halted` by
        fs[stmt_post_def, stmt_lands_def] >>
      `gas_path ctx func t 0 (OK (jump_to xl t))` by
        (irule emit_jump_zero_path >> simp[] >>
         qexistsl_tac [`last`, `after`] >>
         fs[] >> drule emit_inst_extends >> simp[]) >>
      qexists_tac `jump_to xl t` >> simp[] >>
      qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[stmt_post_def, stmt_lands_def, stmt_state_rel_jump_to,
           block_is_terminated_def, jump_to_def, lookup_var_def]) >>
  qexists_tac `t` >>
  conj_tac >- (fs[stmt_post_def] >> metis_tac[gas_path_rules]) >>
  gvs[stmt_post_def, stmt_lands_def] >> metis_tac[]
QED

Theorem if_branch_outcome_to_exit:
  gas_outcome F (cx_tops cx) (ctx,func) source (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa last s0) R /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome F (cx_tops cx) (ctx,func) source (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0) R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      drule_all if_branch_post_to_exit >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `OK u`] >> simp[] >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
      strip_tac >> simp[] >>
      drule_all gas_path_then >> simp[] )
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem if_branch_outcome:
  gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0)
    (stmt_post ctx func cx lctx cenv cenv' sa last s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\
  es.gas_obs = [] /\ ~s0.vs_halted /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> irule if_branch_outcome_to_exit >>
  qexistsl_tac [`after`, `last`, `xl`] >> simp[] >>
  irule if_branch_outcome_cleanup >> simp[] >> metis_tac[]
QED

Theorem if_condition_stmt_post:
  expr_post ctx func cenv cx c es sa cond s0 mid v op t /\
  sa.cs_next_var <= entry.cs_next_var /\
  stmt_post ctx func cx lctx cenv cenv entry sb (jump_to label t) res ee u ==>
  stmt_post ctx func cx lctx cenv cenv sa sb s0 res ee u
Proof
  simp[expr_post_def, stmt_post_def, jump_to_def, lookup_var_def] >>
  strip_tac >> qexists_tac `cenv''` >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at entry x` by fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem if_selected_outcome_prefix:
  gas_marked_exec F (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV b)) mid (OK t) /\
  gas_path ctx func t 0 (OK (jump_to label t)) /\
  expr_post ctx func cenv cx c es sa cond s0 (mid with gas_obs := []) (BoolV b) op t /\
  sa.cs_next_var <= entry.cs_next_var /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))
    (mid with gas_obs := [],jump_to label t)
    (stmt_post ctx func cx lctx cenv cenv entry sb (jump_to label t))
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_stmt cx (If c ss1 ss2)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (bind (eval_expr cx c) (read_result cx))
     (es,s0) marks (INL (BoolV b)) mid (OK (jump_to label t))` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     strip_tac >> simp[] >> drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "normal"
  >- suspend "exit"
  >> suspend "cert"
QED

Resume if_selected_outcome_prefix[normal]:
  gvs[] >> qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `OK t'`] >> conj_tac
  >- (rewrite_tac[eval_stmt_if_forced] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`mid`, `jump_to label t`, `BoolV b`] >>
      simp[] >> Cases_on `b` >> fs[]) >>
  disj1_tac >> simp[] >> drule_all if_condition_stmt_post >> simp[]
QED
Resume if_selected_outcome_prefix[exit]:
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
  rewrite_tac[eval_stmt_if_forced] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl_tac [`mid`, `jump_to label t`, `BoolV b`] >>
  simp[] >> Cases_on `b` >> fs[]
QED
Resume if_selected_outcome_prefix[cert]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`mid`, `jump_to label t`, `BoolV b`] >> simp[] >>
  Cases_on `b` >> fs[GSYM ignore_bind_def]
QED
Finalise if_selected_outcome_prefix

Theorem if_branch_post_pop_mem:
  (?cenv''.
    stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel ctx func cenv'' cx ee t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    return_buf_frame d cenv'' sb t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next) /\
  ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  ?cenv''.
    stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' (ee with scopes := rest).scopes /\
    stmt_state_rel ctx func cenv'' cx (ee with scopes := rest) t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    return_buf_frame d cenv'' sb t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> qexists_tac `cenv` >> simp[cenv_top_ext_refl] >>
  conj_tac
  >- (irule stmt_state_rel_pop_top_ext >>
      conj_tac >- (qexists_tac `sc` >> simp[]) >>
      qexists_tac `cenv''` >> simp[]) >>
  `cenv''.ce_return_buf = cenv.ce_return_buf` by
    (fs[cenv_top_ext_def, compile_env_component_equality]) >>
  Cases_on `d` >> gvs[return_buf_frame_def] >>
  PairCases_on `x` >> gvs[return_buf_frame_def]
QED

Theorem if_branch_outcome_cleanup_mem:
  gas_outcome T (cx_tops cx) (ctx,func) (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0)
    (\res ee t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\
  es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0)
    (\res ee t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      drule if_branch_marked_scopes >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `ee with scopes := rest`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup >> simp[] >> metis_tac[]) >>
      disj1_tac >> qexists_tac `t` >> simp[] >>
      irule (SRULE [] (Q.INST [`ee` |-> `ee with gas_obs := []`]
        if_branch_post_pop_mem)) >> gvs[] >> metis_tac[])
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      drule if_branch_marked_scopes >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `ee with scopes := rest`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup >> simp[] >> metis_tac[]) >>
      disj2_tac >> gvs[stmt_exit_def]) >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  drule if_branch_cert_scopes >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `fin`] >>
  irule eval_stmt_if_scoped_cert >>
  simp[if_push_scope_marked] >>
  `es with <|scopes := FEMPTY :: es.scopes; gas_obs := []|> =
   es with scopes := FEMPTY :: es.scopes` by
    simp[evaluation_state_component_equality] >> simp[]
QED

Theorem if_branch_post_to_exit_mem:
  (?cenv''.
    stmt_lands lctx last res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated last /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel ctx func cenv'' cx ee t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    return_buf_frame d cenv'' last t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next) /\
  last.cs_next_var <= sb.cs_next_var /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  ?u. gas_path_mem ctx func t 0 (OK u) /\
    ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `return_buf_frame d cenv'' sb t` by
    (Cases_on `d` >> gvs[return_buf_frame_def] >>
     PairCases_on `x` >> gvs[return_buf_frame_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  Cases_on `res = INL ()`
  >- (fs[] >>
      qpat_x_assum `~block_is_terminated last ==> _` mp_tac >>
      simp[] >> strip_tac >>
      `t.vs_current_bb = last.cs_current_bb /\
       t.vs_inst_idx = LENGTH last.cs_current_insts` by
        fs[stmt_lands_def] >>
      `gas_path_mem ctx func t 0 (OK (jump_to xl t))` by
        (irule emit_jump_zero_path_mem >> simp[] >>
         qexistsl_tac [`last`, `after`] >>
         fs[] >> drule emit_inst_extends >> simp[]) >>
      qexists_tac `jump_to xl t` >> simp[] >>
      fs[stmt_lands_def, stmt_state_rel_jump_to, block_is_terminated_def,
         jump_to_def, lookup_var_def, allocaHistoryTheory.alloca_history_def] >>
      Cases_on `d` >> gvs[return_buf_frame_def] >>
      PairCases_on `x` >> gvs[return_buf_frame_def, lookup_var_def]) >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[fragGasPathMemTheory.gas_path_mem_rules] >>
  qexists_tac `cenv''` >> gvs[stmt_lands_def]
QED

Theorem if_branch_outcome_to_exit_mem:
  gas_outcome T (cx_tops cx) (ctx,func) source (es,s0)
    (\res ee t. ?cenv''.
      stmt_lands lctx last res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated last /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' last t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next) R /\
  last.cs_next_var <= sb.cs_next_var /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome T (cx_tops cx) (ctx,func) source (es,s0)
    (\res ee t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next) R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      qpat_x_assum `(\res ee t. _) _ _ _` mp_tac >>
      simp[] >> disch_tac >>
      drule_all (SRULE [] (Q.INST [`ee` |-> `ee with gas_obs := []`]
        if_branch_post_to_exit_mem)) >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `OK u`] >> conj_tac
      >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
          simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
          strip_tac >> simp[] >>
          drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[]) >>
      disj1_tac >> qexists_tac `u` >> simp[] >>
      qexists_tac `cenv''` >> simp[])
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem if_branch_outcome_mem:
  gas_outcome T (cx_tops cx) (ctx,func) (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0)
    (\res ee t. ?cenv''.
      stmt_lands lctx last res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated last /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' last t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\
  es.gas_obs = [] /\ ~s0.vs_halted /\
  last.cs_next_var <= sb.cs_next_var /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0)
    (\res ee t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> irule if_branch_outcome_to_exit_mem >>
  qexistsl_tac [`after`, `last`, `xl`] >> simp[] >>
  irule if_branch_outcome_cleanup_mem >> simp[] >> metis_tac[]
QED

Theorem if_condition_stmt_post_mem:
  expr_post ctx func cenv cx c es sa cond s0 mid v op t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  sa.cs_next_var <= entry.cs_next_var /\
  (?cenv''.
    stmt_lands lctx sb res u /\ ~u.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel ctx func cenv'' cx ee u /\
    (!x w. not_fresh_at entry x /\ lookup_var x (jump_to label t) = SOME w ==>
           lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP (jump_to label t).vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    return_buf_frame d cenv'' sb u /\ alloca_history func u /\
    (jump_to label t).vs_alloca_next <= u.vs_alloca_next) ==>
  ?cenv''.
    stmt_lands lctx sb res u /\ ~u.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel ctx func cenv'' cx ee u /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    return_buf_frame d cenv'' sb u /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next
Proof
  simp[expr_post_def, jump_to_def, lookup_var_def] >>
  strip_tac >> qexists_tac `cenv''` >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at entry x` by fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem if_selected_outcome_prefix_mem:
  gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV b)) mid (OK t) /\
  gas_path_mem ctx func t 0 (OK (jump_to label t)) /\
  expr_post ctx func cenv cx c es sa cond s0 (mid with gas_obs := []) (BoolV b) op t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  sa.cs_next_var <= entry.cs_next_var /\
  gas_outcome T (cx_tops cx) (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))
    (mid with gas_obs := [],jump_to label t)
    (\res ee u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee u /\
      (!x w. not_fresh_at entry x /\ lookup_var x (jump_to label t) = SOME w ==>
             lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP (jump_to label t).vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      (jump_to label t).vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_stmt cx (If c ss1 ss2)) (es,s0)
    (\res ee u. ?cenv''.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      return_buf_frame d cenv'' sb u /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
     (es,s0) marks (INL (BoolV b)) mid (OK (jump_to label t))` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     strip_tac >> simp[] >>
     drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "normal"
  >- suspend "exit"
  >> suspend "cert"
QED

Resume if_selected_outcome_prefix_mem[normal]:
  gvs[] >> qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `OK t'`] >> conj_tac
  >- (rewrite_tac[eval_stmt_if_forced] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`mid`, `jump_to label t`, `BoolV b`] >>
      simp[] >> Cases_on `b` >> fs[]) >>
  disj1_tac >> qexists_tac `t'` >> conj_tac >- simp[] >>
  irule (SRULE [] (Q.INST [`ee` |-> `es_end with gas_obs := []`]
    if_condition_stmt_post_mem)) >>
  qpat_assum `expr_post ctx func cenv cx c es sa cond s0 _ _ op t`
    (irule_at Any) >>
  qexistsl_tac [`label`, `entry`] >> simp[] >>
  qexists_tac `cenv''` >> simp[]
QED
Resume if_selected_outcome_prefix_mem[exit]:
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
  rewrite_tac[eval_stmt_if_forced] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl_tac [`mid`, `jump_to label t`, `BoolV b`] >>
  simp[] >> Cases_on `b` >> fs[]
QED
Resume if_selected_outcome_prefix_mem[cert]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`mid`, `jump_to label t`, `BoolV b`] >> simp[] >>
  Cases_on `b` >> fs[GSYM ignore_bind_def]
QED
Finalise if_selected_outcome_prefix_mem

Theorem compile_if_code_layout_frontiers:
  compile_stmt cenv lctx ty (If c ss1 ss2) sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!sx op sy. lower_value compile_expr cenv (BaseT BoolT) c sx = (op,sy) ==>
    cs_extends sx sy /\ sx.cs_next_var <= sy.cs_next_var) /\
  cs_mono (stmts_env cenv lctx ty ss1) /\
  cs_mono (stmts_env cenv lctx ty ss2) ==>
  ?op cond pre post tl el xl.
    lower_value compile_expr cenv (BaseT BoolT) c sa = (op,cond) /\
    fn_has_code sa cond func /\ cs_extends sa cond /\
    sa.cs_next_var <= cond.cs_next_var /\
    sa.cs_next_var <= sb.cs_next_var /\
    pre.cs_current_bb = cond.cs_current_bb /\
    pre.cs_current_insts = cond.cs_current_insts /\
    emit_inst JNZ [op; Label tl; Label el] [] pre = ((),post) /\
    fn_has_code pre post func /\
    (!b. ?entry last after.
      compile_stmts cenv lctx ty (if b then ss1 else ss2) entry = ((),last) /\
      entry.cs_current_bb = (if b then tl else el) /\
      entry.cs_current_insts = [] /\
      cs_extends sa entry /\ sa.cs_next_var <= entry.cs_next_var /\
      cs_extends entry last /\ cs_extends last sb /\
      last.cs_next_var <= sb.cs_next_var /\
      fn_has_code entry last func /\ fn_has_code last after func /\
      (if block_is_terminated last then after = last
       else emit_inst JMP [Label xl] [] last = ((),after)) /\
      (~block_is_terminated last ==>
        sb.cs_current_bb = xl /\ sb.cs_current_insts = []))
Proof
  strip_tac >> drule compile_if_parts_all >> strip_tac >>
  imp_res_tac new_block_props >>
  imp_res_tac if_branch_compiler_mono >>
  imp_res_tac if_optional_jump_extends >>
  imp_res_tac emit_inst_extends >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by metis_tac[] >>
  `cs_extends s4 s5` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s5 s6 /\ cs_extends s8 s9` by
    metis_tac[cs_extends_new_block] >>
  `cs_extends s11 sb /\ s11.cs_next_var = sb.cs_next_var /\
   (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
    sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [])` by
    (Cases_on `block_is_terminated s7 /\ block_is_terminated s10`
     >- metis_tac[cs_extends_refl] >>
     `?x. new_block exit_lbl s11 = (x,sb)` by metis_tac[] >>
     imp_res_tac new_block_props >> metis_tac[cs_extends_new_block]) >>
  `sa.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var /\
   s7.cs_next_var <= sb.cs_next_var /\ s10.cs_next_var <= sb.cs_next_var` by
    decide_tac >>
  `!a b. cs_extends sa a /\ cs_extends a b /\ cs_extends b sb ==>
    fn_has_code a b func` by metis_tac[fn_has_code_mid] >>
  `cs_extends sa s4 /\ cs_extends sa s6 /\ cs_extends sa s9 /\
   cs_extends s7 sb /\ cs_extends s10 sb /\ cs_extends s1 sb /\
   cs_extends s5 sb /\ cs_extends s8 sb /\ cs_extends sa s7 /\
   cs_extends sa s10` by metis_tac[cs_extends_trans] >>
  qexistsl_tac [`cond_op`, `s1`, `s4`, `s5`, `then_lbl`, `else_lbl`, `exit_lbl`] >>
  simp[] >> conj_tac
  >- metis_tac[cs_extends_refl] >>
  gen_tac >> Cases_on `b` >> simp[]
  >- (qexistsl_tac [`s6`, `s7`, `s8`] >> simp[] >>
      metis_tac[cs_extends_refl]) >>
  qexistsl_tac [`s9`, `s10`, `s11`] >> simp[] >>
  metis_tac[cs_extends_refl]
QED

Theorem compile_if_layout_mem:
  !cenv lctx ty c ss1 ss2 sa sb func.
    compile_stmt cenv lctx ty (If c ss1 ss2) sa = ((), sb) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\ fn_has_code sa sb func ==>
    ?op s1 s4 s5 s6 s7 s8 s9 s10 s11 lt lf le x5 x8.
      lower_value compile_expr cenv (BaseT BoolT) c sa = (op, s1) /\
      s4.cs_current_bb = s1.cs_current_bb /\
      s4.cs_current_insts = s1.cs_current_insts /\
      emit_inst JNZ [op; Label lt; Label lf] [] s4 = ((), s5) /\
      new_block lt s5 = (x5, s6) /\
      compile_stmts cenv lctx ty ss1 s6 = ((), s7) /\
      (if block_is_terminated s7 then s8 = s7
       else emit_inst JMP [Label le] [] s7 = ((), s8)) /\
      new_block lf s8 = (x8, s9) /\
      compile_stmts cenv lctx ty ss2 s9 = ((), s10) /\
      (if block_is_terminated s10 then s11 = s10
       else emit_inst JMP [Label le] [] s10 = ((), s11)) /\
      (~block_is_terminated s7 \/ ~block_is_terminated s10 ==>
       ?x11. new_block le s11 = (x11, sb)) /\
      (block_is_terminated s7 /\ block_is_terminated s10 ==> sb = s11) /\
      fn_has_code sa s1 func /\ fn_has_code s6 s7 func /\
      fn_has_code s9 s10 func /\ fn_has_code s7 s9 func /\
      fn_has_code s10 sb func /\
      lookup_block s5.cs_current_bb func.fn_blocks =
        SOME <| bb_label := s5.cs_current_bb;
                bb_instructions := s5.cs_current_insts |> /\
      cs_extends sa s6 /\ cs_extends sa s9 /\
      sa.cs_next_var <= s6.cs_next_var /\
      s6.cs_next_var <= sb.cs_next_var /\
      sa.cs_next_var <= s9.cs_next_var /\
      s9.cs_next_var <= sb.cs_next_var
Proof
  rpt strip_tac >> drule compile_if_parts_all >> strip_tac >>
  imp_res_tac new_block_props >> imp_res_tac emit_inst_extends >>
  `stmts_env cenv lctx ty ss1 s6 = (FST (stmts_env cenv lctx ty ss1 s6), s7) /\
   stmts_env cenv lctx ty ss2 s9 = (FST (stmts_env cenv lctx ty ss2 s9), s10)` by
    (fs[compile_stmts_env] >>
     Cases_on `stmts_env cenv lctx ty ss1 s6` >>
     Cases_on `stmts_env cenv lctx ty ss2 s9` >> gvs[]) >>
  `cs_extends s6 s7 /\ s6.cs_next_var <= s7.cs_next_var /\
   cs_extends s9 s10 /\ s9.cs_next_var <= s10.cs_next_var` by
    (fs[cs_mono_def] >> metis_tac[]) >>
  `!sx sy. (if block_is_terminated sx then sy = sx
            else emit_inst JMP [Label exit_lbl] [] sx = ((), sy)) ==>
           cs_extends sx sy /\ sx.cs_next_var = sy.cs_next_var` by
    (rw[] >> imp_res_tac emit_inst_extends >>
     metis_tac[cs_extends_refl, cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends s7 s8 /\ s7.cs_next_var = s8.cs_next_var /\
   cs_extends s10 s11 /\ s10.cs_next_var = s11.cs_next_var` by metis_tac[] >>
  `cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s8 s9` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `cs_extends s11 sb /\ s11.cs_next_var = sb.cs_next_var` by
    (Cases_on `block_is_terminated s7 /\ block_is_terminated s10`
     >- (fs[] >> simp[cs_extends_refl]) >>
     `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
     metis_tac[cs_extends_new_block, new_block_props]) >>
  `cs_extends sa s4 /\ cs_extends sa s6 /\ cs_extends s6 s9 /\
   cs_extends s7 s9 /\ cs_extends s9 sb /\ cs_extends s10 sb /\
   cs_extends s7 sb /\ cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s6 s7 func /\ fn_has_code s9 s10 func /\
   fn_has_code s7 s9 func /\ fn_has_code s10 sb func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_refl,
              cs_extends_trans] >>
  `lookup_block s5.cs_current_bb func.fn_blocks =
     SOME <| bb_label := s5.cs_current_bb;
             bb_instructions := s5.cs_current_insts |>` by
    metis_tac[fn_has_code_new_block] >>
  qexistsl_tac [`cond_op`, `s1`, `s4`, `s5`, `s6`, `s7`, `s8`, `s9`,
                `s10`, `s11`, `then_lbl`, `else_lbl`, `exit_lbl`, `x5`, `x8`] >>
  simp[] >> metis_tac[cs_extends_trans]
QED
