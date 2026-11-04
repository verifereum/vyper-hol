(* Pure source forcing and compiler decomposition for conditional statements. *)
Theory stmtSimIfProps
Ancestors
  stmtSimDefs stmtSimProps exprSimDefs loweringPosts list rich_list finite_map pred_set
  fragExec localPtrsProps loweringSlice
  stmtLowering exprLowering compileEnv emitHelper emitHelperProps exprLoweringProps
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
