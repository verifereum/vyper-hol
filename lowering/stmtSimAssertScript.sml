(* Actual-source counted conditional statement simulation. *)
Theory stmtSimAssert
Ancestors
  stmtSimDefs stmtSimProps stmtSimIfProps exprSimDefs exprSimProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

Theorem compile_assert_frag:
  !ctx func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >> (
    qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
    simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
    Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
    rename1 `_ = (op, s1)` >> simp[] >>
    Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok, s2)` >> simp[] >>
    Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl, s3)` >>
    simp[] >>
    Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
    rename1 `_ = (u4, s4)` >> simp[] >>
    Cases_on `new_block fl s4` >> rename1 `_ = (x5, s5)` >> simp[] >>
    qmatch_goalsub_abbrev_tac `emit_inst opc ops [] s5` >>
    Cases_on `emit_inst opc ops [] s5` >> rename1 `_ = (u6, s6)` >> simp[] >>
    Cases_on `new_block ok s6` >> rename1 `new_block ok s6 = (x7, s7)` >>
    simp[] >> strip_tac >> gvs[] >>
    imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
    imp_res_tac emit_inst_extends >>
    `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
     cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\
     cs_extends s6 s7` by
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
    drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
    disch_then (qspec_then `lctx` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    rename1 `(do raw <- eval_expr cx e; read_result cx raw od) es = (r1,es1)` >>
    qspecl_then [`ctx`, `func`, `cx`, `cenv`, `e`, `es`, `r1`, `es1`, `sa`,
                 `op`, `s1`, `s3`, `s4`, `ok`, `fl`, `s0`] mp_tac cond_jump_frag >>
    impl_tac >- fs[] >> strip_tac
    >- (
      Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def]
      >- (
        (* the condition holds: the ok block, where the code ends *)
        disj1_tac >> rename1 `stmt_state_rel ctx func cenv cx es' sv` >>
        qexists_tac `jump_to s7.cs_current_bb sv` >>
        gvs[stmt_lands_def, stmt_state_rel_jump_to, cenv_top_ext_refl,
            block_is_terminated_def] >>
        simp[jump_to_def, lookup_var_def] >> fs[lookup_var_def, jump_to_def]) >>
      (* it fails: the fail block aborts *)
      disj2_tac >> rename1 `stmt_state_rel ctx func cenv cx es' sv` >>
      qmatch_goalsub_abbrev_tac `stmt_exit RetQ es' rres _` >>
      qspecl_then [`ctx`, `func`, `opc`, `ops`, `s5`, `s6`,
                   `jump_to s5.cs_current_bb sv`, `RetQ`, `es'`, `rres`]
        mp_tac emit_abort_exit >>
      impl_tac
      >- (fs[markerTheory.Abbrev_def, jump_to_def] >> gvs[expr_exit_def] >>
          metis_tac[step_revert_zero, step_invalid]) >>
      strip_tac >>
      qpat_x_assum
        `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >>
      impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
      qexists_tac `fuel'` >> gvs[]) >>
    (* the condition's error *)
    disj2_tac >> qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >>
    disj1_tac >>
    metis_tac[expr_exit_INR_type])
QED
