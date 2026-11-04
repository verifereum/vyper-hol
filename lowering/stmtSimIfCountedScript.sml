(* Actual-source counted conditional statement simulation. *)
Theory stmtSimIfCounted
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

Theorem compile_if_stmt_frag:
  !ctx func cx lctx RetQ cenv ty c ss1 ss2 es.
    expr_type c = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!gs b es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL (BoolV b), es1) ==>
       stmt_frag ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      (eval_stmt cx (If c ss1 ss2)) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c ss1 ss2) sa` >>
  rename1 `_ = (u, sm)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule compile_if_parts_all >> strip_tac >>
  (* the code *)
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
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by metis_tac[] >>
  `cs_extends s7 s8 /\ s7.cs_next_var = s8.cs_next_var /\
   cs_extends s10 s11 /\ s10.cs_next_var = s11.cs_next_var` by metis_tac[] >>
  `cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s8 s9` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `cs_extends s11 sb` by
    (Cases_on `block_is_terminated s7 /\ block_is_terminated s10`
     >- (fs[] >> simp[cs_extends_refl]) >>
     `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
     metis_tac[cs_extends_new_block]) >>
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
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var` by
    (fs[] >> decide_tac) >>
  (* the source *)
  qpat_x_assum `eval_stmt _ _ _ = _`
    (strip_assume_tac o MATCH_MP eval_stmt_if_all)
  >- (
    (* the condition's error *)
    fs[] >>
    `expr_res_ok r1` by
      (gvs[] >>
       qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
       simp[bind_def] >> Cases_on `eval_expr cx c es` >>
       rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
       imp_res_tac read_result_no_control >>
       imp_res_tac (cj 1 eval_expr_no_control) >>
       gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
    qspecl_then [`ctx`, `func`, `cx`, `cenv`, `c`, `es`, `r1`, `es1`, `sa`,
                 `cond_op`, `s1`, `s4`, `s5`, `then_lbl`, `else_lbl`, `s0`]
      mp_tac cond_jump_frag >>
    impl_tac >- fs[] >> strip_tac >> fs[] >>
    disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >> disj1_tac >>
    metis_tac[expr_exit_INR_type])
  >- gvs[stmt_res_ok_def] >>
  (* the branch the condition selects *)
  fs[] >>
  qspecl_then [`ctx`, `func`, `cx`, `cenv`, `c`, `es`,
               `INL (BoolV b)`, `es1`, `sa`, `cond_op`, `s1`, `s4`,
               `s5`, `then_lbl`, `else_lbl`, `s0`] mp_tac cond_jump_frag >>
  impl_tac >- fs[expr_res_ok_def] >>
  strip_tac >> fs[] >>
  rename1 `stmt_state_rel ctx func cenv cx es1 sv` >>
  rename1 `jump_to (if bj then then_lbl else else_lbl) sv` >>
  `!st l. sa.cs_next_var <= st.cs_next_var ==>
          ret_pc_ok cenv st (jump_to l sv)` by
    (rpt strip_tac >> REWRITE_TAC [ret_pc_ok_jump_to] >>
     qspecl_then [`cenv`, `cenv`, `sa`, `st`, `s0`, `sv`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `sa.cs_next_var <= s6.cs_next_var /\ sa.cs_next_var <= s9.cs_next_var` by
    decide_tac >>
  Cases_on `b` >> fs[] >|
  [qpat_x_assum `bj` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [EQT_INTRO th])) >>
   qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ty`, `ss1`,
                `es1 with scopes := FEMPTY::es1.scopes`, `res`, `es2`, `sc`,
                `rest`, `s6`, `s7`, `s8`, `s9`, `else_lbl`, `x8`, `exit_lbl`,
                `sb`, `jump_to then_lbl sv`] mp_tac if_branch_frag,
   qpat_x_assum `~bj` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [EQF_INTRO th])) >>
   qspecl_then [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `ty`, `ss2`,
                `es1 with scopes := FEMPTY::es1.scopes`, `res`, `es2`, `sc`,
                `rest`, `s9`, `s10`, `s11`, `sb`, `exit_lbl`,
                `s11.cs_current_bb`, `exit_lbl`, `sb`, `jump_to else_lbl sv`]
     mp_tac if_branch_frag] >>
  (* the two branches go the same way from here *)
  (impl_tac
    >- (rpt conj_tac >>
        fs[stmt_state_rel_jump_to, stmt_state_rel_push_scope, jump_to_def]
        >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[]) >>
        strip_tac >>
        qpat_x_assum `_ \/ _ ==> ?x11. _` mp_tac >> fs[] >> strip_tac >>
        imp_res_tac new_block_props >> fs[]) >>
    strip_tac
    >- (
      disj1_tac >>
      rename1 `stmt_state_rel ctx func cenv cx (es2 with scopes := rest) sz` >>
      qexistsl_tac [`sz`, `cenv`] >> fs[cenv_top_ext_refl] >> rpt conj_tac
      >- (strip_tac >> fs[] >>
          `?x11. new_block exit_lbl s11 = (x11, sb)` by metis_tac[] >>
          imp_res_tac new_block_props >> fs[block_is_terminated_def])
      >- (rpt strip_tac >>
          `lookup_var x sv = SOME w` by res_tac >>
          qpat_x_assum
            `!x w. not_fresh_at _ x /\ lookup_var x (jump_to _ sv) = SOME w ==> _`
            irule >>
          fs[lookup_var_def, jump_to_def] >>
          irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> fs[])
      >- (rpt strip_tac >> res_tac >>
          qpat_x_assum
            `!aid b. FLOOKUP (jump_to _ sv).vs_allocas aid = SOME b ==> _` irule >>
          fs[jump_to_def]) >>
      rpt strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func sz <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >> impl_tac >- fs[] >> strip_tac >>
      qpat_x_assum
        `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >>
      impl_tac >- metis_tac[] >> metis_tac[]) >>
    disj2_tac >>
    qpat_x_assum
      `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
      (qspec_then `fuel` mp_tac) >>
    impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
    qexists_tac `fuel'` >> gvs[])
QED
