(* Counted actual-source simulation for a word return. *)
Theory stmtSimReturnWord
Ancestors
  stmtSimReturn stmtSimProps stmtSimDefs exprSimProps exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode gasExemptCert
  list rich_list finite_map fragExec freshWrites vyperTypeABI
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding venomMemDefs
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl
  vyperStatePreservation venomExecSemantics venomInst venomState
Libs
  monadsyntax

Theorem return_word_consumer[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ret_tv /\
  ret_pc_ok cenv sa s0 /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
  ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst iid RET [op; Var rpc] []) ==>
  gas_marked_path F ctx func t 0
    (IntRet <|iret_values := [typed_val_to_w256 ret_tv v]; iret_adopt_fmp := NONE|> t) /\
  (!tail. stmt_exit (intret_q func cenv cx ret_tv)
    (ee with gas_obs := tail) (INR (ReturnException v))
    (IntRet <|iret_values := [typed_val_to_w256 ret_tv v]; iret_adopt_fmp := NONE|> t))
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  fs[expr_post_def, expr_val_rel_def] >>
  rename1 `eval_operand op t = SOME w` >>
  `w = typed_val_to_w256 ret_tv v` by metis_tac[] >>
  `?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[gas_marked_path_def] >> irule (cj 3 gas_path_rules) >>
      simp[exit_result_def] >>
      simp[gas_path_edge_def] >>
      qexists_tac `0` >>
      simp[gas_count_defs, venomInstTheory.mk_inst_def] >>
      disj2_tac >>
      `step_inst 0 ctx (mk_inst iid RET [op; Var rpc] []) t =
       IntRet <|iret_values := [w]; iret_adopt_fmp := NONE|> t` by
        simp[step_inst_non_invoke, venomInstTheory.mk_inst_def,
             step_inst_base_def, eval_operands_def, eval_operand_def] >>
      fs[venomInstTheory.mk_inst_def, exit_result_def]) >>
  `state_rel func cenv cx (ee with scopes := []) t` by
    (irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
  simp[stmt_exit_def, intret_q_gas_obs, intret_q_def, result_rel_def,
       expr_exit_def] >>
  gen_tac >> conj_tac
  >- (`ee with <|scopes := []; gas_obs := tail|> =
       (ee with scopes := []) with gas_obs := tail` by simp[] >>
      pop_assum SUBST1_TAC >> simp[state_rel_gas_obs]) >>
  irule intret_vals_match_word >> metis_tac[]
QED

Theorem return_word_summary[local]:
  gas_summary_at F (ctx,func) marks
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
      t.vs_current_bb = s1.cs_current_bb /\
      t.vs_inst_idx = LENGTH s1.cs_current_insts)
    (\res ee r. expr_exit res r) /\
  (!ee v t.
    expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
    ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
    ?r. gas_marked_path F ctx func t 0 r /\ exit_result r /\
      !tail. stmt_exit (intret_q func cenv cx ret_tv)
        (ee with gas_obs := tail) (INR (ReturnException v)) r) ==>
  gas_summary_at F (ctx,func) marks (eval_stmt cx (Return (SOME e))) (es,s0)
    Q (\res ee r. !tail. stmt_exit (intret_q func cenv cx ret_tv)
                                  (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- (gvs[] >>
      `~t.vs_halted` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >> metis_tac[gas_marked_path_exec, gas_path_normal]) >>
      first_x_assum drule_all >> strip_tac >>
      `gas_marked_exec F (ctx,func)
        (raise (ReturnException v) : evaluation_state -> unit evaluation_result)
        (es_end with gas_obs := [],t) [] (INR (ReturnException v)) es_end r` by
        simp[gas_marked_exec_def, raise_def] >>
      qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >>
      conj_tac
      >- (irule (SIMP_RULE std_ss [APPEND_NIL]
            (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
      disj2_tac >>
      qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
      simp[stmt_exit_def, expr_exit_def] >> strip_tac >> gen_tac >>
      `es_end with <|scopes := []; gas_obs := tail|> =
       (es_end with scopes := []) with gas_obs := tail` by simp[] >>
      pop_assum SUBST1_TAC >> simp[intret_q_gas_obs] >>
      qpat_x_assum `intret_q _ _ _ _ _ _ _` mp_tac >>
      `es_end with <|scopes := []; gas_obs := []|> =
       (es_end with scopes := []) with gas_obs := []` by simp[] >>
      pop_assum SUBST1_TAC >> simp[intret_q_gas_obs]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

(* return e in an internal function whose result, a word, goes back on the
   stack (ce_returns_count = 1, no return buffer): e's fragment, whose
   errors exit, then RET [e's operand; the return PC]. *)
Theorem compile_return_word_int_frag:
  !ctx func cx lctx cenv ty e es rpc rsz ret_tv.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
    expr_type e = ty /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ret_tv /\
    expr_sim ctx func cenv cx ty e es /\
    (!sa op sb. lower_value compile_expr cenv ty e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx (intret_q func cenv cx ret_tv) cenv
      (stmt_env cenv lctx ty (Return (SOME e)))
      (eval_stmt cx (Return (SOME e))) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       compile_internal_return_from_env_def, compile_internal_return_def,
       word_type_elem_types] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op, s1)` >>
  simp[] >>
  Cases_on `emit_inst RET [op; Var rpc] [] s1` >> rename1 `_ = (u, s2)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends sa s1` by metis_tac[] >>
  `cs_extends s1 s2` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_split] >>
  qspecl_then [`s1`, `s2`, `func`, `[mk_inst s1.cs_next_id RET [op; Var rpc] []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb (LENGTH s1.cs_current_insts) =
     SOME (mk_inst s1.cs_next_id RET [op; Var rpc] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule return_forced_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule return_word_summary >> qexistsl_tac [`op`, `s1`, `sa`] >>
      reverse conj_tac >- (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qexists_tac `IntRet <|iret_values := [typed_val_to_w256 ret_tv v];
                             iret_adopt_fmp := NONE|> t` >>
      `gas_marked_path F ctx func t 0
        (IntRet <|iret_values := [typed_val_to_w256 ret_tv v]; iret_adopt_fmp := NONE|> t) /\
       !tail. stmt_exit (intret_q func cenv cx ret_tv) (ee with gas_obs := tail)
         (INR (ReturnException v))
         (IntRet <|iret_values := [typed_val_to_w256 ret_tv v]; iret_adopt_fmp := NONE|> t)` by
        (irule return_word_consumer >> metis_tac[]) >>
      simp[exit_result_def]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule return_forced_exempt >> simp[]
QED

(* Integrity gate for the forced return boundary and RET consumer. *)
