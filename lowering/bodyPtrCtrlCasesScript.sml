(*
 * The pointer twin of bodySimMain's induction: the cases for the control statements and statement lists.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_pass_case_ptr
 *   body_continue_case_ptr
 *   body_break_case_ptr
 *   body_if_case_ptr
 *   body_for_case_ptr
 *   body_expr_stmt_case_ptr
 *   body_stmts_nil_case_ptr
 *   body_stmts_cons_case_ptr
 *)
Theory bodyPtrCtrlCases
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list
  bodySimStmtCases bodyExprPreFacts supportedStmts supportedExprs
  stmtLoweringMono vyperTypeSystem vyperTypeCallStackSoundness
  stmtFragPtr gasSummaryComposePtr fragGasPathPtr gasSummary gasContext gasCount
  stmtSimDefs stmtSimProps loweringPosts stmtLowering compileEnv emitHelper
  emitHelperProps exprLoweringProps fragExec ptrSafeRun ptrDiscipline
  codegenRel contextCodegenRel venomInst venomState venomExecSemantics
  venomExecProofs stmtIfPtr exprSimSource supportedExprTraverse
  supportedStmtTraverse

val _ = Parse.hide "body";

Theorem frame_ret_ok_ptr_same_frame[local]:
  same_frame cenv c /\ frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
  frame_ret_ok_ptr d ctx PG func cx RetQ c ret_ty
Proof
  rw[frame_ret_ok_ptr_def] >> first_x_assum irule >> simp[] >>
  metis_tac[same_frame_trans]
QED

(* ===== Zero-cost paths ===== *)

(* The raw jump a break or continue emits: a pointer-checked edge that
   keeps the ghost. *)
Theorem emit_jump_zero_path_ptr:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_safe_step D 0 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem stmt_state_rel_clear_obs[local]:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := []) s
Proof
  strip_tac >> drule msg_gas_state_frame >>
  disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`]
    mp_tac) >>
  simp[stmt_state_rel_inst_idx]
QED

(* A break or continue: no gas read, the jump, and the post. *)
fun loop_jump_tac exc lbl =
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_ignore_bind_def,
       comp_bind_def, compile_stmt_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  pure_rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR ^exc`, `es`, `G0`, `tn0`,
                `OK (jump_to ^lbl s0)`] >>
  simp[Once evaluate_def, raise_def, gas_explicit_def,
       fragExecTheory.exit_result_def] >>
  (conj_tac
   >- (irule emit_jump_zero_path_ptr >> simp[] >>
       qexistsl_tac [`sa`, `sj`] >> simp[])) >>
  qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to,
       jump_to_def, lookup_var_def, stmt_state_rel_clear_obs,
       ghost_inv_gas_obs, ghost_inv_jump_to];

Theorem loop_jump_ptr[local]:
  stmt_env cenv (InLoop ex inc) ty st sa = (cenv', sb) /\
  (st = Break \/ st = Continue) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr D tops (ctx, func) PG (eval_stmt cx st)
    (es, s0, G0, tn0)
    (\res ee G tn t. ?cenv''.
      stmt_lands (InLoop ex inc) sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      ghost_inv d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x)))
    R
Proof
  strip_tac >> gvs[] >|
  [loop_jump_tac ``BreakException`` ``ex:string``,
   loop_jump_tac ``ContinueException`` ``inc:string``]
QED


Theorem body_stmts_nil_case_ptr:
  !cx. body_stmts_ptr_ok cx []
Proof
  rw[body_stmts_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff, stmt_frag_ptr_def, stmts_env_def,
     comp_return_def] >>
  pure_rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL ()`, `es`, `G0`, `tn0`, `OK s0`] >>
  simp[Once evaluate_def, return_def, gas_explicit_def, gas_path_ptr_rules,
       fragExecTheory.exit_result_def, stmt_lands_def, cenv_top_ext_refl,
       stmt_state_rel_clear_obs, ghost_inv_gas_obs]
QED

Theorem body_pass_case_ptr:
  !cx. body_stmt_ptr_ok cx Pass
Proof
  rpt gen_tac >>
  `eval_stmt cx Pass = eval_stmts cx []` by
    simp[FUN_EQ_THM, evaluate_def, return_def] >>
  `!cenv lctx ty. stmt_env cenv lctx ty Pass = stmts_env cenv lctx ty []` by
    simp[FUN_EQ_THM, stmt_env_def, stmts_env_def, declare_stmt_local_def,
         comp_bind_def, comp_ignore_bind_def, compile_stmt_def,
         comp_return_def] >>
  mp_tac (Q.SPEC `cx` body_stmts_nil_case_ptr) >>
  simp[body_stmt_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff, body_stmts_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff] >>
  rpt strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  first_x_assum irule >>
  simp[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
       supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  metis_tac[]
QED

Theorem body_continue_case_ptr:
  !cx. body_stmt_ptr_ok cx Continue
Proof
  rw[body_stmt_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff, stmt_frag_ptr_def] >>
  Cases_on `lctx`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `es.gas_obs` mp_tac) >>
      simp[Once evaluate_def, raise_def, stmt_res_ok_def]) >>
  rename1 `stmt_env cenv (InLoop ex inc) ret_ty _ sa = (cenv', sb)` >>
  irule gas_outcome_ptr_conseq >>
  irule_at Any loop_jump_ptr >>
  qexistsl_tac [`ret_ty`, `sb`, `sa`, `inc`, `ex`, `d`, `cenv`, `cenv'`,
                `\a b c e. F`] >>
  simp[]
QED

Theorem body_break_case_ptr:
  !cx. body_stmt_ptr_ok cx Break
Proof
  rw[body_stmt_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff, stmt_frag_ptr_def] >>
  Cases_on `lctx`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `es.gas_obs` mp_tac) >>
      simp[Once evaluate_def, raise_def, stmt_res_ok_def]) >>
  rename1 `stmt_env cenv (InLoop ex inc) ret_ty _ sa = (cenv', sb)` >>
  irule gas_outcome_ptr_conseq >>
  irule_at Any loop_jump_ptr >>
  qexistsl_tac [`ret_ty`, `sb`, `sa`, `inc`, `ex`, `d`, `cenv`, `cenv'`,
                `\a b c e. F`] >>
  simp[]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_if_case_ptr:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ptr_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ptr_ok cx ss2) /\ body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (If e ss1 ss2)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff] >>
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  `supported_expr tops e` by fs[supportedExprsTheory.supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
      is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >> simp[] >>
     qexists_tac `int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `!ty. expr_sim_ptr d ctx PG func cenv cx ty e es /\
        expr_vv_sim_ptr d ctx PG func cenv cx ty e es` by
    (gen_tac >>
     qpat_x_assum `body_expr_ptr_ok _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_ptr_ok_def]) >>
     disch_then irule >> metis_tac[]) >>
  irule compile_if_stmt_frag_ptr >> simp[stmts_env_cs_mono] >>
  conj_tac >- metis_tac[compile_expr_grows] >>
  rpt strip_tac >>
  rename1 `_ = (INL (BoolV b), es1)` >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `?tv s1. eval_expr cx e (es with gas_obs := gs) = (INL tv, s1)` by
    (qpat_x_assum `_ = (INL (BoolV b), es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_stmts_ptr_ok cx ss1 /\ body_stmts_ptr_ok cx ss2` by
    (`push_scope es1 = (INL (), es1 with scopes updated_by CONS FEMPTY)` by
       simp[push_scope_def, return_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es1` by
    (metis_tac[exprSimSourceTheory.expr_body_pre_eval]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  rpt (qpat_x_assum `body_stmts_ptr_ok _ _`
         (strip_assume_tac o REWRITE_RULE [body_stmts_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff])) >>
  Cases_on `b` >> fs[] >> first_x_assum irule >>
  gvs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def,
      allocLimitsTheory.alloc_limits_stmt_def, compileVyperTheory.stmt_valued_return_def, GSYM optionTheory.IS_SOME_EXISTS] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_for_case_ptr:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ptr_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ptr_ok cx it) ==>
    body_stmt_ptr_ok cx (For id typ it n body)
Proof
  cheat
QED

Theorem body_expr_stmt_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Expr e)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff] >>
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     irule stmt_expr_body_pre >> fs[body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_ptr_ok _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_ptr_ok_def]) >>
     disch_then (qspecl_then [`d`, `PG`, `tops`, `ctx`, `func`, `cenv`,
                              `env`, `expr_type e`, `es`] mp_tac) >>
     simp[]) >>
  irule compile_expr_stmt_frag_ok_ptr >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  metis_tac[compile_expr_open]
QED


Theorem body_stmts_cons_case_ptr:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ptr_ok cx ss) /\
    body_stmt_ptr_ok cx s ==>
    body_stmts_ptr_ok cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmts_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, AllCaseEqs(), int_calls_stmt_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  irule stmt_frag_cons_env_ptr >>
  simp[cj 1 compile_stmt_cs_mono, stmts_env_cs_mono] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `body_stmt_ptr_ok _ _`
        (irule o REWRITE_RULE [body_stmt_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff]) >>
      metis_tac[call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  rename1 `stmt_env cenv lctx ret_ty s sa = (c, sm)` >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `stmt_exprs_ok c = stmt_exprs_ok cenv` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env1 es1` by
    (irule expr_sim_inv_stmt >> fs[body_inv_def] >>
     metis_tac[exprSimHypsDefsTheory.expr_sim_inv_gas_obs, call_evaluation_safe_append_left]) >>
  `ce_locals_declared c env1` by metis_tac[ce_locals_declared_stmt] >>
  `locals_alloc_ok c env1` by metis_tac[locals_alloc_ok_stmt] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `frame_ret_ok_ptr d ctx PG func cx RetQ c ret_ty` by
    metis_tac[frame_ret_ok_ptr_same_frame] >>
  qpat_x_assum `!s'' t. _ ==> body_stmts_ptr_ok _ _` drule >>
  simp[body_stmts_ptr_ok_def, body_stmt_safe_def, body_stmts_safe_iff] >> disch_then irule >>
  metis_tac[call_evaluation_safe_append_right]
QED
