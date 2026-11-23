(*
 * Expression simulation: an and/or chain (BoolChain)
 *
 * The frontend wraps the nested conditional it builds for an and/or chain
 * of three or more operands in the identity builtin BoolChain, and the
 * lowering compiles the operands read back by bool_chain_operands with
 * compile_bool_chain_ops, as the pinned compiler's lower_BoolOp does: each
 * operand but the last tested in turn with a jump to a block that sets the
 * result and leaves, the last one's value the result.
 *
 * The case lemma takes the operands' judgments in the style of
 * compile_ifexp_case (exprSimOperators): each later operand's where the
 * earlier one evaluates, as the body predicates' conditional clause gives
 * them.
 *
 * TOP-LEVEL:
 *   bool_chain_case_def      - the operands' judgments, in order
 *   compile_bool_chain_case  - the chain's judgments from its operands'
 *)
Theory exprSimBoolChain
Ancestors
  exprSimIfExp exprSimOperators exprSimProps exprSimDefs exprSimHypsDefs
  exprLowering boolChainCountedControl boolChainCodeLayout boolChainWordPost
  boolChainOperandsCons
  gasOutcomeSourceCong exprSimSource exprSimHyps exprSimWordArgs loweringPosts
  vyperAST vyperState vyperValue vyperInterpreter vyperStorageTrace
  vyperStorageFootprint gasSummary stmtSimDeclCompose fragGasMode fragGasPath
  stmtSimProps emitHelperProps exprLoweringProps compileEnv venomState venomInst
  vyperTypeCallGraph finite_map loweringSlice valueEncoding boolChainSource
  boolChainWrapperRead exprSimMemDefs loweringShapeDefs

(* Each operand simulates, a later one where the one before evaluates. *)
Definition bool_chain_case_def:
  bool_chain_case nocalls ctx func cenv cx [] = T /\
  bool_chain_case nocalls ctx func cenv cx (e::es) =
    (expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e /\
     ((?s tv s'. eval_expr cx e s = (INL tv, s')) ==>
      bool_chain_case nocalls ctx func cenv cx es))
End

(* The endpoint is at the preallocated exit; the lift carries the frame
   relative to the original entry across the already executed tests. *)
Theorem bool_chain_ops_outcome:
  !k x es sa sb s.
    expr_body_pre ce cx env x es /\ expr_type x = BaseT BoolT /\
    (nocalls ==> int_calls_expr x = []) /\
    bool_chain_case nocalls ctx func ce cx (bool_chain_operands d k x) /\
    compile_bool_chain_ops compile_expr ce d rv xl (bool_chain_operands d k x) sa = ((),sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func ce cx es s /\ storage_well_formed_on cx es (FST H)) /\
    local_ptrs_reserved ce sa0 /\ ~not_fresh_at sa0 rv /\ expr_type out = BaseT BoolT /\
    (!H e sc ee b op u. valid_horizon cx st0 H es.storage_trace /\
         expr_type e = BaseT BoolT /\ (~expr_has_effect x ==> ~expr_has_effect e) /\
         expr_post H ctx func ce cx e es sa sc s ee (BoolV b) op u ==>
         expr_post H ctx func ce cx out es0 sa0 sx s0 ee (BoolV b) op u) ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (bind (eval_expr cx x) (read_result cx)) (es,s)
      (\H res ee z. ?b. res = INL (BoolV b) /\
         expr_post H ctx func ce cx out es0 sa0 sx s0 ee (BoolV b) (Var rv) z /\
         z.vs_current_bb = xl /\ z.vs_inst_idx = 0)
      (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  Induct_on `k`
  >- (simp[bool_chain_operands_def, bool_chain_case_def] >> rpt strip_tac >>
      suspend "last") >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `expr_type x = BaseT BoolT`
    (mp_then Any (qspecl_then [`k`,`d`] strip_assume_tac) bool_chain_residual_cases)
  >- (fs[bool_chain_case_def] >> suspend "last") >>
  suspend "test"
QED

Resume bool_chain_ops_outcome[last]:
  markerLib.RESUME_TAC >> irule bool_chain_singleton_outcome >> simp[is_word_type_def] >>
  (conj_tac >- (qexistsl_tac [`d`,`sa`,`sb`] >> simp[] >> metis_tac[])) >>
  (conj_tac >- (qexists_tac `env` >> simp[])) >>
  irule expr_sim_case_apply >> metis_tac[]
QED

Resume bool_chain_ops_outcome[test]:
  `?hd hs. bool_chain_operands d k tail = hd::hs` by
    simp[bool_chain_operands_cons] >>
  fs[bool_chain_case_def] >>
  drule bool_chain_test_layout >> strip_tac >>
  qpat_x_assum `!fn. fn_has_code sa sb fn ==> _` (qspec_then `func` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `x = IfExp _ _ _ _` SUBST_ALL_TAC >>
  drule expr_body_pre_ifexp >> strip_tac >>
  `expr_type tail = BaseT BoolT` by (Cases_on `d` >> fs[]) >>
  `(nocalls ==> int_calls_expr c = []) /\ (nocalls ==> int_calls_expr tail = [])` by
    (Cases_on `d` >> fs[int_calls_expr_def]) >>
  `expr_sim ctx func ce cx (BaseT BoolT) c es` by
    (irule expr_sim_case_apply >> metis_tac[]) >>
  qabbrev_tac `next = \v. if v = BoolV d then bind (eval_expr cx tail) (read_result cx)
                          else if v = BoolV (~d) then return v
                          else raise (Error (TypeError "not BoolV"))` >>
  irule gas_outcome_source_cong >>
  qexists_tac `bind (bind (eval_expr cx c) (read_result cx)) next` >>
  conj_tac >- (simp[Abbr `next`] >> drule bool_chain_step_action >> simp[]) >>
  irule bool_chain_operand_bind >> simp[] >>
  `!v. storage_trace_frame (next v)` by
    (gen_tac >> simp[Abbr `next`] >> rpt IF_CASES_TAC >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result, storage_trace_frame_return,
          storage_trace_frame_raise]) >>
  simp[] >> qexistsl_tac [`ce`,`env`,`op`,`sa`,`sc`] >> simp[] >>
  rpt strip_tac >>
  `eval_operand op u = SOME (if b then 1w else 0w)` by
    (Cases_on `b` >> fs[valueEncodingTheory.val_to_w256_def]) >>
  `gas_path ctx func u 0
     (OK (jump_to (if b then (if d then ln else ls) else (if d then ls else ln)) u))` by
    (irule assert_jnz_zero_path >> simp[] >> qexistsl_tac [`op`,`sj`,`sn`] >>
     qpat_assum `emit_inst JNZ _ _ _ = _` (mp_then Any mp_tac emit_inst_extends) >>
     simp[]) >>
  `gas_marked_path F ctx func u 0 (OK (jump_to (if b = d then ln else ls) u))` by
    (Cases_on `b` >> Cases_on `d` >> fs[gas_marked_path_def]) >>
  irule gas_outcome_zero_prefix >>
  qexists_tac `jump_to (if b = d then ln else ls) u` >> simp[] >>
  Cases_on `b = d`
  >- suspend "continue" >> suspend "short"
QED

Resume bool_chain_ops_outcome[continue]:
  simp[Abbr `next`] >>
  qabbrev_tac `obs = gas_explicit marks s.vs_gas_readings` >>
  `bind (eval_expr cx c) (read_result cx) (es with gas_obs := obs) =
     (INL (BoolV d),mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (qspec_then `[]` mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[Abbr `obs`]) >>
  `expr_body_pre ce cx env tail (mid with gas_obs := [])` by
    (`expr_body_pre ce cx env c (es with gas_obs := obs)` by simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >> strip_tac >>
     first_x_assum drule >> Cases_on `d` >> simp[]) >>
  `bool_chain_case nocalls ctx func ce cx (hd::hs)` by
    metis_tac[bool_chain_case_def, CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_read_INL] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `ci_mono sa st` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce st` by metis_tac[local_ptrs_reserved_next_var] >>
  `(jump_to ln u).vs_current_bb = ln /\ (jump_to ln u).vs_inst_idx = 0 /\
   ~(jump_to ln u).vs_halted` by simp[jump_to_def] >>
  first_x_assum irule >> simp[] >>
  (conj_tac >-
    (gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     qpat_assum `expr_post _ _ _ _ _ c _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def]) >>
     simp[stmt_state_rel_jump_to])) >>
  qexistsl_tac [`st`,`sb`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qabbrev_tac `parent = IfExp (BaseT BoolT) c
     (if d then tail else Literal (BaseT BoolT) (BoolL T))
     (if d then Literal (BaseT BoolT) (BoolL F) else tail)` >>
  `stmt_state_rel H ctx func ce cx es s` by metis_tac[] >>
  `eval_operand op' u' = SOME (val_to_w256 (BoolV b'))` by
    (qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac expr_post_word_operand) >>
     simp[is_word_type_def, evaluate_type_def, word_value_def]) >>
  `~expr_has_effect parent ==> ~expr_has_effect c /\ ~expr_has_effect e` by
    (Cases_on `d` >> fs[Abbr `parent`]) >>
  `expr_post H ctx func ce cx parent es sa st s ee (BoolV b') op' u'` by
    (irule word_post_selected_prefix >> simp[is_word_type_def, word_value_def] >>
     qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _`
       (irule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ (jump_to _ _) _ _ _ _`)) >>
     qpat_assum `expr_post _ _ _ _ _ c _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`parent`,`st`] >> simp[Abbr `parent`]
QED

Resume bool_chain_ops_outcome[short]:
  `b = ~d` by (Cases_on `b` >> Cases_on `d` >> fs[]) >>
  simp[Abbr `next`] >>
  `(jump_to ls u).vs_current_bb = ls /\ (jump_to ls u).vs_inst_idx = 0 /\
   ~(jump_to ls u).vs_halted` by simp[jump_to_def] >>
  irule bool_chain_return_exit >> simp[is_word_type_def] >>
  reverse conj_tac
  >- (qexistsl_tac [`ss`,`Lit (if d then 0w else 1w)`,`sd`,`se`] >>
      Cases_on `d` >> simp[eval_operand_def, valueEncodingTheory.val_to_w256_def]) >>
  qexists_tac `op` >> gen_tac >> strip_tac >>
  irule bool_chain_word_post_jump >> simp[] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qexists_tac `sx` >> first_x_assum irule >>
  simp[] >> qexistsl_tac [`c`,`sc`] >> simp[] >>
  qpat_assum `b = ~d` (once_rewrite_tac o single o GSYM) >> first_assum ACCEPT_TAC
QED

Finalise bool_chain_ops_outcome

(* The chain is the identity on its one argument, the nested conditional;
   its code tests the operands in turn (compile_bool_chain_ops), which
   computes the conditional's value: an and stops at the first false
   operand with false, an or at the first true one with true. *)

Theorem compile_bool_chain_case:
  !nocalls ctx func cenv cx ann is_and n e.
    bool_chain_case nocalls ctx func cenv cx
      (bool_chain_operands is_and (n - 1) e) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ann (BoolChain is_and n) [e]) /\
    expr_vv_case nocalls ctx func cenv cx
      (Builtin ann (BoolChain is_and n) [e])
Proof
  rpt gen_tac >> strip_tac >> conj_asm1_tac
  >- (
    simp[expr_sim_case_def, expr_sim_def, int_calls_expr_def] >> rpt strip_tac >>
    drule_then assume_tac bool_chain_wrapper_read_action >>
    drule_then strip_assume_tac bool_chain_wrapper_action >>
    qpat_x_assum `!gs. eval_expr _ (Builtin _ _ _) _ = _` kall_tac >> gvs[] >>
    Cases_on `compile_expr cenv ty (Builtin (BaseT BoolT) (BoolChain is_and n) [e]) sa` >>
    drule_then strip_assume_tac bool_chain_root_layout >>
    gvs[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
    rename1 `new_block _ sf = (_,sb)` >>
    `sa.cs_next_var <= sg.cs_next_var` by simp[] >>
    `local_ptrs_reserved cenv sg` by metis_tac[local_ptrs_reserved_next_var] >>
    `fn_has_code sg sf func` by metis_tac[] >>
    irule gas_outcome_source_cong >>
    qexists_tac `bind (eval_expr cx e) (read_result cx)` >> simp[] >>
    irule gas_outcome_post_mono >>
    qexists_tac `\H res ee z. ?b. res = INL (BoolV b) /\
       expr_post H ctx func cenv cx (Builtin (BaseT BoolT) (BoolChain is_and n) [e])
         es sa sb s0 ee (BoolV b) (Var rv) z /\
       z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = 0` >>
    conj_tac >- (simp[] >> rpt strip_tac >> qexists_tac `BoolV b` >> simp[]) >>
    irule bool_chain_ops_outcome >> simp[expr_type_def] >>
    (conj_tac >- (qexists_tac `env` >> simp[])) >>
    qexistsl_tac [`is_and`,`n - 1`,`nocalls`,`sg`,`sf`] >> simp[] >>
    rpt strip_tac >> match_mp_tac expr_post_word_intro >>
    simp[expr_type_def, is_word_type_def, word_value_def] >>
    `eval_operand op u = SOME (val_to_w256 (BoolV b))` by
      (drule expr_post_word_operand >> simp[is_word_type_def, evaluate_type_def, word_value_def]) >>
    fs[expr_post_def, wb_frame_def] >> rpt strip_tac
    >- (qpat_assum `!x w. not_fresh_at sg x /\ _ ==> _` irule >> simp[] >>
        irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
    >- (qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ u.vs_memory = _` irule >>
        simp[] >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `aid` >> simp[]) >>
    `~expr_has_effect e'` by fs[] >>
    qpat_x_assum `_ ==> pure_frame _ _ _ sg _ _` mp_tac >> simp[pure_frame_def]) >>
  irule expr_vv_case_stack >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule eval_expr_builtin_value >> simp[]) >>
  rpt gen_tac >> Cases_on `compile_expr cenv ty (Builtin ann (BoolChain is_and n) [e]) sa` >>
  drule_then strip_assume_tac bool_chain_root_layout >> simp[]
QED
