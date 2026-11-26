(* Counted transitions for a forced Boolean operand and the chain exit. *)
Theory boolChainCountedControl
Ancestors
  exprSimDefs exprSimSource exprSimWordArgs exprSimSliceCompose exprSimMemDefs
  exprSimIfExp
  boolChainWordPost boolChainSource boolChainCodeLayout gasOutcomeSourceCong stmtSimProps
  placeTypedCopyPath fragGasSeqAbort exprSimUint2Str emitHelperProps
  fragGasMode fragGasPath gasSummary gasOutcome vyperStorageTrace
  vyperStorageFootprint vyperTyping vyperTypeValues valueEncoding vyperAST vyperValue
  loweringSlice exprLowering
  vyperInterpreter vyperState compileEnv loweringPosts venomInst venomState

(* A Boolean head gives one counted run. The consumer is called only on
   its normal outcome, at horizons valid for that run's source endpoint. *)
Theorem bool_chain_operand_bind:
  expr_sim ctx func ce cx (BaseT BoolT) e es /\
  expr_body_pre ce cx env e es /\ expr_type e = BaseT BoolT /\
  lower_value compile_expr ce (BaseT BoolT) e sa = (op,sc) /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es s /\ storage_well_formed_on cx es (FST H)) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks b mid u.
     gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
       (es,s) marks (INL (BoolV b)) mid (OK u) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
     u.vs_inst_idx = LENGTH sc.cs_current_insts /\
     eval_operand op u = SOME (val_to_w256 (BoolV b)) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace /\
          expr_post H ctx func ce cx e es sa sc s (mid with gas_obs := [])
            (BoolV b) op u) ==>
     gas_outcome F (cx_tops cx) (ctx,func) cx st0 (next (BoolV b))
       (mid with gas_obs := [],u) Q (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (next : value -> evaluation_state -> value evaluation_result)) (es,s)
    Q (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  drule expr_sim_apply >> disch_then drule_all >> strip_tac >>
  irule slice_gas_outcome_bind_value >> simp[] >>
  qexistsl_tac
    [`\H v ee t. expr_post H ctx func ce cx e es sa sc s ee v op t /\
        t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts`] >>
  reverse conj_tac
  >- (irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_INL]) >>
  rpt strip_tac >> rename1 `gas_marked_exec _ _ _ _ marks (INL v) mid (OK u)` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?b. v = BoolV b` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (qspec_then `[]` mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[] >> strip_tac >>
     `expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s.vs_gas_readings)`
       by simp[] >>
     `is_word_type (expr_type e)` by simp[is_word_type_def] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value) >>
     simp[evaluate_type_def, value_has_type_BoolTV]) >>
  gvs[] >>
  `~u.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >> drule_all gas_marked_exec_valid_prefix >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `eval_operand op u = SOME (val_to_w256 (BoolV b))` by
    (drule expr_post_word_operand >> simp[is_word_type_def, evaluate_type_def, word_value_def]) >>
  qpat_assum `!marks b mid u. _` (qspecl_then [`marks`,`b`,`mid`,`u`] mp_tac) >> simp[]
QED

(* The shared ASSIGN/JMP suffix is a zero-mark run of [return] on the
   source side. Only the origin's freshness is used for the final post. *)
Theorem bool_chain_return_exit:
  emit_inst ASSIGN [src] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\
  eval_operand src u = SOME (val_to_w256 (BoolV b)) /\
  local_ptrs_reserved ce sa0 /\ ~not_fresh_at sa0 rv /\
  is_word_type (expr_type out) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func ce cx out es0 sa0 sx s0 (ee with gas_obs := [])
         (BoolV b) op u) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (return (BoolV b)) (ee,u)
    (\H res ef z. ?b. res = INL (BoolV b) /\
       expr_post H ctx func ce cx out es0 sa0 sx s0 ef (BoolV b) (Var rv) z /\
       z.vs_current_bb = xl /\ z.vs_inst_idx = 0) R
Proof
  strip_tac >>
  qabbrev_tac `m = update_var rv (val_to_w256 (BoolV b)) u` >>
  qabbrev_tac `z = jump_to xl m` >>
  `gas_marked_path F ctx func u 0 (OK z)` by
    (simp[gas_marked_path_def] >>
     drule_all exprSimIfExpTheory.ifexp_root_suffix_path >>
     simp[Abbr `z`, Abbr `m`, jump_to_def]) >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL (BoolV b)`, `ee`, `OK z`] >>
  simp[gas_marked_exec_def, return_def] >> rpt strip_tac >>
  `z = jump_to xl (m with vs_inst_idx := 0)` by simp[Abbr `z`,jump_to_def] >>
  `z.vs_current_bb = xl /\ z.vs_inst_idx = 0` by simp[Abbr `z`,jump_to_def] >>
  simp[] >>
  qpat_x_assum `z = _` SUBST1_TAC >>
  simp[Abbr `m`, fragExecTheory.exit_result_def] >> rpt strip_tac >>
  irule word_post_fresh_assign_exit >> simp[word_value_def] >>
  conj_tac >- (qexists_tac `src` >> simp[]) >>
  qexistsl_tac [`out`,`op`,`sx`] >> simp[]
QED

(* For the recognized shape, the short arm is just a return. *)
Theorem bool_chain_step_action:
  expr_body_pre ce cx env
    (IfExp (BaseT BoolT) c (if d then x else Literal (BaseT BoolT) (BoolL T))
                           (if d then Literal (BaseT BoolT) (BoolL F) else x)) es ==>
  !gs. bind (eval_expr cx
    (IfExp (BaseT BoolT) c (if d then x else Literal (BaseT BoolT) (BoolL T))
                           (if d then Literal (BaseT BoolT) (BoolL F) else x)))
      (read_result cx) (es with gas_obs := gs) =
    bind (bind (eval_expr cx c) (read_result cx))
      (\v. if v = BoolV d then bind (eval_expr cx x) (read_result cx)
           else if v = BoolV (~d) then return v
           else raise (Error (TypeError "not BoolV"))) (es with gas_obs := gs)
Proof
  strip_tac >> drule bool_chain_forced_select >> disch_then (simp o single) >>
  gen_tac >> Cases_on `d` >>
  simp[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def,
       read_result_def, bind_return] >>
  `!(v:value). (if v = BoolV T then return (BoolV T)
                else if v = BoolV F then bind (eval_expr cx x) (read_result cx)
                else raise (Error (TypeError "not BoolV"))) =
               (if v = BoolV F then bind (eval_expr cx x) (read_result cx)
                else if v = BoolV T then return (BoolV T)
                else raise (Error (TypeError "not BoolV")))` by
    (gen_tac >> Cases_on `v = BoolV T` >> simp[]) >>
  simp[]
QED

(* A branch changes just the PC, so the existing Boolean value post survives. *)
Theorem bool_chain_word_post_jump:
  expr_type e = BaseT BoolT /\ expr_post H ctx func ce cx e es sa sb s0 ee (BoolV b) op u ==>
  expr_post H ctx func ce cx e es sa sc s0 ee (BoolV b) op (jump_to lbl u)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `eval_operand op u = SOME (val_to_w256 (BoolV b))` by
    (drule expr_post_word_operand >> simp[evaluate_type_def, word_value_def]) >>
  `eval_operand op (jump_to lbl u) = eval_operand op u` by
    (Cases_on `op` >> simp[NoAsms, eval_operand_def, lookup_var_def, jump_to_def]) >>
  `wb_frame ce es ee sa s0 u` by metis_tac[expr_post_frame] >>
  `wb_frame ce es ee sa s0 (jump_to lbl u)` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sa`,`u`] >>
     simp[jump_to_def, lookup_var_def]) >>
  `pure_frame ce func es sa s0 (jump_to lbl u) <=> pure_frame ce func es sa s0 u` by
    (irule pure_frame_state_cong >> simp[jump_to_def]) >>
  irule expr_post_word_intro >>
  fs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_jump_to, word_value_def,
     is_word_type_def] >> metis_tac[]
QED

Theorem bool_chain_singleton_outcome:
  expr_sim ctx func ce cx (BaseT BoolT) e es /\
  expr_body_pre ce cx env e es /\ expr_type e = BaseT BoolT /\
  compile_bool_chain_ops compile_expr ce d rv xl [e] sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es s /\ storage_well_formed_on cx es (FST H)) /\
  local_ptrs_reserved ce sa0 /\ ~not_fresh_at sa0 rv /\ is_word_type (expr_type out) /\
  (!H sc ee b op u. valid_horizon cx st0 H es.storage_trace /\
       expr_post H ctx func ce cx e es sa sc s ee (BoolV b) op u ==>
       expr_post H ctx func ce cx out es0 sa0 sx s0 ee (BoolV b) op u) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s)
    (\H res ef z. ?b. res = INL (BoolV b) /\
       expr_post H ctx func ce cx out es0 sa0 sx s0 ef (BoolV b) (Var rv) z /\
       z.vs_current_bb = xl /\ z.vs_inst_idx = 0)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  drule boolChainCodeLayoutTheory.bool_chain_singleton_layout >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule gas_outcome_source_cong >>
  qexists_tac `bind (bind (eval_expr cx e) (read_result cx)) return` >>
  conj_tac
  >- (gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
      rename1 `bind (eval_expr cx e) (read_result cx) _ = (rr,ss)` >>
      Cases_on `rr` >> simp[bind_def, return_def]) >>
  irule bool_chain_operand_bind >> simp[storage_trace_frame_return] >>
  qexistsl_tac [`ce`,`env`,`op`,`sa`,`sc`] >> simp[] >>
  rpt strip_tac >> irule bool_chain_return_exit >> simp[] >>
  reverse conj_tac >- (qexistsl_tac [`sc`,`op`,`sd`,`sb`] >> simp[]) >>
  qexists_tac `op` >> metis_tac[]
QED

(* The next budget unit either peels a recognized test or leaves a singleton. *)
Theorem bool_chain_residual_cases:
  expr_type x = BaseT BoolT ==>
  bool_chain_operands d (SUC k) x = [x] \/
  ?c tail.
    x = IfExp (BaseT BoolT) c (if d then tail else Literal (BaseT BoolT) (BoolL T))
                             (if d then Literal (BaseT BoolT) (BoolL F) else tail) /\
    bool_chain_operands d (SUC k) x = c :: bool_chain_operands d k tail
Proof
  Cases_on `x` >> Cases_on `d` >> simp[Once bool_chain_operands_def, expr_type_def] >>
  rpt strip_tac >> gvs[] >> rpt IF_CASES_TAC >> gvs[Once bool_chain_operands_def]
QED
