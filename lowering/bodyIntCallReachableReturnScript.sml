(* Reachable return consumers: the expression producer remains a premise. *)
Theory bodyIntCallReachableReturn
Ancestors
  bodyIntCallReturnCopy stmtSimForced gasSummaryCompose gasOutcome
  fragGasSeq fragGasMode fragGasPath gasCount gasSummary gasExemptCert
  vyperInterpreter exprSimDefs stmtSimDefs stmtSimReturn
  valueCopy intCallReturnMem intCallResult loweringPosts fragExec exprLoweringProps emitHelperProps
  stmtLowering exprLowering emitHelper compileEnv instIdxIndep venomInst venomState
  venomExecSemantics context valueEncoding vyperState vyperTyping finite_map
  list rich_list arithmetic
Libs
  monadsyntax

Theorem exit_fragment_path_post:
  frag_exec ctx sa sb P (\s. F) R /\
  fn_has_code sa sb func /\ P s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_path ctx func s n r /\ exit_result r ==>
  R r
Proof
  strip_tac >>
  drule_all gas_path_exit >> strip_tac >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frag_exec_def] >> disch_then drule_all >>
  simp[] >> strip_tac >>
  rename1 `R (run_from j ctx func s)` >>
  `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
  `!e. run_from j ctx func s <> Error e` by
    metis_tac[exit_result_not_error] >>
  `run_from (MAX fuel j) ctx func s = r` by
    (irule gas_run_from_fuel_mono >> simp[] >>
     qexists_tac `fuel` >> simp[]) >>
  `run_from (MAX fuel j) ctx func s = run_from j ctx func s` by
    (irule gas_run_from_fuel_mono >> simp[] >>
     qexists_tac `j` >> simp[]) >>
  metis_tac[]
QED

Theorem run_inst_seq_ret_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK u /\
  u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
  get_instruction bb (s.vs_inst_idx + LENGTH code) =
    SOME (mk_inst iid RET [rpc] []) /\
  (?pc. eval_operand rpc u = SOME pc) ==>
  gas_path ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
       (u with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  strip_tac >>
  drule_all tuple_run_inst_seq_gas_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_goalsub_abbrev_tac `IntRet ir land` >>
  `gas_path ctx func land 0 (IntRet ir land)` by
    (irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
     simp[gas_path_edge_def, Abbr `land`] >>
     qexistsl_tac [`0`, `mk_inst iid RET [rpc] []`] >>
     simp[gas_count_step_def] >>
     conj_tac >- metis_tac[ADD_COMM] >> disj2_tac >>
     simp[step_inst_non_invoke, mk_inst_def] >>
     simp[step_inst_base_def, eval_operands_def,
          eval_op_inst_idx, Abbr `ir`, exit_result_def]) >>
  drule gas_path_then >> disch_then drule >> simp[Abbr `land`]
QED

Theorem store_memory_ret_path:
  compile_store_memory ce src dst ty ty sa = ((),sm) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
  (?pc. eval_operand rpc s = SOME pc) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r
Proof
  strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  drule_all store_result_operand_frame >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  qpat_assum `fn_has_code sa sm func`
    (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id RET [rpc] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  qspecl_then [`sm`, `sb`, `func`, `[mk_inst sm.cs_next_id RET [rpc] []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb (s.vs_inst_idx + LENGTH (emitted_insts sa sm)) =
     SOME (mk_inst sm.cs_next_id RET [rpc] [])` by
    (gvs[same_blocks_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule_at Any (GEN_ALL run_inst_seq_ret_path) >>
  simp[exit_result_def] >>
  goal_assum (drule_at Any) >>
  gvs[venom_state_component_equality] >>
  qexistsl_tac [`rpc`, `pc`, `sm.cs_next_id`] >> simp[]
QED

Theorem internal_memory_return_path:
  compile_internal_return ce (SOME src) rpc 0 ty ty elems (SOME dst) sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
  (?pc. eval_operand rpc s = SOME pc) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r
Proof
  strip_tac >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_store_memory ce src dst ty ty sa` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  `cs_extends sa sm` by
    (qpat_x_assum `expr_val_rel _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
     first_x_assum drule >> strip_tac >>
     drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  irule store_memory_ret_path >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem internal_memory_return_counted:
  compile_internal_return ce (SOME src) rpc 0 ty ty elems (SOME dst) sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx (es with scopes := []) s /\
  expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
  (?pc. eval_operand rpc s = SOME pc) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    intret_mem_q func ce cx tv bw v (es with scopes := []) r
Proof
  strip_tac >>
  `?n r. gas_path ctx func s n r /\ exit_result r` by
    (irule internal_memory_return_path >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`n`, `r`] >> simp[] >>
  drule_all compile_internal_return_memory_size_bound_frag >>
  disch_then (mp_tac o SPEC_ALL) >>
  strip_tac >>
  drule exit_fragment_path_post >>
  simp[] >> disch_then irule >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* A counted suffix may have generated GAS reads: its marks need not be empty. *)
Theorem forced_counted_then_outcome:
  gas_outcome F tops (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. expr_exit res r) /\
  (!v ee t. P v ee t ==>
    gas_summary (ctx,func) (k v) (ee,t) Q R) /\
  (!ex ee r. expr_exit (INR ex : value + exception) r ==> R (INR ex) ee r) ==>
  gas_outcome F tops (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac
  >- (`gas_summary (ctx,func)
        (bind (eval_expr cx e) (read_result cx)) (es,s0)
        (\res ee t. ?v. res = INL v /\ P v ee t)
        (\res ee r. expr_exit res r)` by
        (irule gas_summary_at_summary >> goal_assum (drule_at Any)) >>
      `gas_summary (ctx,func)
        (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R` by
        (irule gas_summary_bind >> irule gas_summary_conseq >>
         qexistsl_tac [`\res ee t. ?v. res = INL v /\ P v ee t`,
                       `\res ee r. expr_exit res r`] >>
         simp[] >> conj_tac
         >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >> metis_tac[]) >>
         metis_tac[]) >>
      fs[gas_summary_def, gas_summary_at_def, gas_marked_exec_def,
         gas_marked_path_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[ignore_bind_def]
QED

Theorem reachable_memory_return:
  expr_type e = ty /\
  compile_internal_return ce (SOME src) rpc 0 ty ty elems (SOME dst) sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. expr_exit res r) /\
  (!v ee t. P v ee t ==>
    value_has_type tv v /\ val_wf tv v /\
    stmt_state_rel ctx func ce cx (ee with scopes := []) t /\
    expr_val_rel cx ty v src t /\ eval_operand dst t = SOME bw /\
    (?pc. eval_operand rpc t = SOME pc) /\ ~t.vs_halted /\
    t.vs_current_bb = sa.cs_current_bb /\
    t.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (ce.ce_is_ctor ==> !name itv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv))) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_stmt cx (Return (SOME e))) (es,s0)
    (\res ee t. F)
    (\res ee r. stmt_exit (\v ee r. intret_mem_q func ce cx tv bw v ee r) ee res r)
Proof
  strip_tac >>
  simp[Once evaluate_def, GSYM bind_assoc] >>
  simp[SF ETA_ss] >> irule forced_counted_then_outcome >>
  conj_tac
  >- (rpt gen_tac >> simp[stmt_exit_def] >> strip_tac >> disj1_tac >>
      Cases_on `r` >> Cases_on `ex` >> gvs[expr_exit_def] >>
      rename1 `expr_exit (INR (Error err)) _` >>
      Cases_on `err` >> gvs[expr_exit_def]) >>
  qexists_tac `P` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `?n r. gas_path ctx func t n r /\ exit_result r /\
    intret_mem_q func ce cx tv bw v (ee with scopes := []) r` by
    (irule internal_memory_return_counted >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule gas_summary_no_source_read >>
  qexistsl_tac [`ee`, `n`, `r`, `INR (ReturnException v)`] >>
  simp[raise_def, stmt_exit_def] >> disj2_tac >>
  qpat_x_assum `intret_mem_q _ _ _ _ _ _ _ _` mp_tac >>
  `ee with <|scopes := []; gas_obs := []|> =
     (ee with scopes := []) with gas_obs := []` by
    simp[evaluation_state_component_equality] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  simp[intret_mem_q_gas_obs]
QED
