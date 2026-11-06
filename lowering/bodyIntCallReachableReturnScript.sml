(* Reachable return consumers: the expression producer remains a premise. *)
Theory bodyIntCallReachableReturn
Ancestors
  bodyIntCallReturnCopy stmtSimForced gasSummaryCompose gasOutcome
  fragGasSeq fragGasMode fragGasPath gasCount stmtSimDefs stmtSimReturn
  valueCopy intCallReturnMem intCallResult loweringPosts fragExec exprLoweringProps emitHelperProps
  stmtLowering exprLowering emitHelper compileEnv instIdxIndep venomInst venomState
  venomExecSemantics list rich_list arithmetic
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
