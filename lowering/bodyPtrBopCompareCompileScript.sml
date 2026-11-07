Theory bodyPtrBopCompareCompile
Ancestors
  bodyPtrBopCompare emitHelper emitHelperProps exprLoweringProps fragExec
  compileEnv arithmetic rich_list instIdxIndep venomInst venomState
  venomExecSemantics

Theorem bop_compare_emit_placement:
  emit_op opc ops sc = (op,sd) /\ fn_has_code sc sd fn /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sc.cs_next_id opc ops [STRING #"%" (toString sc.cs_next_var)])
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN]
QED

Theorem bop_eq_emit_ptr:
  emit_op EQ [left;right] sc = (op,sd) /\ fn_has_code sc sd fn /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  op_prov G' op = NONE /\ op_taint tn' op = {} /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  (!x. not_fresh_at sc x ==> FLOOKUP G' x = FLOOKUP G x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_compare_emit_placement >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst sc.cs_next_id EQ [left;right] [STRING #"%" (toString sc.cs_next_var)])`
    by simp[] >>
  drule_all bop_eq_counted_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> fs[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> `x <> STRING #"%" (toString sc.cs_next_var)` by
    gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem bop_iszero_emit_ptr:
  emit_op ISZERO [arg] sc = (op,sd) /\ fn_has_code sc sd fn /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  op_taint tn arg = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  op_prov G' op = NONE /\ op_taint tn' op = {} /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  (!x. not_fresh_at sc x ==> FLOOKUP G' x = FLOOKUP G x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_compare_emit_placement >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst sc.cs_next_id ISZERO [arg] [STRING #"%" (toString sc.cs_next_var)])`
    by simp[] >>
  drule_all bop_iszero_counted_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> fs[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> `x <> STRING #"%" (toString sc.cs_next_var)` by
    gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem bop_compare_emit_layout:
  emit_op opc ops sc = (op,sd) ==>
  inst_extends sc sd /\ cs_extends sc sd /\
  sd.cs_current_bb = sc.cs_current_bb /\
  LENGTH sd.cs_current_insts = LENGTH sc.cs_current_insts + 1
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED

Theorem bop_compare_emit_readonly:
  ((opc = EQ /\ ops = [left;right]) \/ (opc = ISZERO /\ ops = [left])) /\
  emit_op opc ops sc = (op,sd) /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  irule bop_compare_state_frame >> metis_tac[]
QED

Theorem bop_compare_emit_run_cursor:
  emit_op opc ops sc = (op,sd) /\ ~is_terminator opc /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  run_inst_seq (emitted_insts sc sd) (s with vs_inst_idx := idx) =
    OK (t with vs_inst_idx := idx)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sd)` by
    simp[venomInstTheory.mk_inst_def] >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`s`, `idx`] mp_tac) >>
  simp[exec_result_map_def]
QED

(* These scalar runs do not require whole-state freshness. *)
Theorem bop_eq_emit_run:
  emit_op EQ [left;right] sc = (op,sd) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  ?t. run_inst_seq (emitted_insts sc sd) s = OK t /\
      eval_operand op t = SOME (bool_to_word (a = b))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem bop_iszero_emit_run:
  emit_op ISZERO [arg] sc = (op,sd) /\ eval_operand arg s = SOME a ==>
  ?t. run_inst_seq (emitted_insts sc sd) s = OK t /\
      eval_operand op t = SOME (bool_to_word (a = 0w))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED
