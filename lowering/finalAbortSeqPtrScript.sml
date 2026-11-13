Theory finalAbortSeqPtr
Ancestors fragGasSeqAbort fragGasSeqPtr fragGasPathPtr fragExec instIdxIndep gasCount
  exprLoweringProps venomInstProofs venomExecSemantics venomState venomInst
  ptrSafeRun list rich_list arithmetic

Theorem step_inst_base_abort_cursor:
  step_inst_base i s = Abort a t ==>
  ?k. step_inst_base i (s with vs_inst_idx := n) = Abort a (t with vs_inst_idx := k)
Proof
  strip_tac >> Cases_on `is_terminator i.inst_opcode`
  >- (drule terminator_step_inst_base_idx_norm0 >>
      disch_then (qspecl_then [`s`, `n`] mp_tac) >>
      Cases_on `step_inst_base i (s with vs_inst_idx := n)` >>
      simp[exec_result_map_def] >> strip_tac >>
      rename1 `v with vs_inst_idx := 0 = t with vs_inst_idx := 0` >>
      qexists `v.vs_inst_idx` >>
      fs[venom_state_component_equality]) >>
  qexists `n` >> simp[step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem run_inst_seq_final_abort_cursor:
  !xs s u i a t n.
    EVERY (\h. ~is_terminator h.inst_opcode) xs /\
    run_inst_seq xs s = OK u /\ run_inst_seq (xs ++ [i]) s = Abort a t ==>
    ?k. run_inst_seq (xs ++ [i]) (s with vs_inst_idx := n) =
      Abort a (t with vs_inst_idx := k)
Proof
  Induct
  >- (rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
      Cases_on `step_inst_base i s` >> gvs[] >>
      drule step_inst_base_abort_cursor >>
      disch_then (qspec_then `n` strip_assume_tac) >>
      qexists `k` >> simp[]) >>
  rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem run_inst_seq_final_abort_gas_path_ptr:
  !xs i s u a t G tn Gf tnf ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (xs ++ [i]) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\h. h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode) xs /\
    i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    run_inst_seq xs s = OK u /\
    run_inst_seq (xs ++ [i]) s = Abort a t /\
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ [i]) s Gf tnf ==>
    ?j. gas_path_ptr D lo ctx fn PG G tn s
      (LENGTH (FILTER (\h. h.inst_opcode = GAS) xs)) Gf tnf
      (Abort a (t with vs_inst_idx := j))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      rule_assum_tac (PURE_REWRITE_RULE [APPEND]) >>
      drule instruction_prefix_cursor >> strip_tac >>
      Cases_on `step_inst_base i s` >>
      gvs[run_inst_seq_def, inst_seq_ptr_def] >>
      qexists `t.vs_inst_idx` >> simp[] >>
      irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
      rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
      qexists `0` >>
      simp[step_inst_non_invoke, gas_count_step_def, exit_result_def, ptr_safe_step_def]) >>
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [APPEND]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK v` >>
  `step_inst 0 ctx h s = OK v` by simp[step_inst_non_invoke] >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `EVERY (\h. ~is_terminator h.inst_opcode) xs` by fs[EVERY_MEM] >>
  `run_inst_seq xs (v with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_all run_inst_seq_final_abort_cursor >>
  disch_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac) >>
  first_x_assum (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  qexists `j` >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
  simp[] >> Cases_on `h.inst_opcode = GAS` >> simp[ADD1]
QED
