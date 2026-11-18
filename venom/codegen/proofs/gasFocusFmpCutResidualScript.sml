(* Residual certificates for observed C4 steps within lowered segments. *)
Theory gasFocusFmpCutResidual
Ancestors
  fmpStageCoverRun fmpStageCoverMem fmpStageRel lowerDloadPtrRawReachable
  oracleExecProps o1PassContract unitMemInv contextCodegenRel codegenRel
  venomInstProps venomExecSemantics venomState venomInst arithmetic list

Theorem focus_fmp_cut_inserted_residual:
  ALL_DISTINCT (fn_labels fn') /\
  lookup_function name C4.ctx_functions = SOME fn' /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  active_inst fn' ti t /\
  t.vs_current_bb = u.vs_current_bb /\ t.vs_inst_idx < u.vs_inst_idx /\
  (!k. fmp_target_run k C4 name t (u.vs_inst_idx - t.vs_inst_idx) u) /\
  (!i. t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
       i < LENGTH bb.bb_instructions /\
       fmp_inserted_op (EL i bb.bb_instructions).inst_opcode) ==>
  fmp_inserted_op ti.inst_opcode /\
  (!fuel z. step_inst fuel C4 ti t = OK z ==>
    let v = z with vs_inst_idx := SUC t.vs_inst_idx in
      v.vs_current_bb = u.vs_current_bb /\
      v.vs_inst_idx <= u.vs_inst_idx /\
      v.vs_gas_readings = t.vs_gas_readings /\
      (!k. fmp_target_run k C4 name v (u.vs_inst_idx - v.vs_inst_idx) u) /\
      (!i. v.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
           i < LENGTH bb.bb_instructions /\
           fmp_inserted_op (EL i bb.bb_instructions).inst_opcode))
Proof
  strip_tac >> drule_all active_inst_block_lookup >> strip_tac >> fs[] >>
  conj_asm1_tac
  >- (qpat_assum `!i. _ <= i /\ i < _ ==> _`
        (qspec_then `t.vs_inst_idx` mp_tac) >> gvs[get_instruction_def, AllCaseEqs()]) >>
  `~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\ ti.inst_opcode <> GAS` by
    gvs[fmp_inserted_op_def, is_terminator_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  drule_all step_inst_noninvoke_gas_readings >> strip_tac >>
  simp[] >>
  `u.vs_inst_idx - SUC t.vs_inst_idx = (u.vs_inst_idx - t.vs_inst_idx) - 1` by
    decide_tac >>
  pop_assum SUBST1_TAC >>
  irule fmp_cov_run_step >> simp[] >>
  qexistsl [`bb`, `fuel`, `ti`] >> gvs[] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. _ <= i /\ i < _ ==> _` (qspec_then `i` mp_tac) >>
  impl_tac >- decide_tac >>
  simp[NoAsms, fmp_inserted_op_def] >> strip_tac >> simp[is_terminator_def]
QED

Theorem focus_fmp_cut_tail_observation:
  ALL_DISTINCT (fn_labels fn') /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  active_inst fn' ti t /\ revert_forward_pair bb p j /\
  p < t.vs_inst_idx /\ t.vs_inst_idx <= j ==>
  lowered_mem_fact eom C4 fn' ti t /\
  ((t.vs_inst_idx = j /\ ti.inst_opcode = REVERT) \/
   (t.vs_inst_idx < j /\ ti.inst_opcode = ASSIGN)) /\
  (!fuel z. ~is_terminator ti.inst_opcode /\ step_inst fuel C4 ti t = OK z ==>
    let v = z with vs_inst_idx := SUC t.vs_inst_idx in
      lookup_block v.vs_current_bb fn'.fn_blocks = SOME bb /\
      revert_forward_pair bb p j /\ p < v.vs_inst_idx /\ v.vs_inst_idx <= j /\
      v.vs_gas_readings = t.vs_gas_readings)
Proof
  strip_tac >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (drule_all active_inst_block_lookup >> strip_tac >> gvs[]) >>
  Cases_on `t.vs_inst_idx = j`
  >- (`ti.inst_opcode = REVERT` by gvs[revert_forward_pair_def] >>
      simp[is_terminator_def, lowered_mem_fact_def, lowered_mem_ok_def] >>
      simp[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  `t.vs_inst_idx < j` by decide_tac >>
  `ti.inst_opcode = ASSIGN` by metis_tac[revert_forward_pair_def] >>
  simp[lowered_mem_fact_def, lowered_mem_ok_def, inst_mem_ranges_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       is_terminator_def] >>
  rpt gen_tac >> strip_tac >>
  `~is_terminator ti.inst_opcode` by simp[is_terminator_def] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `ti.inst_opcode <> INVOKE /\ ti.inst_opcode <> GAS` by simp[] >>
  drule_all step_inst_noninvoke_gas_readings >> simp[]
QED
