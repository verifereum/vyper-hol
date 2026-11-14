(* INVOKE barriers exclude the static-write predecessors of memory reads. *)
Theory dftStaticInvokeTrace
Ancestors
  dftGasInvResidualTrace dftGasInvCrossingProbe dftGasInvSSAProbe
  dftGasInvOracleFrame dftGasOracleDefs dftRunRel dftScheduleOrder
  dftAvailability venomExecSemantics venomInst venomState list option

Theorem inv_remaining_trace_extension_invoke:
  !pre s.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\
  y.inst_opcode = INVOKE /\
  EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
    ~dft_must_order x y) pre ==>
  ?t. inv_ev_trace orc p d fuel ctx pre s t /\
    dft_remaining_inv fn bb (y::post) t /\
    (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s)
Proof
  Induct >> simp[inv_ev_trace_def] >>
  rpt strip_tac >>
  `inv_memory_observation y.inst_opcode` by simp[inv_memory_observation_def] >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> CODECOPY` by
    metis_tac[inv_invoke_cannot_cross_memory, inv_codecopy_cannot_cross_memory,
              inv_crossing_candidate_necessary] >>
  `MEM h bb.bb_instructions /\ ~is_pseudo h.inst_opcode` by
    fs[dft_remaining_inv_def] >>
  `inst_wf h` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `!op. MEM op h.inst_operands ==> ?v. eval_operand op s = SOME v` by
    metis_tac[inv_remaining_head_operands, IS_SOME_EXISTS] >>
  `?u. ev_step orc p d fuel ctx h s = OK u` by
    (Cases_on `h.inst_opcode = ALLOCA`
     >- metis_tac[inv_oracle_alloca_total] >>
     `inv_crossing_candidate h.inst_opcode y.inst_opcode (h.inst_outputs = [])` by
       metis_tac[inv_crossing_candidate_necessary] >>
     `~MEM h.inst_opcode [SSTORE; TSTORE; LOG]` by
       (strip_tac >> fs[] >>
        qpat_x_assum `inv_crossing_candidate _ _ _` mp_tac >>
        asm_rewrite_tac[] >> EVAL_TAC) >>
     `opcode_fail_class h.inst_opcode = NoFail /\
      ~dft_swap_runtime_error_opcode h.inst_opcode` by
       metis_tac[inv_fallible_crossing_classification] >>
     irule inv_oracle_nofail_total >> simp[]) >>
  `dft_remaining_inv fn bb (pre ++ y::post)
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (SRULE [] (Q.INST [`pre` |-> `[]`] inv_remaining_ev_step)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `u.vs_call_ctx = s.vs_call_ctx` by metis_tac[inv_ev_step_call_ctx] >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[] >>
  metis_tac[inv_crossing_operand_frame]
QED

