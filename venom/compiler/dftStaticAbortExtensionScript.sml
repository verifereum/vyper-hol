Theory dftStaticAbortExtension
Ancestors
  dftGasInvResidualTrace dftGasInvFlexibleTrace dftGasInvOracleFrame
  dftGasInvCrossingProbe dftGasInvSSAProbe passSharedFrame
  venomExecSemantics venomInst venomState dftRunRel dftGasOracleDefs
  dftScheduleOrder unitShapeDefs option list

Theorem inv_static_step_no_writes:
  s.vs_call_ctx.cc_static /\ ev_step orc p d fuel ctx inst s = OK u ==>
  ~MEM inst.inst_opcode [SSTORE; TSTORE; LOG]
Proof
  strip_tac >> Cases_on `inst.inst_opcode = LOG`
  >- (gvs[Once ev_step_def, Once step_inst_def] >>
      metis_tac[log_ok_not_static]) >>
  strip_tac >>
  gvs[Once ev_step_def, Once step_inst_def] >>
  gvs[Once step_inst_base_def, AllCaseEqs(), exec_write2_def,
      eval_operands_def]
QED

Theorem inv_static_ftrace_no_writes:
  !xs s t. s.vs_call_ctx.cc_static /\ inv_ev_ftrace orc p d ctx xs s t ==>
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) xs
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt gen_tac >> strip_tac >>
  `~MEM h.inst_opcode [SSTORE; TSTORE; LOG]` by
    metis_tac[inv_static_step_no_writes] >>
  `u.vs_call_ctx = s.vs_call_ctx` by metis_tac[inv_ev_step_call_ctx] >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`, `t`] mp_tac) >>
  gvs[]
QED

Theorem inv_remaining_trace_prefix_no_static_writes:
  !pre s.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ rest ++ y::post) s /\
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) pre /\
  inv_memory_observation y.inst_opcode /\
  EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
    ~dft_must_order x y) pre ==>
  ?t. inv_ev_trace orc p d fuel ctx pre s t /\
    dft_remaining_inv fn bb (rest ++ y::post) t /\
    (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s)
Proof
  Induct >> simp[inv_ev_trace_def] >> rpt strip_tac >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> CODECOPY` by
    metis_tac[inv_invoke_cannot_cross_memory, inv_codecopy_cannot_cross_memory,
              inv_crossing_candidate_necessary] >>
  `MEM h bb.bb_instructions /\ ~is_pseudo h.inst_opcode` by
    fs[dft_remaining_inv_def] >>
  `inst_wf h` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `!op. MEM op h.inst_operands ==> ?v. eval_operand op s = SOME v` by
    metis_tac[inv_remaining_head_operands, IS_SOME_EXISTS] >>
  `?u. ev_step orc p d fuel ctx h s = OK u` by
    (`opcode_fail_class h.inst_opcode = NoFail /\
      ~dft_swap_runtime_error_opcode h.inst_opcode` by
       (drule inv_crossing_candidate_necessary >> strip_tac >>
        drule_all inv_fallible_crossing_classification >> simp[]) >>
     Cases_on `h.inst_opcode = ALLOCA`
     >- metis_tac[inv_oracle_alloca_total] >>
     irule inv_oracle_nofail_total >> simp[]) >>
  `dft_remaining_inv fn bb (pre ++ rest ++ y::post)
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (SRULE [] (Q.INST [`pre` |-> `[]`] inv_remaining_ev_step)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[] >>
  metis_tac[inv_crossing_operand_frame]
QED

Theorem inv_remaining_trace_extension_no_static_writes:
  !pre s.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) pre /\
  inv_memory_observation y.inst_opcode /\
  EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
    ~dft_must_order x y) pre ==>
  ?t. inv_ev_trace orc p d fuel ctx pre s t /\
    dft_remaining_inv fn bb (y::post) t /\
    (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s)
Proof
  rpt strip_tac >>
  irule (SRULE [] (Q.INST [`rest` |-> `[]`]
    inv_remaining_trace_prefix_no_static_writes)) >>
  goal_assum (drule_at Any) >> gvs[]
QED
