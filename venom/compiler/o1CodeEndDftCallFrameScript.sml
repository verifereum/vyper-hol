(* Successful crossed calls restore caller labels and preserve all variables
   except their declared outputs. No termination or success claim is made. *)
Theory o1CodeEndDftCallFrame
Ancestors
  dftGasInvCallPartner dftGasInvResidualTrace o1CodeEndDftBoundary
  dftScheduleOrder venomInst venomState pred_set dftAvailability

Theorem code_end_dft_call_operand_frame:
  ev_step orc p d fuel ctx x s = OK t /\
  x.inst_opcode = INVOKE /\ ~dft_must_order x obs ==>
  !op. MEM op obs.inst_operands ==>
    eval_operand op (t with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op s
Proof
  strip_tac >> drule_all inv_ev_call_structural >> strip_tac >>
  Cases >> simp[eval_operand_def] >> strip_tac
  >- (rename1 `MEM (Var name) obs.inst_operands` >>
      `~MEM name x.inst_outputs` by
        (fs[dft_must_order_def, inst_defs_def, inst_uses_def, DISJOINT_DEF,
            EXTENSION, MEM_operand_vars_eq_Var] >> metis_tac[]) >>
      drule_all inv_ev_call_lookup_outside >> simp[lookup_var_def]) >>
  simp[]
QED

Theorem code_end_dft_crossing_operand_frame:
  ev_step orc p d fuel ctx x s = OK t /\ inst_wf x /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  ~dft_must_order x obs ==>
  !op. MEM op obs.inst_operands ==>
    eval_operand op (t with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op s
Proof
  strip_tac >> Cases_on `x.inst_opcode = INVOKE`
  >- metis_tac[code_end_dft_call_operand_frame] >>
  metis_tac[inv_crossing_operand_frame]
QED

Theorem code_end_dft_replay_prefix_operands:
  !pre s t.
    EVERY (\x. inst_wf x /\ ~is_pseudo x.inst_opcode /\
      ~is_terminator x.inst_opcode /\ ~dft_must_order x obs) pre /\
    inv_ev_trace orc p d fuel ctx pre s t ==>
    !op. MEM op obs.inst_operands ==> eval_operand op t = eval_operand op s
Proof
  Induct >> simp[inv_ev_trace_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all code_end_dft_crossing_operand_frame >> metis_tac[]
QED
