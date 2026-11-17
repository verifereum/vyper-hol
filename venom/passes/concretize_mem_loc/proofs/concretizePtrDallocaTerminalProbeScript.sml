Theory concretizePtrDallocaTerminalProbe
Ancestors
  ptrDiscipline venomExecSemantics venomState venomInst contextCodegenRel
  lowerDloadRevertSuffix o1LowerDloadRangeTransport pred_set words list

(* Terminal audit: non-INVOKE Halt is produced by STOP, RETURN, SINK and
   SELFDESTRUCT. STOP clears return data; SINK keeps it; SELFDESTRUCT fails
   in static frames and otherwise changes balances and clears return data.
   REVERT/INVALID produce Abort, RET/DRET produce IntRet. Calls/creates
   do not directly Halt. RETURN alone needs a relocated memory slice.

   A source final_taint witness additionally needs source frame_reachable,
   active_inst and a successful outgoing Halt. Continuing paired chronology
   supplies neither that Halt nor the relative-byte/reflection hypotheses
   below. Matching scalar sizes/defined operands come from value transport;
   relative clean bytes and taint reflection need the new memory invariant.
   The two offsets need not be equal. No new relation is defined here. *)
Theorem ptr_dalloca_return_mask:
  inst.inst_opcode = RETURN /\ inst.inst_operands = [a;n] /\
  it.inst_opcode = RETURN /\ it.inst_operands = [a_t;szop_t] /\
  eval_operand a s = SOME off /\ eval_operand n s = SOME sz /\
  eval_operand a_t t = SOME offt /\ eval_operand szop_t t = SOME sz /\
  (!i. i < w2n sz /\ w2n offt + i IN un.t_mem ==>
       w2n off + i IN tn.t_mem) /\
  (!i. i < w2n sz /\ w2n off + i NOTIN tn.t_mem ==>
       read_byte (w2n off + i) s.vs_memory =
       read_byte (w2n offt + i) t.vs_memory) /\
  step_inst fuel CS inst s = Halt sh /\
  step_inst fuelt CT it t = Halt th ==>
  ret_taint un it t SUBSET ret_taint tn inst s /\
  LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
  (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
       EL i sh.vs_returndata = EL i th.vs_returndata)
Proof
  strip_tac >>
  `sh = halt_state (set_returndata (read_memory (w2n off) (w2n sz) s) s)` by
    (qpat_x_assum `step_inst fuel CS inst s = _` mp_tac >>
     simp[Once step_inst_non_invoke, step_inst_base_def, read_memory_def]) >>
  `th = halt_state (set_returndata (read_memory (w2n offt) (w2n sz) t) t)` by
    (qpat_x_assum `step_inst fuelt CT it t = _` mp_tac >>
     simp[Once step_inst_non_invoke, step_inst_base_def, read_memory_def]) >>
  gvs[ret_taint_def, halt_state_def, set_returndata_def] >>
  conj_tac >- (simp[SUBSET_DEF] >> metis_tac[]) >>
  simp[ld_read_memory_length] >> rpt strip_tac >>
  simp[ld_read_memory_element]
QED

(* The existing ld_revert_pair_suffix_step is the stronger, endpoint-inclusive
   exclusion and should be used directly by consumers. Here the strict interior
   also identifies the instruction and preserves the precise control point. *)
Theorem ptr_dalloca_forward_terminal:
  revert_forward_pair bb i j /\ i < s.vs_inst_idx /\ s.vs_inst_idx < j /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  inst.inst_opcode = ASSIGN /\
  step_inst fuel ctx inst s <> Halt h /\
  step_inst fuel ctx inst s <> IntRet vals h /\
  (step_inst fuel ctx inst s = OK u ==>
    u.vs_requests = s.vs_requests /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx)
Proof
  strip_tac >>
  `inst.inst_opcode = ASSIGN` by metis_tac[revert_forward_pair_def] >>
  metis_tac[ld_revert_suffix_step]
QED
