(* Request-sensitive static DFT forward simulation on actual frames. *)
Theory dftStaticRequestSim
Ancestors
  dftStaticContextSim dftStaticSwap dftStaticSchedule dftStaticTransport dftStaticFuel
  dftGasRequestLift dftGasRequestFuel dftGasRequestSwap dftGasRequestPartner
  dftGasRequestRel dftGasOracleDefs dftRunRel dftScheduleOrder dftDefs
  o1PassContract unitShapeDefs venomExecSemantics venomState venomInst
  list finite_map

Theorem dft_ev_context_sim_rq_static:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\ dead_wf D /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\ s.vs_fmp = s.vs_initial_fmp /\
  code_layout_valid s /\
  (s.vs_call_ctx.cc_static ==>
    !fn inst l. MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
      l IN FDOM s.vs_labels) /\
  terminates (ev_context orc fuel C s) ==>
  dft_rq_res_rel D (ev_context orc fuel C s) (ev_context orc fuel C' s)
Proof
  rpt strip_tac >> simp[]
QED
