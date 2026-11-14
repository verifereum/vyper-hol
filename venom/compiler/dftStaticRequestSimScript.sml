(* Request-sensitive static DFT forward simulation on actual frames. *)
Theory dftStaticRequestSim
Ancestors
  dftStaticRequestFuel dftStaticContextSim dftStaticSwap dftStaticSchedule dftStaticTransport dftStaticFuel
  dftGasRequestLift dftGasRequestFuel dftGasRequestSwap dftGasRequestPartner
  dftGasRequestRel dftGasOracleDefs dftRunRel dftScheduleOrder dftDefs
  o1PassContract unitShapeDefs passSimulationDefs venomExecSemantics venomState venomInst
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
  strip_tac >>
  reverse (Cases_on `s.vs_call_ctx.cc_static`) >-
    (irule dft_ev_context_sim_rq >> simp[o1_run_state_ok_def]) >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `!f. (dft_fn f).fn_name = f.fn_name` by
    (gen_tac >> simp[dft_fn_def] >> pairarg_tac >> simp[]) >>
  qpat_x_assum `terminates _` mp_tac >> simp[ev_context_def] >>
  Cases_on `C.ctx_entry` >> simp[terminates_def] >>
  rename1 `lookup_function nm C.ctx_functions` >>
  Cases_on `lookup_function nm C.ctx_functions` >>
  simp[terminates_def, lookup_function_map] >>
  rename1 `lookup_function nm C.ctx_functions = SOME fn` >>
  strip_tac >> drule lookup_function_MEM >> strip_tac >>
  irule ev_function_frame_sim_rq_ready >> simp[terminates_def] >>
  qpat_x_assum `LIST_REL dft_fn_rel _ _` mp_tac >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[MEM_EL]
QED
