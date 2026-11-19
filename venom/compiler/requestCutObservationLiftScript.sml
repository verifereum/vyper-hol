Theory requestCutObservationLift
Ancestors
  requestCutStaticObservation dftGasInvForwardActive dftGasToListReachBoundary
  dftGasOracleDefs dftRunRel dftDefs contextCodegenRel
  o1PassContract staticAbortDefs venomInst venomState list

(* When the C7 trace covers an observed visit, restoring its remaining
   gas produces exactly the native observation used by the C9 guards. *)
Theorem request_cut_native_observation_or_static_write:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  ev_reachable orc initial C8 p d fn8 inst
    (t with vs_gas_readings := initial.vs_gas_readings) /\
  inv_memory_observation inst.inst_opcode /\ inst.inst_opcode <> DRET /\
  ~in_revert_forward fn8 t /\
  (!fn7 u. ev_reachable orc initial C7 p d fn7 inst u ==>
    ?ws. raw_reachable v7 C7 fn7 inst (u with vs_gas_readings := ws)) ==>
  (?fn7 u ws. raw_reachable v7 C7 fn7 inst (u with vs_gas_readings := ws) /\
    ~in_revert_forward fn7 u /\
    fn8 = dft_fn fn7 /\ u.vs_current_bb = t.vs_current_bb /\
    ev_reachable orc initial C7 p d fn7 inst u) \/
  (in_static_abort_prefix fn8 t /\ ?fn7 op s.
    ev_reachable orc initial C7 p d fn7 op s /\
    MEM op.inst_opcode [SSTORE; TSTORE; LOG] /\ s.vs_call_ctx.cc_static /\
    IS_SOME (eval_operands op.inst_operands s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`t` |-> `t with vs_gas_readings := initial.vs_gas_readings`]
    request_cut_observation_or_static_write) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[eval_operand_def, in_static_abort_prefix_def, static_abort_at_def] >>
  disch_then (DISJ_CASES_THEN2
    (qx_choosel_then [`fn7`, `u`] strip_assume_tac)
    (fn th => disj2_tac >> ACCEPT_TAC th)) >>
  `MEM fn7 C7.ctx_functions` by metis_tac[ev_reachable_function_member] >>
  `dft_fn_rel fn7 (dft_fn fn7)` by
    (fs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  `active_inst fn7 inst u /\
   active_inst fn8 inst (t with vs_gas_readings := initial.vs_gas_readings)` by
    metis_tac[ev_reachable_cases] >>
  `~in_revert_forward fn7 u` by
    (strip_tac >>
     mp_tac (Q.INST [`C` |-> `C7`, `fn` |-> `fn7`, `a` |-> `u`,
       `b` |-> `t with vs_gas_readings := initial.vs_gas_readings`] inv_forward_active) >>
     gvs[in_revert_forward_def]) >>
  qpat_x_assum `!fn7 u. ev_reachable orc initial C7 p d fn7 inst u ==> _`
    (drule_then strip_assume_tac) >>
  disj1_tac >> qexistsl_tac [`fn7`, `u`, `ws`] >> simp[]
QED
