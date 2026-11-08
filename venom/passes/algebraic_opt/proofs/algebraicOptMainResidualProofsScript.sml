Theory algebraicOptMainResidualProofs
Ancestors
  algebraicOptMainCallProofs algebraicOptMainControlProofs
  algebraicOptRelationProofs algebraicOptDefs algebraicOptShapeProofs
  venomExecSemantics venomState venomInst venomWf stateEquiv stateEquivProps list

Theorem ao_main_equal_write:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  ao_main_observations fn V (update_var x w s) (update_var x w r) /\
  (update_var x w s with
    <|vs_vars := (update_var x w r).vs_vars;
      vs_inst_idx := r.vs_inst_idx|>) = update_var x w r
Proof
  strip_tac >> conj_tac
  >- (irule ao_main_observations_update >> simp[]) >>
  gvs[update_var_def, venom_state_component_equality]
QED

Theorem ao_main_parameter_base:
  inst_wf inst /\
  MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; GETFMP; INITIAL_FMP] /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  ao_resolve_iszero_inst targets inst = inst /\
  ((?e. step_inst_base inst s = Error e) \/
   ?t u. step_inst_base inst s = OK t /\ step_inst_base inst r = OK u /\
     ao_main_observations fn V t u /\
     (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
     t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx)
Proof
  strip_tac >>
  `s.vs_fmp = r.vs_fmp /\ s.vs_initial_fmp = r.vs_initial_fmp /\
   s.vs_params = r.vs_params /\ s.vs_return_pc_token = r.vs_return_pc_token` by
    gvs[venom_state_component_equality] >>
  gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `ao_resolve_iszero_inst targets inst = inst` by
    simp[ao_resolve_iszero_inst_def, ao_resolve_iszero_op_def,
         instruction_component_equality] >>
  simp[step_inst_base_opcode_eqs] >>
  rpt IF_CASES_TAC >> simp[] >>
  irule ao_main_equal_write >> simp[]
QED
