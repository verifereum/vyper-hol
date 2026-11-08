Theory dftGasInvCallPartner
Ancestors
  dftGasOracleDefs dftGasInvCallFrame dftGasInvOracleExchange dftRunRel dftBlockSim
  venomInstProofs1 venomWf
  venomExecSemantics venomEffects venomInst venomState list pred_set

Definition inv_partner_inputs_def:
  inv_partner_inputs inst s u <=>
    (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op u) /\
    s.vs_prev_bb = u.vs_prev_bb /\ s.vs_params = u.vs_params /\
    s.vs_call_ctx = u.vs_call_ctx /\ s.vs_tx_ctx = u.vs_tx_ctx /\
    s.vs_block_ctx = u.vs_block_ctx /\ s.vs_data_section = u.vs_data_section /\
    s.vs_code = u.vs_code /\ s.vs_prev_hashes = u.vs_prev_hashes /\
    s.vs_labels = u.vs_labels /\ s.vs_initial_fmp = u.vs_initial_fmp /\
    s.vs_return_pc_token = u.vs_return_pc_token
End

Theorem inv_partner_inputs_sym:
  inv_partner_inputs inst s u <=> inv_partner_inputs inst u s
Proof
  rewrite_tac[inv_partner_inputs_def] >> metis_tac[]
QED

Theorem inv_call_partner_class:
  dft_gas_swap_pair c i /\ c.inst_opcode = INVOKE ==>
  i.inst_opcode <> INVOKE /\
  ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
  ~is_ext_call_op i.inst_opcode /\ ~is_pseudo i.inst_opcode /\
  read_effects i.inst_opcode = {} /\ write_effects i.inst_opcode = {}
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  gvs[dft_gas_swap_pair_def, effects_independent_def,
      read_effects_def, write_effects_def, all_effects_def, empty_effects_def,
      is_terminator_def, is_alloca_op_def, is_ext_call_op_def, is_pseudo_def,
      DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED

Theorem inv_ev_call_structural:
  ev_step orc p d fuel ctx inst s = OK t /\ inst.inst_opcode = INVOKE ==>
  t.vs_prev_bb = s.vs_prev_bb /\ t.vs_params = s.vs_params /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_data_section = s.vs_data_section /\
  t.vs_code = s.vs_code /\ t.vs_prev_hashes = s.vs_prev_hashes /\
  t.vs_labels = s.vs_labels /\ t.vs_initial_fmp = s.vs_initial_fmp /\
  t.vs_return_pc_token = s.vs_return_pc_token
Proof
  strip_tac >> gvs[ev_step_def, AllCaseEqs(), bind_outputs_def] >>
  simp[foldl_update_var_preserves, update_var_def] >>
  Cases_on `ret.iret_adopt_fmp` >>
  gvs[merge_callee_state_def, adopt_return_fmp_def]
QED

Theorem inv_partner_portable_updates:
  dft_gas_swap_pair c i /\ c.inst_opcode = INVOKE /\ inst_wf i /\
  inv_partner_inputs i s u /\ ev_step orc p d fuel ctx i s = OK t ==>
  ?pairs. MAP FST pairs = i.inst_outputs /\
    t = FOLDL (\st (out,w). update_var out w st) s pairs /\
    ev_step orc p d fuel ctx i u =
      OK (FOLDL (\st (out,w). update_var out w st) u pairs)
Proof
  strip_tac >> drule_all inv_call_partner_class >> strip_tac >>
  Cases_on `i.inst_opcode = GAS`
  >- (drule_all inv_ev_gas_shape >> strip_tac >> gvs[] >>
      qexists_tac `[(out,orc (p,d,i.inst_id))]` >> simp[]) >>
  gvs[ev_step_def] >>
  Cases_on `i.inst_opcode` >> (
  gvs[read_effects_def, write_effects_def, empty_effects_def, all_effects_def,
      is_terminator_def, is_alloca_op_def, is_pseudo_def, is_ext_call_op_def,
      EXTENSION] >>
  qpat_x_assum `step_inst_base i s = OK t` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, AllCaseEqs()] >> strip_tac >>
  gvs[inv_partner_inputs_def, MEM] >>
  FIRST [
    qmatch_goalsub_abbrev_tac `update_var out2 value2 (update_var out1 value1 s)` >>
      qexists_tac `[(out1,value1); (out2,value2)]` >> simp[],
    qmatch_goalsub_abbrev_tac `update_var out value s` >>
      qexists_tac `[(out,value)]` >> simp[] >>
      gvs[Abbr `value`] >> metis_tac[], 
    qexists_tac `[]` >> gvs[inst_wf_def] >> metis_tac[]])
QED

Theorem inv_bind_outputs_observation:
  (!k w st. MEM k outs ==> obs (update_var k w st) = obs st) /\
  bind_outputs outs vals s = SOME t ==> obs t = obs s
Proof
  map_every qid_spec_tac [`t`, `s`, `vals`, `outs`] >>
  Induct >> Cases_on `vals` >> simp[bind_outputs_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `t` mp_tac) >>
  simp[bind_outputs_def] >> metis_tac[]
QED

Theorem inv_bind_outputs_lookup_outside:
  ~MEM v outs /\ bind_outputs outs vals s = SOME t ==>
  lookup_var v t = lookup_var v s
Proof
  strip_tac >> irule inv_bind_outputs_observation >>
  qexistsl_tac [`outs`, `vals`] >> simp[] >>
  rpt strip_tac >> `k <> v` by metis_tac[] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem inv_ev_call_lookup_outside:
  ev_step orc p d fuel ctx inst s = OK t /\ inst.inst_opcode = INVOKE /\
  ~MEM v inst.inst_outputs ==>
  lookup_var v t = lookup_var v s
Proof
  strip_tac >> gvs[ev_step_def, AllCaseEqs()] >>
  drule_all inv_bind_outputs_lookup_outside >> strip_tac >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, lookup_var_def, merge_callee_state_def]
QED

Theorem inv_call_partner_inputs:
  dft_gas_swap_pair c i /\ c.inst_opcode = INVOKE /\
  ev_step orc p d fuel ctx c s = OK sc ==>
  inv_partner_inputs i s sc
Proof
  strip_tac >> drule_all inv_ev_call_structural >> strip_tac >>
  simp[inv_partner_inputs_def] >> rpt strip_tac >>
  Cases_on `op` >> simp[eval_operand_def] >>
  rename1 `MEM (Var v) i.inst_operands` >>
  `~MEM v c.inst_outputs` by
    (gvs[dft_gas_swap_pair_def, inst_defs_def, inst_uses_def,
         DISJOINT_DEF, EXTENSION] >>
     metis_tac[mem_var_operand_vars]) >>
  drule_all inv_ev_call_lookup_outside >> simp[]
QED
