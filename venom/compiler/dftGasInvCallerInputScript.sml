Theory dftGasInvCallerInput
Ancestors
  dftGasInvCallPartner dftGasInvInversion dftGasInvFlexibleTrace
  dftRunRel dftCommutation dftGasOracleDefs
  venomExecSemantics venomInst venomState list

Theorem inv_setup_callee_index:
  setup_callee callee args (s with vs_inst_idx := n) = setup_callee callee args s
Proof
  simp[setup_callee_def]
QED

Theorem inv_setup_callee_updates[local]:
  !pairs s. setup_callee callee args
    (FOLDL (\st (out,w). update_var out w st) s pairs) =
    setup_callee callee args s
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[setup_callee_update_var]
QED

Theorem inv_ev_invoke_partner_setup:
  dft_gas_swap_pair call x /\ call.inst_opcode = INVOKE /\ inst_wf x /\
  ev_step orc p d fuel ctx x s = OK t ==>
  !callee args n. setup_callee callee args (t with vs_inst_idx := n) =
    setup_callee callee args s
Proof
  strip_tac >>
  `inv_partner_inputs x s s` by simp[inv_partner_inputs_def] >>
  drule_all inv_partner_portable_updates >> strip_tac >>
  simp[inv_setup_callee_index, inv_setup_callee_updates]
QED

Theorem inv_ev_invoke_trace_setup:
  !xs s t. EVERY (\x. dft_gas_swap_pair call x /\ inst_wf x) xs /\
  call.inst_opcode = INVOKE /\ inv_ev_ftrace orc p d ctx xs s t ==>
  !callee args. setup_callee callee args t = setup_callee callee args s
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  drule_all inv_ev_invoke_partner_setup >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem inv_lookup_invoke_partner_setup:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  MEM call bb.bb_instructions /\ MEM x bb.bb_instructions /\
  call.inst_opcode = INVOKE /\ ~is_pseudo x.inst_opcode /\
  ((id_before (MAP (\i. i.inst_id) bb.bb_instructions) call.inst_id x.inst_id /\
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id call.inst_id) \/
   (id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id call.inst_id /\
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) call.inst_id x.inst_id)) /\
  ev_step orc p d fuel ctx x s = OK t ==>
  !callee args n. setup_callee callee args (t with vs_inst_idx := n) =
    setup_callee callee args s
Proof
  strip_tac >>
  `~is_pseudo call.inst_opcode` by simp[is_pseudo_def] >>
  irule inv_ev_invoke_partner_setup >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[inv_lookup_inversion_swap, dft_gas_swap_pair_sym]
QED
