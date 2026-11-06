Theory makeSsaCurrentEndpointBatch
Ancestors
  makeSsaCurrentDominanceAvailability makeSsaCurrentPhiBatchRuntime
  makeSsaCurrentPrefixRuntime venomExecProofs venomWf venomExecSemantics
  venomState list option

Theorem current_endpoint_available_lookup[local]:
  wf_function f /\ MEM pred f.fn_blocks /\
  def_available_at f pred NONE x /\
  strict_dom_vars_defined f (st with vs_current_bb := pred.bb_label) /\
  (!i x. MEM i pred.bb_instructions /\ MEM x i.inst_outputs ==>
    IS_SOME (lookup_var x st)) ==> IS_SOME (lookup_var x st)
Proof
  rpt strip_tac >> fs[def_available_at_def] >>
  Cases_on `def_bb.bb_label = pred.bb_label`
  >- (`def_bb = pred` by metis_tac[same_label_same_block] >> gvs[] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`st` |-> `st with vs_current_bb := pred.bb_label`]
    current_strict_dom_producer_lookup)) >>
  simp[lookup_var_def] >> strip_tac >> simp[]
QED

Theorem current_endpoint_phi_read[local]:
  wf_function f /\ wf_ssa f /\ MEM pred f.fn_blocks /\
  MEM bb f.fn_blocks /\ MEM inst bb.bb_instructions /\ inst_wf inst /\
  inst.inst_opcode = PHI /\ fn_cfg_edge f pred.bb_label bb.bb_label /\
  st.vs_prev_bb = SOME pred.bb_label /\
  strict_dom_vars_defined f (st with vs_current_bb := pred.bb_label) /\
  (!i x. MEM i pred.bb_instructions /\ MEM x i.inst_outputs ==>
    IS_SOME (lookup_var x st)) ==> IS_SOME (eval_one_phi st inst)
Proof
  rpt strip_tac >>
  `phi_edge_uses_wf f bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  fs[phi_edge_uses_wf_def] >>
  `?v. MEM (pred.bb_label,v) (phi_pairs inst.inst_operands)` by
    (first_x_assum (qspec_then `pred.bb_label` mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `?pb. MEM pb f.fn_blocks /\ pb.bb_label = pred.bb_label /\
       def_available_at f pb NONE v` by metis_tac[] >>
  `pb = pred` by metis_tac[same_label_same_block] >> gvs[] >>
  `IS_SOME (lookup_var v st)` by
    (drule_all current_endpoint_available_lookup >> simp[]) >>
  `resolve_phi pb.bb_label inst.inst_operands = SOME (Var v)` by
    (irule current_prefix_resolve_phi_selected >> simp[]) >>
  fs[inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  simp[eval_one_phi_def, eval_operand_def] >>
  Cases_on `lookup_var v st` >> gvs[]
QED

Theorem current_endpoint_phi_batch_total:
  wf_function f /\ wf_ssa f /\ MEM pred f.fn_blocks /\ MEM bb f.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\ fn_cfg_edge f pred.bb_label bb.bb_label /\
  st.vs_prev_bb = SOME pred.bb_label /\
  strict_dom_vars_defined f (st with vs_current_bb := pred.bb_label) /\
  (!i x. MEM i pred.bb_instructions /\ MEM x i.inst_outputs ==>
    IS_SOME (lookup_var x st)) ==> ?post. eval_phis st bb.bb_instructions = OK post
Proof
  rpt strip_tac >> irule current_phi_batch_success_all >> rpt strip_tac >>
  irule current_endpoint_phi_read >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM] >> metis_tac[]
QED
