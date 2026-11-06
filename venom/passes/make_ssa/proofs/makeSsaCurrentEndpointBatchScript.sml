Theory makeSsaCurrentEndpointBatch
Ancestors
  makeSsaCurrentDominanceAvailability makeSsaCurrentPhiBatchRuntime
  makeSsaCurrentPrefixRuntime venomExecProofs venomWf venomExecSemantics
  venomState list option cfgNormSupplySim finite_map sccpCorrectnessProofs

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

Theorem current_completed_block_outputs_defined:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  exec_block fuel C bb st = OK edge /\
  (!j x. j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
     MEM x (EL j bb.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x st)) ==>
  !i x. MEM i bb.bb_instructions /\ MEM x i.inst_outputs ==>
    IS_SOME (lookup_var x edge)
Proof
  rpt strip_tac >>
  `?idx. idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = i` by
    metis_tac[MEM_EL] >>
  `~is_terminator i.inst_opcode` by
    (strip_tac >> `i.inst_outputs = []` by
       metis_tac[terminator_no_outputs, EVERY_MEM] >> gvs[]) >>
  `x IN FDOM edge.vs_vars` by
    (irule exec_block_outputs_in_fdom_from_prefix >>
     qexistsl [`bb`, `C`, `fuel`, `idx`, `st`] >>
     simp[] >> rpt strip_tac >>
     fs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     metis_tac[option_nchotomy, IS_SOME_DEF]) >>
  fs[lookup_var_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem current_completed_edge_phi_batch_total:
  wf_function f /\ wf_ssa f /\ MEM pred f.fn_blocks /\
  pred.bb_label = before.vs_current_bb /\ EVERY inst_wf pred.bb_instructions /\
  strict_dom_vars_defined f before /\ fn_reachable f before.vs_current_bb /\
  before.vs_inst_idx <= LENGTH pred.bb_instructions /\
  (!j x. j < before.vs_inst_idx /\ j < LENGTH pred.bb_instructions /\
     MEM x (EL j pred.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x before)) /\
  exec_block fuel C pred before = OK edge /\
  lookup_block edge.vs_current_bb f.fn_blocks = SOME bb /\
  EVERY inst_wf bb.bb_instructions ==> ?post. eval_phis edge bb.bb_instructions = OK post
Proof
  rpt strip_tac >>
  `bb_well_formed pred` by metis_tac[wf_function_def] >>
  `pred.bb_instructions <> [] /\
   (!i. i < LENGTH pred.bb_instructions - 1 ==>
      ~is_terminator (EL i pred.bb_instructions).inst_opcode)` by
    (fs[bb_well_formed_def] >> rpt strip_tac >>
     `i < LENGTH pred.bb_instructions` by decide_tac >>
     `i = PRE (LENGTH pred.bb_instructions)` by metis_tac[] >> decide_tac) >>
  `edge.vs_prev_bb = SOME before.vs_current_bb` by
    (drule_all exec_block_ok_prev_bb_general >> simp[]) >>
  `MEM edge.vs_current_bb (bb_succs pred)` by
    (drule_all exec_block_current_bb_in_succs >> simp[]) >>
  `MEM bb f.fn_blocks /\ bb.bb_label = edge.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `fn_cfg_edge f pred.bb_label bb.bb_label` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `strict_dom_vars_defined f (edge with vs_current_bb := pred.bb_label)` by
    (drule exec_block_fdom_mono >>
     simp[strict_dom_vars_defined_def, pred_setTheory.SUBSET_DEF] >>
     fs[strict_dom_vars_defined_def] >> metis_tac[]) >>
  `!i x. MEM i pred.bb_instructions /\ MEM x i.inst_outputs ==>
     IS_SOME (lookup_var x edge)` by
    (rpt strip_tac >> irule current_completed_block_outputs_defined >>
     qexistsl [`C`, `pred`, `fuel`, `i`, `before`] >> simp[] >> metis_tac[]) >>
  irule current_endpoint_phi_batch_total >>
  conj_tac >- simp[] >> qexistsl [`f`, `pred`] >> simp[] >> metis_tac[]
QED
