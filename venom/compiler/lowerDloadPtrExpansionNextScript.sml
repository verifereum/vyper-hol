Theory lowerDloadPtrExpansionNext
Ancestors
  lowerDloadPtrJointNext lowerDloadPtrExpansionTransport lowerDloadPtrPhi
  lowerDloadPtrPhase lowerDloadPtrRel ptrDiscipline venomInst
  lowerDloadDefs venomExecSemantics venomState
  instIdxIndep list words finite_map pred_set arithmetic

(* Footprints, not value equality: original pointers may be relocated. *)
Theorem dload_replay_alloca_footprint[local]:
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [av] /\
  step_inst fuel C a t = OK u ==>
  u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
  u.vs_inst_idx = t.vs_inst_idx /\
  (!v. v <> av ==> lookup_var v u = lookup_var v t)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem dload_replay_add_footprint[local]:
  a.inst_opcode = ADD /\ a.inst_outputs = [cv] /\
  step_inst fuel C a t = OK u ==>
  u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
  u.vs_inst_idx = t.vs_inst_idx /\
  (!v. v <> cv ==> lookup_var v u = lookup_var v t)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def] >>
  gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem dload_replay_copy_footprint[local]:
  a.inst_opcode = CODECOPY /\ step_inst fuel C a t = OK u ==>
  u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
  u.vs_inst_idx = t.vs_inst_idx /\
  (!v. lookup_var v u = lookup_var v t)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def] >>
  gvs[AllCaseEqs(), write_memory_with_expansion_def, lookup_var_def]
QED

Theorem dload_replay_read_footprint[local]:
  MEM a.inst_opcode [DLOAD;MLOAD] /\ a.inst_outputs = [out] /\
  step_inst fuel C a t = OK u ==>
  ?z. u = update_var out z t
Proof
  simp[] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem dload_four_step_definedness_control:
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\
  d.inst_opcode = MLOAD /\ d.inst_outputs = [out] /\
  i.inst_opcode = DLOAD /\ i.inst_outputs = [out] /\
  av NOTIN U /\ cv NOTIN U /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C i s = OK s1 /\
  dload_prefix_match fuel Ct PH [a;b;c;d] 4 t H un t4 H4 un4 ==>
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\
  t4.vs_current_bb = t.vs_current_bb /\ t4.vs_prev_bb = t.vs_prev_bb /\
  t4.vs_inst_idx = t.vs_inst_idx + 4 /\
  (!v. v IN U ==>
    (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
     lookup_var v t4 = NONE))
Proof
  strip_tac >> drule dload_four_step_replay >> strip_tac >>
  drule_all dload_replay_alloca_footprint >> strip_tac >>
  drule_all dload_replay_add_footprint >> strip_tac >>
  drule_all dload_replay_copy_footprint >> strip_tac >>
  `?z. s1 = update_var out z s` by
    (qpat_assum `step_inst fuel C i s = OK s1`
       (mp_then Any mp_tac dload_replay_read_footprint) >> simp[]) >>
  `?w. v4 = update_var out w t3` by
    (qpat_assum `step_inst fuel Ct d t3 = OK v4`
       (mp_then Any mp_tac dload_replay_read_footprint) >> simp[]) >>
  gvs[update_var_def, lookup_var_def] >>
  rpt strip_tac >> Cases_on `v = out` >> simp[FLOOKUP_UPDATE] >>
  `v <> av /\ v <> cv` by metis_tac[] >>
  metis_tac[]
QED

Theorem dload_supply_definedness_control:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av NOTIN U /\ cv NOTIN U /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C i s = OK s1 /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 ==>
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\
  t4.vs_current_bb = t.vs_current_bb /\ t4.vs_prev_bb = t.vs_prev_bb /\
  t4.vs_inst_idx = t.vs_inst_idx + LENGTH xs /\
  (!v. v IN U ==>
    (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
     lookup_var v t4 = NONE))
Proof
  strip_tac >> drule_all dload_supply_expansion >> strip_tac >> gvs[] >>
  qpat_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac dload_four_step_definedness_control) >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem dload_actual_dload_next:
  dload_boundary_core lo (r::rs) {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  t.vs_alloca_next + 32 < dimword (:256) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN {v | ~retpc_var f v} /\ cv NOTIN {v | ~retpc_var f v} /\
  off <> Var av /\ code_layout_valid s /\ dload_offset_ok C f i s /\
  eval_operand off s = SOME x /\ eval_operand off t = SOME x /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i xs 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  av NOTIN set (fn_ir_vars f) /\ cv NOTIN set (fn_ir_vars f) /\
  active_inst g j t4 ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      t4 i' emitted' 0 /\ j = HD emitted' /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v t4 = NONE))
Proof
  strip_tac >> drule_all dload_supply_replay_boundary >> strip_tac >>
  drule_all dload_supply_definedness_control >> strip_tac >>
  drule_all dload_control_emission_next_fields >> strip_tac >>
  qexistsl [`s1`,`r1`,`i'`,`emitted'`] >> simp[] >>
  irule frame_reachable_next >> simp[is_terminator_def] >>
  `active_inst f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ i' _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `dload_control_match _ _ _ s t _ _ _` mp_tac >>
  simp[dload_control_match_def] >> metis_tac[]
QED
