Theory deadStoreElimLocal
Ancestors
  deadStoreElimPending deadStoreElimMemory deadStoreElimSafety deadStoreElimEquiv
  deadStoreElimFrame deadStoreElimDefs venomState venomExecSemantics
  basePtrDefs memLocDefs finite_map
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Definition dse_operational_agrees_def:
  dse_operational_agrees s t <=>
    s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
    s.vs_prev_bb = t.vs_prev_bb /\ s.vs_fmp = t.vs_fmp /\
    s.vs_call_entry_fmp = t.vs_call_entry_fmp /\
    s.vs_initial_fmp = t.vs_initial_fmp /\
    s.vs_return_pc_token = t.vs_return_pc_token
End

Definition dse_local_agrees_def:
  dse_local_agrees sp P s t <=>
    dse_pending_space sp P s t /\ dse_safety_agrees s t /\
    dse_operational_agrees s t
End

Theorem dse_local_agrees_refl:
  dse_local_agrees sp P s s
Proof
  simp[dse_local_agrees_def, dse_pending_space_refl,
       dse_safety_agrees_refl, dse_operational_agrees_def]
QED

Theorem dse_local_agrees_empty:
  dse_local_agrees sp [] s t ==> s = t
Proof
  simp[dse_local_agrees_def, dse_pending_space_def,
       dse_pending_keys_def] >> strip_tac >>
  `s.vs_memory = t.vs_memory` by
    (Cases_on `sp = AddrSp_Memory`
     >- (irule dse_pending_memory_empty >> fs[]) >>
     fs[dse_equiv_def]) >>
  `s.vs_vars = t.vs_vars` by
    (fs[dse_safety_agrees_def, lookup_var_def, fmap_eq_flookup]) >>
  fs[dse_safety_agrees_def, dse_operational_agrees_def,
     dse_equiv_def] >>
  Cases_on `sp` >> fs[venom_state_component_equality]
QED

Theorem dse_local_agrees_inst_idx:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (s with vs_inst_idx := idx) (t with vs_inst_idx := idx)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
     dse_safety_agrees_def, dse_operational_agrees_def,
     dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
     lookup_var_def]
QED

Theorem dse_local_agrees_current_bb:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (s with vs_current_bb := bb) (t with vs_current_bb := bb)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
     dse_safety_agrees_def, dse_operational_agrees_def,
     dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
     lookup_var_def]
QED

Theorem dse_local_agrees_prev_bb:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (s with vs_prev_bb := bb) (t with vs_prev_bb := bb)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
     dse_safety_agrees_def, dse_operational_agrees_def,
     dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
     lookup_var_def]
QED

Theorem dse_local_agrees_update_var:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (update_var x v s) (update_var x v t)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
      dse_safety_agrees_def, dse_operational_agrees_def,
      dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `x = v'` >> simp[]
QED

Theorem dse_local_agrees_undefined_read:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\
  bp_get_read_location bp (EL idx bb.bb_instructions) sp = ml_undefined ==>
  s = t
Proof
  strip_tac >> drule_all dse_pending_at_undefined_read >> strip_tac >>
  gvs[] >> drule dse_local_agrees_empty >> simp[]
QED

Theorem dse_local_agrees_undefined_read_step:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\
  bp_get_read_location bp (EL idx bb.bb_instructions) sp = ml_undefined ==>
  step_inst fuel ctx (EL idx bb.bb_instructions) s =
  step_inst fuel ctx (EL idx bb.bb_instructions) t
Proof
  strip_tac >> drule_all dse_local_agrees_undefined_read >> simp[]
QED
