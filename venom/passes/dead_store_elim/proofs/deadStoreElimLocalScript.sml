Theory deadStoreElimLocal
Ancestors
  deadStoreElimPending deadStoreElimMemory deadStoreElimSafety deadStoreElimEquiv
  deadStoreElimFrame deadStoreElimDefs venomState venomExecSemantics
  basePtrDefs memLocDefs finite_map phiCongruence venomExecProofs
  deadStoreElimLiveness list vfmState
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

Theorem dse_local_agrees_eval_one_phi:
  dse_local_agrees sp P s t ==> eval_one_phi s inst = eval_one_phi t inst
Proof
  strip_tac >>
  `dse_safety_agrees s t` by fs[dse_local_agrees_def] >>
  `s.vs_prev_bb = t.vs_prev_bb` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  `!op. eval_operand op s = eval_operand op t` by
    metis_tac[dse_safety_agrees_eval_operand] >>
  simp[eval_one_phi_def]
QED

Theorem dse_pending_at_phi_prefix:
  dse_pending_at cfg bp sp fn bb 0 P s ==>
  dse_pending_at cfg bp sp fn bb (phi_prefix_length bb.bb_instructions) P s
Proof
  rewrite_tac[dse_pending_at_def] >> strip_tac >>
  reverse conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  simp[EVERY_MEM] >> qx_gen_tac `entry` >> strip_tac >>
  PairCases_on `entry` >> gvs[] >>
  qpat_x_assum `EVERY _ P` mp_tac >> simp[EVERY_MEM] >>
  disch_then drule >> simp[] >> strip_tac >>
  irule dse_suffix_dead_phi_prefix >> simp[]
QED

Theorem dse_local_agrees_eval_phis:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb 0 P s /\
  eval_phis s bb.bb_instructions = OK s1 ==>
  ?t1. eval_phis t bb.bb_instructions = OK t1 /\
    dse_local_agrees sp P
      (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (t1 with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    dse_pending_at cfg bp sp fn bb
      (phi_prefix_length bb.bb_instructions) P s1
Proof
  strip_tac >>
  `?t1. eval_phis t bb.bb_instructions = OK t1 /\
        dse_local_agrees sp P s1 t1` by
    (irule eval_phis_rel >> conj_tac
     >- metis_tac[dse_local_agrees_update_var] >>
     qexists_tac `s` >> simp[] >>
     metis_tac[dse_local_agrees_eval_one_phi]) >>
  qexists_tac `t1` >> simp[dse_local_agrees_inst_idx] >>
  qpat_assum `eval_phis s _ = OK s1`
    (mp_then Any strip_assume_tac eval_phis_preserves_alloca_fields) >>
  irule dse_pending_at_allocas_extend >> qexists_tac `s` >>
  simp[dse_pending_at_phi_prefix]
QED

Theorem dse_local_agrees_undefined_read_ok:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\
  bp_get_read_location bp (EL idx bb.bb_instructions) sp = ml_undefined /\
  step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s1 ==>
  step_inst fuel ctx (EL idx bb.bb_instructions) t = OK s1 /\
  dse_local_agrees sp [] s1 s1 /\
  dse_pending_at cfg' bp' sp fn' bb' idx' [] s1
Proof
  strip_tac >> drule_all dse_local_agrees_undefined_read_step >>
  disch_then (qspecl_then [`fuel`, `ctx`] assume_tac) >>
  gvs[dse_local_agrees_refl, dse_pending_at_empty]
QED

Theorem dse_local_agrees_undefined_read_ok_inst_idx:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\
  bp_get_read_location bp (EL idx bb.bb_instructions) sp = ml_undefined /\
  step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s1 ==>
  step_inst fuel ctx (EL idx bb.bb_instructions) t = OK s1 /\
  dse_local_agrees sp [] (s1 with vs_inst_idx := next_idx)
    (s1 with vs_inst_idx := next_idx) /\
  dse_pending_at cfg' bp' sp fn' bb' idx' [] s1
Proof
  strip_tac >> drule_all dse_local_agrees_undefined_read_ok >>
  simp[dse_local_agrees_refl, dse_pending_at_empty]
QED

Theorem dse_local_agrees_account_code:
  dse_local_agrees sp P s t ==>
  (lookup_account addr s.vs_accounts).code =
  (lookup_account addr t.vs_accounts).code
Proof
  strip_tac >>
  Cases_on `sp = AddrSp_Storage`
  >- (fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
      Cases_on `addr = s.vs_call_ctx.cc_address`
      >- (gvs[lookup_account_def] >>
          metis_tac[dse_accounts_normalize_code]) >>
      fs[lookup_account_def] >> metis_tac[dse_accounts_normalize_other]) >>
  fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]
QED
