Theory staticShadowFrame
Ancestors
  staticShadowPrim staticShadowDefs venomState venomExecSemantics list finite_map

Theorem static_shadow_rel_istore:
  static_shadow_rel s sh ==>
  static_shadow_rel (istore off v s) (istore off v sh)
Proof
  strip_tac >>
  `sh.vs_immutables = s.vs_immutables` by
    gvs[static_shadow_rel_def, static_shadow_def, venom_state_component_equality] >>
  simp[istore_def] >>
  gvs[static_shadow_rel_def, static_shadow_def, mstore_def,
      venom_state_component_equality]
QED

Theorem static_shadow_rel_controls:
  static_shadow_rel s sh ==>
  static_shadow_rel (jump_to lbl s) (jump_to lbl sh) /\
  static_shadow_rel (halt_state s) (halt_state sh) /\
  static_shadow_rel (set_returndata bs s) (set_returndata bs sh)
Proof
  simp[static_shadow_rel_def, static_shadow_def, jump_to_def, halt_state_def,
       set_returndata_def, venom_state_component_equality]
QED

Theorem static_shadow_rel_updates:
  static_shadow_rel s sh ==>
  static_shadow_rel (s with vs_inst_idx := n) (sh with vs_inst_idx := n) /\
  static_shadow_rel (s with vs_current_bb := lbl) (sh with vs_current_bb := lbl) /\
  static_shadow_rel (s with vs_prev_bb := prev) (sh with vs_prev_bb := prev) /\
  static_shadow_rel (s with vs_fmp := fmp) (sh with vs_fmp := fmp) /\
  static_shadow_rel (s with vs_gas_readings := gs) (sh with vs_gas_readings := gs) /\
  static_shadow_rel (s with vs_immutables := im) (sh with vs_immutables := im) /\
  static_shadow_rel (s with vs_allocas := allocas) (sh with vs_allocas := allocas) /\
  static_shadow_rel (s with vs_alloca_next := frontier)
                    (sh with vs_alloca_next := frontier)
Proof
  simp[static_shadow_rel_def, static_shadow_def, venom_state_component_equality]
QED

Theorem static_shadow_rel_merge_callee:
  static_shadow_rel s sh /\ static_shadow_rel t th ==>
  static_shadow_rel (merge_callee_state s t) (merge_callee_state sh th)
Proof
  simp[static_shadow_rel_def, static_shadow_def, merge_callee_state_def,
       venom_state_component_equality]
QED

Theorem static_shadow_rel_adopt_return:
  static_shadow_rel s sh ==>
  static_shadow_rel (adopt_return_fmp ir s) (adopt_return_fmp ir sh)
Proof
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, static_shadow_rel_updates]
QED
