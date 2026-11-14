(* State-local memory facts agree with a masked shadow. These facts do not
   assert that any shadow suffix is safe or reachable. *)
Theory staticShadowMemory
Ancestors
  staticShadowDefs o1ContractCfgNorm unitMemInv contextCodegenRel
  venomState

Theorem static_shadow_mem_ranges:
  static_shadow_rel s sh ==>
  inst_mem_ranges inst sh = inst_mem_ranges inst s
Proof
  strip_tac >>
  `sh.vs_call_entry_fmp = s.vs_call_entry_fmp` by
    gvs[static_shadow_rel_def, static_shadow_def,
        venom_state_component_equality] >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  irule supply_inst_mem_ranges_cong >> simp[]
QED

Theorem static_shadow_revert_forward:
  static_shadow_rel s sh ==>
  (in_revert_forward fn sh <=> in_revert_forward fn s)
Proof
  simp[static_shadow_rel_def, static_shadow_def,
       venom_state_component_equality, in_revert_forward_def]
QED

Theorem static_shadow_static_mem_ok:
  static_shadow_rel s sh ==>
  (static_mem_ok eom C fn inst sh <=> static_mem_ok eom C fn inst s)
Proof
  strip_tac >>
  `inst_mem_ranges inst sh = inst_mem_ranges inst s` by
    (irule static_shadow_mem_ranges >> simp[]) >>
  `in_revert_forward fn sh <=> in_revert_forward fn s` by
    (irule static_shadow_revert_forward >> simp[]) >>
  simp[static_mem_ok_def]
QED

Theorem static_shadow_lowered_mem_ok:
  static_shadow_rel s sh ==>
  (lowered_mem_ok eom fmp C fn inst sh <=>
   lowered_mem_ok eom fmp C fn inst s)
Proof
  strip_tac >>
  `inst_mem_ranges inst sh = inst_mem_ranges inst s` by
    (irule static_shadow_mem_ranges >> simp[]) >>
  `in_revert_forward fn sh <=> in_revert_forward fn s` by
    (irule static_shadow_revert_forward >> simp[]) >>
  simp[lowered_mem_ok_def]
QED
