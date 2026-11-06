Theory bodyPtrIntCallRunEntry
Ancestors bodyPtrIntCallAllocation bodyPtrIntCallTaintBounds
  bodyPtrIntCallConfinement venomExecProofs ptrDiscipline

Theorem intcall_alloc_phis_entry:
  eval_phis s insts = OK t /\ intcall_alloc_outside P s ==>
  intcall_alloc_outside P (t with vs_inst_idx := k)
Proof
  strip_tac >> drule eval_phis_preserves_alloca_fields >> strip_tac >>
  fs[intcall_alloc_outside_def] >> metis_tac[]
QED

Theorem intcall_mem_frame_entry:
  intcall_mem_frame P tn0 (entry_taint_vars fn s tn) <=>
  intcall_mem_frame P tn0 tn
Proof
  simp[entry_taint_vars_def, intcall_mem_frame_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
QED
