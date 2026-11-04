Theory loadElimAllocationExclusion
Ancestors
  finite_map words venomState venomInst venomMemDefs basePtrDefs memLocDefs
  dfgCorrectnessProof memoryCopyElisionSound loadElimSentinelHelpers

Definition le_erase_tracked_def:
  le_erase_tracked bp s = s with
    <| vs_vars := DRESTRICT s.vs_vars {v | bp_get_ptrs bp v = []};
       vs_allocas := FEMPTY; vs_alloca_next := dimword(:256);
       vs_inst_idx := 0 |>
End

Theorem le_erase_tracked_lookup[simp]:
  lookup_var v (le_erase_tracked bp s) =
    if bp_get_ptrs bp v = [] then lookup_var v s else NONE
Proof
  simp[le_erase_tracked_def, lookup_var_def, FLOOKUP_DRESTRICT]
QED

Theorem le_erase_tracked_fields[simp]:
  (le_erase_tracked bp s).vs_allocas = FEMPTY /\
  (le_erase_tracked bp s).vs_alloca_next = dimword(:256) /\
  (le_erase_tracked bp s).vs_inst_idx = 0 /\
  (le_erase_tracked bp s).vs_labels = s.vs_labels /\
  (le_erase_tracked bp s with vs_inst_idx := 0) = le_erase_tracked bp s
Proof
  simp[le_erase_tracked_def]
QED

Theorem le_erase_tracked_dfg:
  bp_assigns_stable bp dfg /\ dfg_assigns_sound dfg s ==>
  dfg_assigns_sound dfg (le_erase_tracked bp s)
Proof
  strip_tac >> rw[dfg_assigns_sound_def] >>
  qpat_x_assum `dfg_assigns_sound _ _` mp_tac >>
  simp[dfg_assigns_sound_def] >> disch_then drule_all >> disch_tac >>
  qpat_x_assum `bp_assigns_stable _ _` mp_tac >>
  simp[bp_assigns_stable_def] >> disch_then drule_all >> disch_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `h::t` >> Cases_on `t` >> gvs[] >>
  Cases_on `h` >> gvs[eval_operand_def]
QED

Theorem le_erase_tracked_bp_sound:
  bp_ptr_sound bp (le_erase_tracked bp s)
Proof
  rw[bp_ptr_sound_def] >> gvs[]
QED

Theorem le_erase_tracked_memloc:
  memloc_within_alloca ml (le_erase_tracked bp s)
Proof
  Cases_on `ml.ml_offset` >> Cases_on `ml.ml_size` >>
  Cases_on `ml.ml_alloca` >> simp[memloc_within_alloca_def] >>
  rename1 `SOME alloc` >> Cases_on `alloc` >>
  simp[memloc_within_alloca_def, FLOOKUP_EMPTY]
QED

Theorem le_erase_tracked_invariants:
  bp_assigns_stable bp dfg /\ dfg_assigns_sound dfg s ==>
  le_step_invariants bp dfg fn (le_erase_tracked bp s)
Proof
  strip_tac >>
  simp[le_step_invariants_def, le_erase_tracked_dfg,
       le_erase_tracked_bp_sound, allocas_non_overlapping_def,
       allocas_in_word_def, FLOOKUP_EMPTY, bp_ptrs_bounded_def,
       le_erase_tracked_memloc]
QED
