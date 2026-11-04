Theory loadElimAllocationExclusion
Ancestors
  finite_map words venomState venomInst venomMemDefs basePtrDefs memLocDefs
  dfgCorrectnessProof memoryCopyElisionSound loadElimSentinelHelpers
  venomExecSemantics venomWf

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

Theorem le_erased_alloca_out_of_word:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
  inst.inst_outputs = [out] ==>
  ?t. step_inst fuel ctx inst (le_erase_tracked bp s) = OK t /\
      ~allocas_in_word (t with vs_inst_idx := 0)
Proof
  strip_tac >>
  simp[step_inst_def, step_inst_base_def, exec_alloca_def, FLOOKUP_EMPTY] >>
  simp[allocas_in_word_def, update_var_def] >>
  qexistsl_tac [`inst.inst_id`, `dimword(:256)`, `w2n n`] >>
  simp[FLOOKUP_UPDATE]
QED

Theorem le_step_preserves_no_alloca:
  le_step_preserves bp dfg fn /\ bp_assigns_stable bp dfg /\
  dfg_assigns_sound dfg s /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\ inst_wf inst ==>
  inst.inst_opcode <> ALLOCA
Proof
  strip_tac >> strip_tac >>
  `?n out. inst.inst_operands = [Lit n] /\ inst.inst_outputs = [out]` by
    (gvs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[] >>
     rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  `le_step_invariants bp dfg fn (le_erase_tracked bp s)` by
    (irule le_erase_tracked_invariants >> simp[]) >>
  `?t. step_inst 0 ARB inst (le_erase_tracked bp s) = OK t /\
       ~allocas_in_word (t with vs_inst_idx := 0)` by
    (irule le_erased_alloca_out_of_word >> simp[] >> metis_tac[]) >>
  `le_step_invariants bp dfg fn
     (le_erase_tracked bp s with vs_inst_idx := 0)` by simp[] >>
  fs[le_step_preserves_def] >>
  metis_tac[le_erase_tracked_fields, le_step_invariants_def]
QED
