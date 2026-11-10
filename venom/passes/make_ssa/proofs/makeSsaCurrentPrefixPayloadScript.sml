Theory makeSsaCurrentPrefixPayload
Ancestors
  makeSsaCurrentLockstepShape makeSsaCurrentCleanupShape makeSsaDefs venomExecSemantics makeSsaCurrentCleanupBoundary

Theorem current_prefix_simplified_payload:
  inst.inst_opcode = PHI /\ (simplify_current_phi inst).inst_opcode <> PHI ==>
  (?dst src. (simplify_current_phi inst).inst_opcode = ASSIGN /\
    (simplify_current_phi inst).inst_outputs = [dst] /\
    (simplify_current_phi inst).inst_operands = [Var src]) \/
  ((simplify_current_phi inst).inst_opcode = NOP /\
    (simplify_current_phi inst).inst_outputs = [] /\
    (simplify_current_phi inst).inst_operands = [])
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  rpt strip_tac >>
  Cases_on `EVERY (\v. MEM v (inst_ir_vars inst))
    (inst_ir_vars (simplify_current_phi_raw inst))` >> gvs[] >>
  gvs[simplify_current_phi_raw_def, AllCaseEqs()] >>
  Cases_on `current_phi_output inst.inst_outputs` >> gvs[] >>
  rename1 `current_phi_output inst.inst_outputs = SOME out` >>
  Cases_on `current_phi_values (remove_current_phi_self out inst.inst_operands)` >> gvs[] >>
  rename1 `current_phi_values _ = SOME vals` >>
  Cases_on `vals` >> gvs[] >>
  Cases_on `EVERY (\w. w = h) t` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[current_phi_output_def] >>
  Cases_on `t'` >> gvs[current_phi_output_def]
QED

Definition current_copy_payload_def:
  current_copy_payload inst <=>
    (?dst src. inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [dst] /\
      inst.inst_operands = [Var src]) \/
    (inst.inst_opcode = NOP /\ inst.inst_outputs = [] /\ inst.inst_operands = [])
End

Theorem current_copy_payload_id[simp]:
  current_copy_payload (inst with inst_id := id) <=> current_copy_payload inst
Proof
  simp[current_copy_payload_def]
QED

Theorem current_prefix_parts_payload:
  !xs phis ord.
  simplify_current_phi_prefix_parts xs = (phis,ord) ==>
  EVERY current_copy_payload (TAKE (phi_prefix_length xs - LENGTH phis) ord)
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def, phi_prefix_length_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[simplify_current_phi_prefix_parts_def, phi_prefix_length_def] >>
      Cases_on `simplify_current_phi_prefix_parts xs` >>
      Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
      simp[] >> rpt strip_tac >> gvs[] >>
      drule simplify_current_phi_prefix_partition >> strip_tac >>
      qpat_x_assum `LENGTH phis + LENGTH copies = phi_prefix_length xs`
        (SUBST_ALL_TAC o SYM) >>
      gvs[GSYM arithmeticTheory.ADD1] >>
      simp[] >>
      drule_all current_prefix_simplified_payload >>
      simp[current_copy_payload_def]) >>
  simp[simplify_current_phi_prefix_parts_def, phi_prefix_length_def]
QED

Theorem current_prefix_cleaned_payload:
  bb = simplify_current_phi_block new /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < phi_prefix_length new.bb_instructions ==>
  current_copy_payload (EL k bb.bb_instructions)
Proof
  strip_tac >>
  Cases_on `simplify_current_phi_prefix_parts new.bb_instructions` >>
  rename1 `simplify_current_phi_prefix_parts new.bb_instructions = (phis,ord)` >>
  drule current_prefix_parts_payload >> strip_tac >>
  drule simplify_current_phi_parts_prefix >> strip_tac >>
  drule current_phi_prefix_parts_length >> strip_tac >>
  `?first rest. new.bb_instructions = first::rest /\ first.inst_opcode = PHI` by
    (Cases_on `new.bb_instructions` >> gvs[phi_prefix_length_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  `bb.bb_instructions = reassign_current_inst_ids
    (MAP instruction_inst_id new.bb_instructions) (phis ++ ord)` by
    simp[simplify_current_phi_block_def, simplify_current_phi_prefix_def, ETA_THM] >>
  `phi_prefix_length bb.bb_instructions = LENGTH phis` by
    simp[reassign_current_inst_ids_phi_prefix] >>
  `k < LENGTH (phis ++ ord)` by
    (qspec_then `new.bb_instructions` mp_tac venomExecProofsTheory.phi_prefix_length_le >>
     gvs[] >> decide_tac) >>
  drule current_reassign_content >>
  disch_then (qspec_then `MAP instruction_inst_id new.bb_instructions` assume_tac) >>
  `k - LENGTH phis < LENGTH ord /\
   k - LENGTH phis < phi_prefix_length new.bb_instructions - LENGTH phis` by gvs[] >>
  `MEM (EL (k - LENGTH phis) ord)
    (TAKE (phi_prefix_length new.bb_instructions - LENGTH phis) ord)` by
    (simp[listTheory.MEM_EL] >> qexists_tac `k - LENGTH phis` >>
     simp[listTheory.EL_TAKE, listTheory.LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
     gvs[] >> sym_tac >> irule listTheory.EL_TAKE >> decide_tac) >>
  `current_copy_payload (EL (k - LENGTH phis) ord)` by
    metis_tac[listTheory.EVERY_MEM] >>
  gvs[listTheory.EL_APPEND_EQN, current_copy_payload_def]
QED

Theorem current_prefix_actual_payload:
  lookup_block h renamed = SOME new /\
  lookup_block h (simplify_current_phis_if enabled renamed) = SOME bb /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < phi_prefix_length new.bb_instructions ==>
  current_copy_payload (EL k bb.bb_instructions)
Proof
  strip_tac >> fs[current_cleanup_if_lookup] >> Cases_on `enabled` >> gvs[] >>
  irule current_prefix_cleaned_payload >> metis_tac[]
QED
