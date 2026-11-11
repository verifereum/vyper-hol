Theory makeSsaCurrentPrefixCopyOccurrence
Ancestors
  makeSsaCurrentPrefixSuffixOwner makeSsaCurrentWfSsa
  makeSsaCurrentLockstepShape makeSsaCurrentCleanupBoundary makeSsaCurrentDefs
  venomInst venomExecSemantics list rich_list

Theorem current_prefix_cleaned_copy_occurrence:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  bb = simplify_current_phi_block new /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < phi_prefix_length new.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL k bb.bb_instructions).inst_outputs = [d] /\
  (EL k bb.bb_instructions).inst_operands = [Var src] ==>
  ?q v. q < LENGTH new.bb_instructions /\
    (EL q new.bb_instructions).inst_opcode = PHI /\
    current_wf_inserted_phi_at A renamed h q v /\
    (EL q new.bb_instructions).inst_outputs = [d] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with
        <|inst_opcode := ASSIGN; inst_operands := [Var src]|>
Proof
  strip_tac >>
  Cases_on `simplify_current_phi_prefix_parts new.bb_instructions` >>
  rename1 `simplify_current_phi_prefix_parts new.bb_instructions = (phis,ord)` >>
  `EVERY (\inst. ?q. q < LENGTH new.bb_instructions /\
    (EL q new.bb_instructions).inst_opcode = PHI /\
    inst.inst_opcode = (simplify_current_phi (EL q new.bb_instructions)).inst_opcode /\
    inst.inst_outputs = (simplify_current_phi (EL q new.bb_instructions)).inst_outputs /\
    inst.inst_operands = (simplify_current_phi (EL q new.bb_instructions)).inst_operands)
    (TAKE (phi_prefix_length new.bb_instructions - LENGTH phis) ord)` by
    (irule current_prefix_parts_property >> simp[] >> rpt strip_tac >>
     `?q. q < LENGTH new.bb_instructions /\ EL q new.bb_instructions = inst` by
       metis_tac[MEM_EL] >> qexists_tac `q` >> simp[]) >>
  drule simplify_current_phi_parts_prefix >> strip_tac >>
  drule current_phi_prefix_parts_length >> strip_tac >>
  `?first rest. new.bb_instructions = first::rest /\ first.inst_opcode = PHI` by
    (Cases_on `new.bb_instructions` >> gvs[phi_prefix_length_def] >>
     Cases_on `h'.inst_opcode = PHI` >> gvs[]) >>
  `bb.bb_instructions = reassign_current_inst_ids
    (MAP instruction_inst_id new.bb_instructions) (phis ++ ord)` by
    simp[simplify_current_phi_block_def, simplify_current_phi_prefix_def, ETA_THM] >>
  `phi_prefix_length bb.bb_instructions = LENGTH phis` by
    simp[reassign_current_inst_ids_phi_prefix] >>
  `k < LENGTH (phis ++ ord)` by
    (qspec_then `new.bb_instructions` mp_tac venomExecProofsTheory.phi_prefix_length_le >>
     gvs[] >> decide_tac) >>
  drule current_reassign_content >>
  disch_then (qspec_then `MAP instruction_inst_id new.bb_instructions` strip_assume_tac) >>
  `k - LENGTH phis < LENGTH ord /\
   k - LENGTH phis < phi_prefix_length new.bb_instructions - LENGTH phis` by gvs[] >>
  `MEM (EL (k - LENGTH phis) ord)
    (TAKE (phi_prefix_length new.bb_instructions - LENGTH phis) ord)` by
    (simp[MEM_EL] >> qexists `k - LENGTH phis` >> conj_tac
     >- (simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> gvs[] >> decide_tac) >>
     sym_tac >> irule EL_TAKE >> simp[] >> gvs[] >> decide_tac) >>
  fs[EVERY_MEM] >>
  qpat_x_assum `!inst. MEM inst _ ==> _`
    (qspec_then `EL (k - LENGTH phis) ord` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[EL_APPEND_EQN] >>
  `q < LENGTH new.bb_instructions` by gvs[] >>
  qpat_x_assum `new.bb_instructions = first::rest` (SUBST_ALL_TAC o SYM) >>
  `?v. current_wf_inserted_phi_at A renamed h q v` by
    (drule_all current_wf_phi_occurrence_provenance >> strip_tac
     >- metis_tac[] >>
     drule_all current_wf_original_phi_retained >> strip_tac >> gvs[]) >>
  drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem current_prefix_cleaned_copy_source_cases:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ bb = simplify_current_phi_block new /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < phi_prefix_length new.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL k bb.bb_instructions).inst_outputs = [d] /\
  (EL k bb.bb_instructions).inst_operands = [Var src] ==>
  ?q v. q < LENGTH new.bb_instructions /\
    (EL q new.bb_instructions).inst_opcode = PHI /\
    current_wf_inserted_phi_at A renamed h q v /\
    (EL q new.bb_instructions).inst_outputs = [d] /\
    simplify_current_phi (EL q new.bb_instructions) =
      (EL q new.bb_instructions) with
        <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
    ((?db di. MEM db renamed /\ MEM di db.bb_instructions /\
      MEM src di.inst_outputs /\ db.bb_label <> new.bb_label /\
      fn_dominates (fn with fn_blocks := renamed) db.bb_label new.bb_label) \/
     (?j r slots. current_wf_original_phi_at fn A renamed h j r slots /\
       MEM src (EL r new.bb_instructions).inst_outputs /\ src <> d /\
       simplify_current_phi (EL r new.bb_instructions) = EL r new.bb_instructions))
Proof
  strip_tac >> drule_all current_prefix_cleaned_copy_occurrence >> strip_tac >>
  qexistsl_tac [`q`, `v`] >> simp[] >>
  drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac >> gvs[] >>
  gvs[instruction_component_equality] >> metis_tac[]
QED
