Theory makeSsaCurrentPrefixSuffixOwner
Ancestors
  makeSsaCurrentPrefixCopyOwner makeSsaCurrentPrefixOwner
  makeSsaCurrentPrefixMaps makeSsaCurrentCarrierOwner
  makeSsaCurrentWfSsa makeSsaCurrentLockstepShape
  makeSsaCurrentCleanupBoundary makeSsaCurrentDefs makeSsaCurrentCertificate
  venomInst venomExecSemantics list rich_list makeSsaRfAllocation
Theorem current_prefix_phi_copy_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ q < LENGTH new.bb_instructions /\
  (EL q new.bb_instructions).inst_opcode = PHI /\
  (simplify_current_phi (EL q new.bb_instructions)).inst_opcode = ASSIGN /\
  (simplify_current_phi (EL q new.bb_instructions)).inst_outputs = [d] /\
  (simplify_current_phi (EL q new.bb_instructions)).inst_operands = [Var src] ==>
  ?v td ts. MEM (td,v,d) H /\ MEM (ts,v,src) H
Proof
  strip_tac >>
  `?v. current_wf_inserted_phi_at A renamed h q v` by
    (drule_all current_wf_phi_occurrence_provenance >> strip_tac
     >- metis_tac[] >>
     drule_all current_wf_original_phi_retained >> strip_tac >> gvs[]) >>
  `simplify_current_phi (EL q new.bb_instructions) =
    (EL q new.bb_instructions) with
      <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
   (EL q new.bb_instructions).inst_outputs = [d]` by
    (drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac >> gvs[]) >>
  drule_all current_prefix_inserted_copy_owner >> metis_tac[]
QED

Theorem current_prefix_parts_property:
  !xs phis ord P.
  simplify_current_phi_prefix_parts xs = (phis,ord) /\
  (!inst. MEM inst xs /\ inst.inst_opcode = PHI ==> P (simplify_current_phi inst)) ==>
  EVERY P (TAKE (phi_prefix_length xs - LENGTH phis) ord)
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
      gvs[GSYM arithmeticTheory.ADD1] >> first_x_assum irule >> metis_tac[]) >>
  simp[simplify_current_phi_prefix_parts_def, phi_prefix_length_def]
QED

Theorem current_prefix_cleaned_copy_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  bb = simplify_current_phi_block new /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < phi_prefix_length new.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = ASSIGN /\
  (EL k bb.bb_instructions).inst_outputs = [d] /\
  (EL k bb.bb_instructions).inst_operands = [Var src] ==>
  ?v td ts. MEM (td,v,d) H /\ MEM (ts,v,src) H
Proof
  strip_tac >>
  Cases_on `simplify_current_phi_prefix_parts new.bb_instructions` >>
  rename1 `simplify_current_phi_prefix_parts new.bb_instructions = (phis,ord)` >>
  `EVERY (\inst. !d src. inst.inst_opcode = ASSIGN /\
    inst.inst_outputs = [d] /\ inst.inst_operands = [Var src] ==>
    ?v td ts. MEM (td,v,d) H /\ MEM (ts,v,src) H)
    (TAKE (phi_prefix_length new.bb_instructions - LENGTH phis) ord)` by
    (irule current_prefix_parts_property >> simp[] >> rpt strip_tac >>
     `?q. q < LENGTH new.bb_instructions /\ EL q new.bb_instructions = inst` by
       metis_tac[MEM_EL] >>
     irule current_prefix_phi_copy_owner >> metis_tac[]) >>
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
   k - LENGTH phis < phi_prefix_length new.bb_instructions - LENGTH phis` by
    gvs[] >>
  fs[EVERY_MEM] >>
  `MEM (EL (k - LENGTH phis) ord)
    (TAKE (phi_prefix_length new.bb_instructions - LENGTH phis) ord)` by
    (simp[MEM_EL] >> qexists `k - LENGTH phis` >>
     simp[EL_TAKE, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> gvs[] >> decide_tac) >>
  gvs[EL_APPEND_EQN] >> metis_tac[]
QED

Theorem current_prefix_cleaned_suffix_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ bb = simplify_current_phi_block new /\
  current_history_valid V H /\
  (!z x. FLOOKUP M z = SOME x ==> ?t. MEM (t,x,z) H) /\
  phi_prefix_length bb.bb_instructions <= k /\
  k <= phi_prefix_length new.bb_instructions ==>
  (!z x. current_prefix_back
    (TAKE (phi_prefix_length new.bb_instructions - k) (DROP k bb.bb_instructions))
    M z x ==> ?t. MEM (t,x,z) H) /\
  current_prefix_functional (current_prefix_back
    (TAKE (phi_prefix_length new.bb_instructions - k) (DROP k bb.bb_instructions)) M)
Proof
  strip_tac >>
  `current_prefix_functional (\z x. ?t. MEM (t,x,z) H)` by
    (simp[current_prefix_functional_def] >>
     metis_tac[current_history_name_unique]) >>
  `!inst d src. MEM inst
      (TAKE (phi_prefix_length new.bb_instructions - k) (DROP k bb.bb_instructions)) /\
    inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [d] /\
    inst.inst_operands = [Var src] ==>
    ?v. (?td. MEM (td,v,d) H) /\ (?ts. MEM (ts,v,src) H)` by
    (rpt strip_tac >>
     qpat_x_assum `MEM inst _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     `n < phi_prefix_length new.bb_instructions - k /\
      n < LENGTH (DROP k bb.bb_instructions)` by
       (gvs[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> decide_tac) >>
     `EL n (TAKE (phi_prefix_length new.bb_instructions - k)
        (DROP k bb.bb_instructions)) = EL (k+n) bb.bb_instructions` by
       (gvs[LENGTH_DROP] >> simp[EL_TAKE, EL_DROP, arithmeticTheory.ADD_COMM]) >>
     `phi_prefix_length bb.bb_instructions <= k+n /\
      k+n < phi_prefix_length new.bb_instructions` by decide_tac >>
     `?v td ts. MEM (td,v,d) H /\ MEM (ts,v,src) H` by
       (irule current_prefix_cleaned_copy_owner >> metis_tac[]) >> metis_tac[]) >>
  qspecl_then
    [`TAKE (phi_prefix_length new.bb_instructions - k) (DROP k bb.bb_instructions)`,
     `M`, `\z x. ?t. MEM (t,x,z) H`] mp_tac current_prefix_back_owner >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  simp[] >> fs[current_prefix_functional_def] >> metis_tac[]
QED

Theorem current_prefix_opcodes_length:
  !xs ys. MAP instruction_inst_opcode xs = MAP instruction_inst_opcode ys ==>
  phi_prefix_length xs = phi_prefix_length ys
Proof
  Induct_on `xs` >- (Cases >> simp[phi_prefix_length_def]) >>
  gen_tac >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  simp[phi_prefix_length_def] >> metis_tac[]
QED

Theorem current_prefix_collect_length:
  !xs. LENGTH (collect_phis xs) = phi_prefix_length xs
Proof
  Induct >> simp[livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem current_prefix_actual_endpoint:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\ A h = current_block_annotations old pre ==>
  phi_prefix_length new.bb_instructions =
    LENGTH pre + LENGTH (collect_phis old.bb_instructions)
Proof
  strip_tac >> drule_all current_wf_phi_context_block_opcodes >> strip_tac >>
  `LENGTH pre = LENGTH pre'` by
    (qpat_x_assum `A h = current_block_annotations old pre` mp_tac >>
     simp[current_block_annotations_def, current_inserted_annotations_def] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  drule current_prefix_opcodes_length >> strip_tac >>
  simp[phi_prefix_length_prepend, current_prefix_collect_length]
QED
