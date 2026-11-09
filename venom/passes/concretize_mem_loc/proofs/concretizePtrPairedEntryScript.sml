Theory concretizePtrPairedEntry
Ancestors
  concretizePtrPairedFields concretizePtrLedgerAlignment
  concretizePtrPairedPrefixProbe concretizePtrMixedPhi
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape venomExecProofs venomExecSemantics venomWf
  concretizePtrPrefixLedger analysisSimProofsBase
  frameHistoryInstructions frameCfgBoundary contextCodegenRel passSimulationDefs
  venomInst unitLabelMapIdentity
  list rich_list arithmetic finite_map

(* Generic filtering boundary: an entirely retained initial segment keeps
   its indices, independently of deletions in the remaining suffix. *)
Theorem ptr_filter_retained_prefix:
  !xs p P. p <= LENGTH xs /\
    (!q. q < p ==> P (EL q xs)) ==>
    p <= LENGTH (FILTER P xs) /\
    (!q. q < p ==> EL q (FILTER P xs) = EL q xs)
Proof
  Induct >> simp[] >> Cases_on `p` >> simp[] >> rpt gen_tac >> strip_tac >>
  `P h` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `n <= LENGTH (FILTER P xs) /\
   (!q. q < n ==> EL q (FILTER P xs) = EL q xs)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC q` mp_tac) >> simp[EL_CONS]) >>
  simp[] >> Cases_on `q` >> simp[]
QED

Theorem ptr_phi_filter_prefix:
  !xs P.
  (!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
    (EL i xs).inst_opcode = PHI) /\
  (!i. MEM i xs /\ i.inst_opcode = PHI ==> P i) ==>
  phi_prefix_length (FILTER P xs) = phi_prefix_length xs
Proof
  Induct >- simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`P h` by metis_tac[MEM] >> simp[phi_prefix_length_def] >>
      first_x_assum irule >> simp[MEM] >> rpt strip_tac
      >- (qpat_x_assum `!i j. _` (qspecl_then [`SUC i`,`SUC j`] mp_tac) >>
          simp[EL_CONS]) >> metis_tac[MEM]) >>
  Cases_on `P h` >- simp[phi_prefix_length_def] >>
  simp[phi_prefix_length_def] >> irule no_phis_phi_prefix_length_zero >>
  simp[EVERY_FILTER, EVERY_EL] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`0`,`SUC n`] mp_tac) >> simp[EL_CONS]
QED

Theorem ptr_ledger_entry_indices:
  ptr_ledger_block_alignment p src tgt indices /\
  (!i j. i < j /\ j < LENGTH src /\ (EL j src).inst_opcode = PHI ==>
    (EL i src).inst_opcode = PHI) ==>
  phi_prefix_length tgt = phi_prefix_length src /\
  (!q. q < phi_prefix_length src ==> EL q indices = q)
Proof
  strip_tac >>
  `!q. q < phi_prefix_length src ==> (EL q src).inst_opcode = PHI` by
    (mp_tac (Q.SPEC `src` analysisSimProofsBaseTheory.phi_prefix_all_phi) >>
     simp[EVERY_EL, LENGTH_TAKE_EQ, phi_prefix_length_le, EL_TAKE]) >>
  conj_tac
  >- (`tgt = FILTER (\i. i.inst_opcode <> NOP)
        (MAP (concretize_inst_with_positions p) src)` by
        (mp_tac (Q.INST [`positions` |-> `p`] ptr_ledger_alignment_construct) >>
         gvs[ptr_ledger_block_alignment_def]) >>
      simp[] >> irule EQ_TRANS >>
      qexists_tac `phi_prefix_length (MAP (concretize_inst_with_positions p) src)` >>
      conj_tac
      >- (match_mp_tac ptr_phi_filter_prefix >> conj_tac
          >- (rpt strip_tac >> fs[] >> `i < LENGTH src` by decide_tac >>
              gvs[EL_MAP, concretize_positions_phi] >> metis_tac[]) >>
          simp[]) >>
      POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `src` >>
      simp[phi_prefix_length_def, concretize_positions_phi]) >>
  `phi_prefix_length src <= LENGTH src` by simp[phi_prefix_length_le] >>
  `!q. q < phi_prefix_length src ==>
    (concretize_inst_with_positions p (EL q src)).inst_opcode <> NOP` by
    (rpt strip_tac >>
     ` (EL q src).inst_opcode = PHI` by metis_tac[] >>
     gvs[concretize_positions_phi]) >>
  mp_tac (Q.ISPECL [`COUNT_LIST (LENGTH (src:instruction list))`,`phi_prefix_length src`,
    `\j. (concretize_inst_with_positions p (EL j src)).inst_opcode <> NOP`]
      ptr_filter_retained_prefix) >>
  simp[EL_COUNT_LIST, LENGTH_COUNT_LIST] >> strip_tac >>
  gvs[ptr_ledger_block_alignment_def, EL_COUNT_LIST]
QED

Theorem ptr_paired_entry_cursor:
  ptr_paired_code R lp positions f g /\
  ALL_DISTINCT (fn_labels f) /\ ALL_DISTINCT (fn_labels g) /\
  fn_inst_wf f /\ EVERY bb_well_formed f.fn_blocks /\
  (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id))) /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  enters_block f s s' /\ enters_block g t t' /\
  a.po_fn = f /\ a.po_state = s' /\
  at.po_fn = g /\ at.po_state = t' /\ active_inst g at.po_inst t' ==>
  ?i. active_inst f i s' /\ ptr_paired_cursor lp (a with po_inst := i) at
Proof
  strip_tac >>
  `s'.vs_current_bb = t'.vs_current_bb /\ s'.vs_prev_bb = t'.vs_prev_bb` by
    metis_tac[enters_block_control_labels] >>
  qpat_assum `enters_block f s s'` (mp_then Any strip_assume_tac enters_block_entry_index) >>
  drule ptr_ledger_alignment_function >>
  disch_then (qspec_then `lp f` strip_assume_tac) >>
  `MEM bbt g.fn_blocks` by fs[ptr_paired_code_def] >>
  `lookup_block s'.vs_current_bb f.fn_blocks = SOME bb /\
   lookup_block t'.vs_current_bb g.fn_blocks = SOME bbt` by
    (conj_tac >> irule MEM_lookup_block >> gvs[fn_labels_def]) >>
  `t'.vs_inst_idx = phi_prefix_length bbt.bb_instructions` by
    (qpat_assum `enters_block g t t'` (mp_then Any strip_assume_tac enters_block_entry_index) >>
     `lookup_block t'.vs_current_bb g.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> gvs[fn_labels_def]) >> gvs[]) >>
  `bb_well_formed bb` by fs[EVERY_MEM] >>
  drule ptr_ledger_entry_indices >>
  impl_tac >- fs[bb_well_formed_def] >> strip_tac >>
  `t'.vs_inst_idx < LENGTH bbt.bb_instructions /\
   at.po_inst = EL t'.vs_inst_idx bbt.bb_instructions` by
    (fs[active_inst_def] >>
     `lookup_block t'.vs_current_bb g.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> gvs[fn_labels_def]) >> gvs[]) >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  `s'.vs_inst_idx <= EL t'.vs_inst_idx indices /\
   EL t'.vs_inst_idx indices < LENGTH bb.bb_instructions` by
    (conj_tac
     >- (Cases_on `phi_prefix_length bb.bb_instructions = 0` >- gvs[] >>
         `phi_prefix_length bb.bb_instructions - 1 < phi_prefix_length bb.bb_instructions` by decide_tac >>
         `EL (phi_prefix_length bb.bb_instructions - 1) indices =
            phi_prefix_length bb.bb_instructions - 1` by metis_tac[] >>
         `EL (phi_prefix_length bb.bb_instructions - 1) indices <
          EL (phi_prefix_length bb.bb_instructions) indices` by
           (irule ptr_ledger_alignment_order >>
            conj_tac >- decide_tac >> conj_tac >- gvs[] >>
            qexistsl_tac [`lp f`,`bb.bb_instructions`,`bbt.bb_instructions`] >> simp[]) >>
         gvs[] >> decide_tac) >>
     metis_tac[]) >>
  qexists_tac `EL s'.vs_inst_idx bb.bb_instructions` >>
  conj_tac
  >- (simp[active_inst_def] >> qexists_tac `bb` >> simp[] >> decide_tac) >>
  `lookup_block t'.vs_current_bb f.fn_blocks = SOME bb` by metis_tac[] >>
  `phi_prefix_length bb.bb_instructions < LENGTH indices /\
   phi_prefix_length bb.bb_instructions <=
     EL (phi_prefix_length bb.bb_instructions) indices` by gvs[] >>
  simp[ptr_paired_cursor_def] >> qexists_tac `indices` >> simp[] >>
  rpt strip_tac >> irule ptr_paired_covered_gap >>
  conj_tac
  >- (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  qexistsl_tac [`indices`,`t'.vs_inst_idx`,`lp f`,`bbt.bb_instructions`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[fn_insts_MEM] >> metis_tac[]) >>
  Cases_on `t'.vs_inst_idx = 0` >> gvs[] >>
  `t'.vs_inst_idx - 1 < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `EL (t'.vs_inst_idx - 1) indices = t'.vs_inst_idx - 1` by metis_tac[] >>
  decide_tac
QED
