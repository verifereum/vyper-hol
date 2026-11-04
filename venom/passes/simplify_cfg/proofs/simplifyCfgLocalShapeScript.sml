(* Block structure boundaries for the local SimplifyCFG edits. *)
Theory simplifyCfgLocalShape
Ancestors
  simplifyCfgDefs simplifyCfgShape simplifyCfgInvariant venomWf venomInst cfgTransform list rich_list

Theorem map_bb_well_formed:
  bb_well_formed bb /\
  (!i. MEM i bb.bb_instructions ==>
    (is_terminator (h i).inst_opcode <=> is_terminator i.inst_opcode) /\
    ((h i).inst_opcode = PHI <=> i.inst_opcode = PHI)) ==>
  bb_well_formed (bb with bb_instructions := MAP h bb.bb_instructions)
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `is_terminator (h (LAST bb.bb_instructions)).inst_opcode` by
    (first_x_assum (qspec_then `LAST bb.bb_instructions` mp_tac) >>
     simp[LAST_MEM] >> gvs[bb_well_formed_def]) >>
  gvs[bb_well_formed_def, LAST_MAP, EL_MAP, EVERY_MEM] >>
  conj_tac
  >- (rpt strip_tac >> gvs[EL_MAP] >>
      `MEM (EL i bb.bb_instructions) bb.bb_instructions` by
        metis_tac[MEM_EL] >>
      first_x_assum drule >> strip_tac >>
      gvs[] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> gvs[EL_MAP] >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions /\
   MEM (EL j bb.bb_instructions) bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  metis_tac[]
QED

Theorem phi_subst_bb_well_formed:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAP (\i. if i.inst_opcode <> PHI then i else subst_label_inst a b i)
      bb.bb_instructions)
Proof
  strip_tac >> irule map_bb_well_formed >> simp[] >>
  rw[subst_label_inst_def]
QED

Theorem update_phi_bypass_bb_well_formed:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAP (update_phi_bypass a b) bb.bb_instructions)
Proof
  strip_tac >> irule map_bb_well_formed >> simp[update_phi_bypass_opcode]
QED

Theorem canon_jnz_inst_classification:
  (is_terminator (canon_jnz_inst i).inst_opcode <=>
   is_terminator i.inst_opcode) /\
  ((canon_jnz_inst i).inst_opcode = PHI <=> i.inst_opcode = PHI)
Proof
  Cases_on `canon_jnz_inst i = i` >- simp[] >>
  drule canon_jnz_inst_changed >>
  simp[is_terminator_def] >> strip_tac >> gvs[is_terminator_def]
QED

Theorem bypass_terminator_bb_well_formed:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAP (\i. if ~is_terminator i.inst_opcode then i
      else canon_jnz_inst (subst_label_inst a b i)) bb.bb_instructions)
Proof
  strip_tac >> irule map_bb_well_formed >> simp[] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  simp[canon_jnz_inst_classification, subst_label_inst_def]
QED

Theorem remove_unreachable_blocks_bb_well_formed:
  EVERY bb_well_formed f.fn_blocks ==>
  EVERY bb_well_formed (remove_unreachable_blocks f).fn_blocks
Proof
  Cases_on `fn_entry_label f` >>
  simp[remove_unreachable_blocks_def, EVERY_MEM, MEM_FILTER]
QED

Theorem update_succ_phi_labels_bb_well_formed:
  !succs bbs.
    EVERY bb_well_formed bbs ==>
    EVERY bb_well_formed (update_succ_phi_labels a b bbs succs)
Proof
  Induct >> simp[update_succ_phi_labels_def] >> rpt strip_tac >>
  qpat_x_assum `!bbs. _` (mp_tac o REWRITE_RULE [update_succ_phi_labels_def]) >>
  Cases_on `lookup_block h bbs` >> simp[] >> disch_then irule >>
  irule replace_block_every >> simp[] >>
  irule phi_subst_bb_well_formed >>
  drule lookup_block_member_label >> strip_tac >>
  gvs[EVERY_MEM] >> first_x_assum irule >> simp[]
QED

Theorem do_merge_jump_bb_well_formed:
  EVERY bb_well_formed f.fn_blocks /\ bb_well_formed a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  EVERY bb_well_formed g.fn_blocks
Proof
  simp[do_merge_jump_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  irule replace_block_every >> reverse conj_tac
  >- (irule replace_block_every >> reverse conj_tac
      >- (irule remove_block_every >> simp[]) >>
      irule update_phi_bypass_bb_well_formed >>
      drule lookup_block_member_label >> strip_tac >>
      gvs[EVERY_MEM] >> first_x_assum irule >> simp[]) >>
  IF_CASES_TAC >> simp[]
  >- (qmatch_goalsub_abbrev_tac `MAP _ insts` >>
      `bb_well_formed (a with bb_instructions := insts)` by
        (unabbrev_all_tac >> irule bypass_terminator_bb_well_formed >> simp[]) >>
      drule update_phi_bypass_bb_well_formed >> simp[]) >>
  irule bypass_terminator_bb_well_formed >> simp[]
QED

Theorem bb_well_formed_front:
  bb_well_formed bb ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)
Proof
  simp[bb_well_formed_def, EVERY_EL] >> rpt strip_tac >>
  gvs[EL_FRONT, NULL_EQ, LENGTH_FRONT] >>
  `n < LENGTH bb.bb_instructions` by decide_tac >>
  qpat_x_assum `!i. _ /\ _ ==> _` drule >> simp[] >> decide_tac
QED

Theorem append_no_phi_bb_well_formed:
  bb_well_formed a /\ bb_well_formed b /\ no_phis b ==>
  bb_well_formed (a with bb_instructions :=
    FRONT a.bb_instructions ++ b.bb_instructions)
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT a.bb_instructions)` by
    (irule bb_well_formed_front >> simp[]) >>
  rule_assum_tac (REWRITE_RULE [bb_well_formed_def, no_phis_def, EVERY_EL]) >>
  POP_ASSUM_LIST (map_every strip_assume_tac) >>
  simp_tac (srw_ss()) [bb_well_formed_def, LAST_APPEND] >>
  conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (Cases_on `b.bb_instructions`
      >- gvs[] >>
      pure_rewrite_tac[LAST_APPEND] >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "terminal" >> suspend "phi_prefix"
QED

Resume append_no_phi_bb_well_formed[terminal]:
  rpt strip_tac >> Cases_on `i < LENGTH (FRONT a.bb_instructions)`
      >- (qpat_assum `i < LENGTH (FRONT _)` (fn th =>
            qpat_x_assum `is_terminator (EL _ (_ ++ _)).inst_opcode`
              (assume_tac o REWRITE_RULE [EL_APPEND_EQN, th])) >>
          qpat_x_assum `!n. n < LENGTH (FRONT _) ==> _`
            (qspec_then `i` mp_tac) >>
          simp_tac std_ss [] >> metis_tac[]) >>
      qpat_assum `~(i < LENGTH (FRONT _))` (fn th =>
        qpat_x_assum `is_terminator (EL _ (_ ++ _)).inst_opcode`
          (assume_tac o REWRITE_RULE [EL_APPEND_EQN, th])) >>
      `i - LENGTH (FRONT a.bb_instructions) < LENGTH b.bb_instructions`
        by decide_tac >>
      qpat_x_assum `!i. i < LENGTH b.bb_instructions /\ _ ==> _`
        (qspec_then `i - LENGTH (FRONT a.bb_instructions)` mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      `0 < LENGTH b.bb_instructions` by
        (Cases_on `b.bb_instructions` >> gvs[]) >> decide_tac
QED

Resume append_no_phi_bb_well_formed[phi_prefix]:
  rpt strip_tac >> Cases_on `j < LENGTH (FRONT a.bb_instructions)`
  >- (`i < LENGTH (FRONT a.bb_instructions)` by decide_tac >>
      `LENGTH (FRONT a.bb_instructions) <= LENGTH a.bb_instructions` by
        (Cases_on `a.bb_instructions` >> simp_tac (srw_ss()) [LENGTH_FRONT]) >>
      `j < LENGTH a.bb_instructions /\ i < LENGTH a.bb_instructions` by
        decide_tac >>
      qpat_assum `j < LENGTH (FRONT _)` (fn th =>
        qpat_x_assum `(EL j (_ ++ _)).inst_opcode = PHI`
          (assume_tac o REWRITE_RULE [EL_APPEND_EQN, th])) >>
      `~NULL a.bb_instructions` by
        (pure_rewrite_tac[NULL_EQ] >> first_assum ACCEPT_TAC) >>
      qpat_assum `~NULL _` (fn th =>
        qpat_assum `j < LENGTH (FRONT _)` (fn bound =>
          qpat_x_assum `(EL j (FRONT _)).inst_opcode = PHI`
            (assume_tac o SIMP_RULE std_ss [EL_FRONT, th, bound]))) >>
      qpat_assum `i < LENGTH (FRONT _)` (fn th =>
        pure_rewrite_tac[EL_APPEND_EQN, th]) >>
      `EL i (FRONT a.bb_instructions) = EL i a.bb_instructions` by
        (irule EL_FRONT >> simp[]) >>
      pop_assum SUBST1_TAC >>
      qpat_x_assum `!i j. _ ==> (EL i a.bb_instructions).inst_opcode = PHI`
        (qspecl_then [`i`,`j`] mp_tac) >>
      metis_tac[]) >>
  `j - LENGTH (FRONT a.bb_instructions) < LENGTH b.bb_instructions`
    by decide_tac >>
  qpat_assum `~(j < LENGTH (FRONT _))` (fn th =>
    qpat_x_assum `(EL j (_ ++ _)).inst_opcode = PHI`
      (assume_tac o REWRITE_RULE [EL_APPEND_EQN, th])) >>
  qpat_x_assum `!n. n < LENGTH b.bb_instructions ==> _`
    (qspec_then `j - LENGTH (FRONT a.bb_instructions)` mp_tac) >>
  simp_tac bool_ss [] >> metis_tac[]
QED

Finalise append_no_phi_bb_well_formed

Theorem merge_blocks_bb_well_formed:
  bb_well_formed a /\ bb_well_formed b /\ no_phis b ==>
  bb_well_formed (merge_blocks a b)
Proof
  simp[merge_blocks_def, append_no_phi_bb_well_formed]
QED

Theorem chain_merge_bb_well_formed:
  EVERY bb_well_formed f.fn_blocks /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  EVERY bb_well_formed
    (update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))
Proof
  strip_tac >> irule update_succ_phi_labels_bb_well_formed >>
  irule replace_block_every >> reverse conj_tac
  >- (irule remove_block_every >> simp[]) >>
  irule merge_blocks_bb_well_formed >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  gvs[EVERY_MEM, can_merge_blocks_def]
QED

Theorem partition_terminal_bb_well_formed:
  EVERY (\i. ~is_terminator i.inst_opcode) (ps ++ ns) /\
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) ns /\
  is_terminator t.inst_opcode /\ t.inst_opcode <> PHI ==>
  bb_well_formed (bb with bb_instructions := ps ++ ns ++ [t])
Proof
  strip_tac >>
  simp_tac (srw_ss()) [bb_well_formed_def, LAST_APPEND, EL_APPEND_EQN] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "terminal" >> suspend "phi_prefix"
QED

Resume partition_terminal_bb_well_formed[terminal]:
  rpt strip_tac >> Cases_on `i < LENGTH ps + LENGTH ns`
  >- (qpat_x_assum `EVERY _ (ps ++ ns)` mp_tac >>
      simp_tac bool_ss [EVERY_EL] >>
      disch_then (qspec_then `i` mp_tac) >>
      gvs[EL_APPEND_EQN]) >> decide_tac
QED

Resume partition_terminal_bb_well_formed[phi_prefix]:
  rpt strip_tac >> Cases_on `j < LENGTH ps`
  >- (`i < LENGTH ps /\ i < LENGTH ps + LENGTH ns` by decide_tac >>
      gvs[EVERY_EL]) >>
  Cases_on `j < LENGTH ps + LENGTH ns`
  >- (`j - LENGTH ps < LENGTH ns` by decide_tac >>
      qpat_x_assum `EVERY _ ns` mp_tac >>
      simp_tac bool_ss [EVERY_EL] >>
      disch_then (qspec_then `j - LENGTH ps` mp_tac) >> gvs[]) >>
  `j - (LENGTH ps + LENGTH ns) = 0` by decide_tac >> gvs[]
QED

Finalise partition_terminal_bb_well_formed

Theorem fix_phi_inst_nonterminator:
  ~is_terminator i.inst_opcode ==>
  ~is_terminator (fix_phi_inst actual_preds i).inst_opcode
Proof
  strip_tac >>
  Cases_on `(fix_phi_inst actual_preds i).inst_opcode = NOP` >>
  simp[is_terminator_def] >>
  Cases_on `(fix_phi_inst actual_preds i).inst_opcode = ASSIGN` >>
  simp[is_terminator_def] >>
  metis_tac[fix_phi_inst_opcode_source]
QED

Theorem fix_phis_in_block_bb_well_formed:
  bb_well_formed bb ==> bb_well_formed (fix_phis_in_block actual_preds bb)
Proof
  strip_tac >> drule bb_well_formed_front >> strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  drule fix_phi_inst_terminator >> strip_tac >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
    metis_tac[APPEND_FRONT_LAST] >>
  simp[fix_phis_in_block_def] >>
  qpat_assum `bb.bb_instructions = _ ++ _` (fn th =>
    once_rewrite_tac[th]) >>
  simp[MAP_APPEND, FILTER_APPEND] >>
  irule partition_terminal_bb_well_formed >>
  `~is_terminator PHI` by simp[is_terminator_def] >>
  simp[EVERY_FILTER, EVERY_MEM, MEM_FILTER, EVERY_MAP] >>
  rpt strip_tac >>
  `~is_terminator x.inst_opcode` by
    (qpat_x_assum `EVERY _ (FRONT _)` mp_tac >> simp[EVERY_MEM]) >>
  metis_tac[fix_phi_inst_nonterminator]
QED

Theorem fix_all_phis_bb_well_formed:
  EVERY bb_well_formed f.fn_blocks ==>
  EVERY bb_well_formed (fix_all_phis f).fn_blocks
Proof
  simp[fix_all_phis_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  metis_tac[fix_phis_in_block_bb_well_formed]
QED

Theorem phi_subst_inst_wf:
  i.inst_opcode = PHI /\ inst_wf i ==>
  inst_wf (subst_label_inst a b i)
Proof
  strip_tac >> gvs[subst_label_inst_def, inst_wf_def,
    phi_well_formed_subst_label]
QED

Theorem phi_subst_label_positions:
  i.inst_opcode = PHI ==>
  label_positions_ok (subst_label_inst a b i)
Proof
  strip_tac >> simp[subst_label_inst_def,
    unitShapeDefsTheory.label_positions_ok_def]
QED

Theorem bypass_terminator_wf:
  is_terminator i.inst_opcode /\ inst_wf i /\ label_positions_ok i ==>
  inst_wf (canon_jnz_inst (subst_label_inst a b i))
Proof
  strip_tac >> irule canon_jnz_inst_wf >>
  Cases_on `i.inst_opcode = JMP`
  >- (gvs[inst_wf_def] >>
      simp[subst_label_inst_def, subst_label_op_def, inst_wf_def] >>
      IF_CASES_TAC >> simp[]) >>
  Cases_on `i.inst_opcode = JNZ`
  >- (gvs[inst_wf_def] >>
      simp[subst_label_inst_def, subst_label_op_def, inst_wf_def] >>
      rpt IF_CASES_TAC >> simp[]) >>
  `EVERY (\op. ~is_label_operand op) i.inst_operands` by
    (Cases_on `i.inst_opcode` >>
     gvs[is_terminator_def, unitShapeDefsTheory.label_positions_ok_def]) >>
  metis_tac[subst_label_inst_no_label_operands]
QED

Theorem chain_merge_inst_wf:
  EVERY inst_wf (fn_insts f) /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b ==>
  EVERY inst_wf (fn_insts (f with fn_blocks :=
    update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b))))
Proof
  strip_tac >> irule chain_merge_every >> simp[phi_subst_inst_wf] >>
  metis_tac[]
QED

Theorem chain_merge_label_positions:
  EVERY label_positions_ok (fn_insts f) /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b ==>
  EVERY label_positions_ok (fn_insts (f with fn_blocks :=
    update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b))))
Proof
  strip_tac >> irule chain_merge_every >> simp[phi_subst_label_positions] >>
  metis_tac[]
QED

Theorem do_merge_jump_instruction_shape:
  EVERY inst_wf (fn_insts f) /\
  EVERY label_positions_ok (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  EVERY (\i. inst_wf i /\ label_positions_ok i) (fn_insts g)
Proof
  strip_tac >> irule do_merge_jump_every >>
  simp[EVERY_MEM] >>
  metis_tac[bypass_terminator_wf, bypass_terminator_label_positions,
    update_phi_bypass_wf, update_phi_bypass_label_positions, EVERY_MEM]
QED

Theorem do_merge_jump_inst_wf:
  EVERY inst_wf (fn_insts f) /\
  EVERY label_positions_ok (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  EVERY inst_wf (fn_insts g)
Proof
  strip_tac >> drule_all do_merge_jump_instruction_shape >>
  simp[EVERY_MEM]
QED

Theorem do_merge_jump_label_positions:
  EVERY inst_wf (fn_insts f) /\
  EVERY label_positions_ok (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  EVERY label_positions_ok (fn_insts g)
Proof
  strip_tac >> drule_all do_merge_jump_instruction_shape >>
  simp[EVERY_MEM]
QED

Theorem fix_all_phis_inst_wf:
  EVERY inst_wf (fn_insts f) ==>
  EVERY inst_wf (fn_insts (fix_all_phis f))
Proof
  strip_tac >> irule fix_all_phis_every >> simp[fix_phi_inst_wf]
QED

Theorem fix_all_phis_instruction_shape:
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) ==>
  EVERY (\i. inst_wf i /\ label_positions_ok i) (fn_insts (fix_all_phis f))
Proof
  strip_tac >> irule fix_all_phis_every >>
  simp[EVERY_MEM] >> metis_tac[fix_phi_inst_wf, fix_phi_inst_label_positions,
    EVERY_MEM]
QED

Theorem fix_all_phis_label_positions:
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) ==>
  EVERY label_positions_ok (fn_insts (fix_all_phis f))
Proof
  strip_tac >> drule_all fix_all_phis_instruction_shape >> simp[EVERY_MEM]
QED
