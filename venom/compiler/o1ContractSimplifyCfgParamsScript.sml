(*
 * SimplifyCFG keeps the parameter layout the O1 function row asks for
 * from stage 4 on: pseudo instructions (PHIs and parameters) lead every
 * block, and only the first block has parameters.
 *
 * TOP-LEVEL:
 *   simplify_cfg_fn_param_prefix
 *)
Theory o1ContractSimplifyCfgParams
Ancestors
  o1PassContract simplifyCfgCollapseShape simplifyCfgInvariant
  simplifyCfgDefs callLayoutDefs venomWf venomInst cfgTransform
  list rich_list arithmetic

(* Why it holds (intuition, not a prescribed proof).

   The first block keeps its label and stays first: it has no
   predecessors (first_block_no_preds), so neither a chain merge nor a
   jump bypass removes it, and it is reachable, so unreachable-block
   removal keeps it.  It has no PHI (first_block_no_phi), so the PHI
   fixup leaves it alone, and a chain merge into it appends a block with
   no PHI (can_merge_blocks) and, being a non-first block, no parameter,
   after FRONT of a pseudo-prefixed list.  Every other block has no
   parameter: chain merges and bypasses only rewrite operands and turn a
   JNZ into a JMP, so they keep every opcode except at the merged block,
   and the PHI fixup puts the remaining PHIs first (fix_phis_in_block),
   so with no parameters its pseudos are exactly its leading PHIs.  The
   block-label substitution leaves bb_label and opcodes alone. *)
Theorem scfg_entry_layout_iff[local]:
  fn.fn_blocks <> [] /\ ALL_DISTINCT (fn_labels fn) /\
  (HD fn.fn_blocks).bb_label = e ==>
  ((EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks) <=>
    EVERY (\bb. bb.bb_label <> e ==> no_param_insts bb.bb_instructions)
      fn.fn_blocks) /\
   (first_block_no_phi fn <=>
    EVERY (\bb. bb.bb_label = e ==>
      EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) fn.fn_blocks))
Proof
  Cases_on `fn.fn_blocks` >> simp[fn_labels_def, first_block_no_phi_def] >>
  rpt strip_tac >> gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem scfg_pseudos_prefix_map[local]:
  (!i. MEM i bb.bb_instructions ==>
       (is_pseudo (f i).inst_opcode <=> is_pseudo i.inst_opcode)) /\
  pseudos_prefix bb ==>
  pseudos_prefix (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  simp[pseudos_prefix_def, EL_MAP] >> rpt strip_tac >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions /\
   MEM (EL j bb.bb_instructions) bb.bb_instructions` by
    simp[EL_MEM] >>
  gvs[EL_MAP] >> metis_tac[]
QED

Theorem scfg_pseudos_prefix_merge[local]:
  pseudos_prefix a /\
  EVERY (\i. ~is_pseudo i.inst_opcode) b.bb_instructions ==>
  pseudos_prefix (merge_blocks a b)
Proof
  simp[pseudos_prefix_def, merge_blocks_def] >> rpt strip_tac >>
  Cases_on `j < LENGTH (FRONT a.bb_instructions)`
  >- (`i < LENGTH (FRONT a.bb_instructions)` by decide_tac >>
      `a.bb_instructions <> []` by
        (Cases_on `a.bb_instructions` >> gvs[]) >>
      `j < LENGTH a.bb_instructions` by
        (gvs[LENGTH_FRONT] >> decide_tac) >>
      `EL i (FRONT a.bb_instructions) = EL i a.bb_instructions` by
        (irule EL_FRONT >> simp[NULL_EQ]) >>
      `EL j (FRONT a.bb_instructions) = EL j a.bb_instructions` by
        (irule EL_FRONT >> simp[NULL_EQ]) >>
      gvs[EL_APPEND_EQN] >> metis_tac[]) >>
  gvs[EL_APPEND_EQN, EVERY_EL] >>
  `j - LENGTH (FRONT a.bb_instructions) < LENGTH b.bb_instructions` by
    decide_tac >> metis_tac[]
QED

Theorem scfg_fix_phis_no_phis[local]:
  no_phis bb ==> fix_phis_in_block ps bb = bb
Proof
  simp[no_phis_def, fix_phis_in_block_def] >> strip_tac >>
  `MAP (fix_phi_inst ps) bb.bb_instructions = bb.bb_instructions` by
    (`MAP (fix_phi_inst ps) bb.bb_instructions = MAP I bb.bb_instructions`
       suffices_by simp[] >>
     irule MAP_CONG >> simp[] >> gvs[EVERY_MEM] >>
     rpt strip_tac >> simp[fix_phi_inst_def]) >>
  simp[] >>
  `FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions = []` by
    gvs[FILTER_EQ_NIL, EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode <> PHI) bb.bb_instructions = bb.bb_instructions` by
    gvs[FILTER_EQ_ID] >> simp[]
QED

Theorem scfg_pseudo_classification[local]:
  is_pseudo op <=> op = PHI \/ is_param_opcode op
Proof
  Cases_on `op` >> simp[is_pseudo_def, is_param_opcode_def]
QED

Theorem scfg_fix_phi_no_param[local]:
  ~is_param_opcode i.inst_opcode ==>
  ~is_param_opcode (fix_phi_inst ps i).inst_opcode
Proof
  simp[fix_phi_inst_def] >> strip_tac >>
  Cases_on `i.inst_opcode = PHI` >> simp[] >>
  Cases_on `filter_phi_ops ps i.inst_operands` >>
  simp[is_param_opcode_def] >>
  rename1 `h::t` >> Cases_on `t` >> simp[is_param_opcode_def] >>
  rename1 `h'::t'` >> Cases_on `t'` >> simp[is_param_opcode_def]
QED

Theorem scfg_fix_phis_layout[local]:
  no_param_insts bb.bb_instructions ==>
  no_param_insts (fix_phis_in_block ps bb).bb_instructions /\
  pseudos_prefix (fix_phis_in_block ps bb)
Proof
  strip_tac >>
  `EVERY (\i. ~is_param_opcode i.inst_opcode)
    (MAP (fix_phi_inst ps) bb.bb_instructions)` by
    (gvs[no_param_insts_def, EVERY_MAP, EVERY_MEM] >>
     metis_tac[scfg_fix_phi_no_param]) >>
  conj_tac
  >- (simp[fix_phis_in_block_def, no_param_insts_def, EVERY_FILTER,
           EVERY_MEM, MEM_FILTER] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[fix_phis_in_block_def, pseudos_prefix_def] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `phis ++ others` >>
  `EVERY (\i. i.inst_opcode = PHI) phis` by
    simp[Abbr `phis`, EVERY_FILTER, EVERY_MEM, MEM_FILTER] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) others` by
    (simp[Abbr `others`, EVERY_MEM, MEM_FILTER, scfg_pseudo_classification] >>
     gvs[EVERY_MEM]) >>
  Cases_on `j < LENGTH phis`
  >- (`i < LENGTH phis` by decide_tac >>
      gvs[EL_APPEND_EQN, EVERY_EL] >> simp[scfg_pseudo_classification]) >>
  `j - LENGTH phis < LENGTH others` by decide_tac >>
  gvs[EL_APPEND_EQN, EVERY_EL]
QED

(* Proof notation, expanded in theorems rather than a logical definition. *)
val param_layout = ``\e f.
  fn_pseudos_prefix f /\
  EVERY (\bb. bb.bb_label <> e ==> no_param_insts bb.bb_instructions) f.fn_blocks /\
  EVERY (\bb. bb.bb_label = e ==>
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) f.fn_blocks``;

Theorem scfg_remove_unreachable_layout[local]:
  ^param_layout e f ==> ^param_layout e (remove_unreachable_blocks f)
Proof
  BETA_TAC >> simp[remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label f` >>
  simp[fn_pseudos_prefix_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem scfg_fix_all_phis_layout[local]:
  ^param_layout e f ==> ^param_layout e (fix_all_phis f)
Proof
  BETA_TAC >> simp[fix_all_phis_def, fn_pseudos_prefix_def,
                  EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> gvs[] >> Cases_on `bb'.bb_label = e`
      >- (`no_phis bb'` by (simp[no_phis_def, EVERY_MEM] >> metis_tac[]) >>
          drule scfg_fix_phis_no_phis >> simp[]) >>
      irule (cj 2 scfg_fix_phis_layout) >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `bb'.bb_label <> e` by gvs[fix_phis_in_block_def] >>
      gvs[] >> irule (cj 1 scfg_fix_phis_layout) >> metis_tac[]) >>
  rpt strip_tac >>
  `bb'.bb_label = e` by gvs[fix_phis_in_block_def] >>
  `no_phis bb'` by (simp[no_phis_def, EVERY_MEM] >> metis_tac[]) >>
  drule scfg_fix_phis_no_phis >> strip_tac >> gvs[no_phis_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem scfg_subst_labels_layout[local]:
  ^param_layout e f ==> ^param_layout e (subst_block_labels_fn lm f)
Proof
  BETA_TAC >>
  `!i. (subst_block_labels_inst lm i).inst_opcode = i.inst_opcode` by
    (gen_tac >> simp[subst_block_labels_inst_def, subst_label_map_inst_def] >>
     Cases_on `is_block_label_opcode i.inst_opcode` >> simp[]) >>
  simp[subst_block_labels_fn_def, fn_pseudos_prefix_def, EVERY_MAP,
       EVERY_MEM, MEM_MAP] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> gvs[subst_block_labels_block_def] >>
      irule scfg_pseudos_prefix_map >> simp[] >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >>
  gvs[subst_block_labels_block_def, no_param_insts_def, EVERY_MAP,
      EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem scfg_update_succ_block_predicate[local]:
  (!bb old new.
    P bb ==> P (bb with bb_instructions :=
      MAP (\i. if i.inst_opcode <> PHI then i
               else subst_label_inst old new i) bb.bb_instructions)) ==>
  !succs bbs. EVERY P bbs ==>
    EVERY P (update_succ_phi_labels old new bbs succs)
Proof
  strip_tac >> Induct_on `succs` >>
  simp[update_succ_phi_labels_def] >> rpt strip_tac >>
  qpat_x_assum `!bbs. _` (mp_tac o SRULE [update_succ_phi_labels_def, LET_THM]) >>
  disch_then irule >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  irule replace_block_every >> simp[] >> first_x_assum irule >>
  drule lookup_block_member_label >> strip_tac >>
  gvs[EVERY_MEM]
QED

Theorem scfg_merge_block_layout[local]:
  pseudos_prefix a /\ no_phis b /\ no_param_insts b.bb_instructions /\
  (a.bb_label <> e ==> no_param_insts a.bb_instructions) /\
  (a.bb_label = e ==> no_phis a) ==>
  pseudos_prefix (merge_blocks a b) /\
  ((merge_blocks a b).bb_label <> e ==>
    no_param_insts (merge_blocks a b).bb_instructions) /\
  ((merge_blocks a b).bb_label = e ==> no_phis (merge_blocks a b))
Proof
  strip_tac >> conj_tac
  >- (irule scfg_pseudos_prefix_merge >>
      gvs[no_phis_def, no_param_insts_def, EVERY_MEM,
          scfg_pseudo_classification] >> metis_tac[]) >>
  simp[merge_blocks_def, no_param_insts_def, no_phis_def] >>
  conj_tac >> strip_tac >>
  gvs[no_param_insts_def, no_phis_def] >>
  qpat_x_assum `EVERY _ a.bb_instructions` mp_tac >>
  qspec_tac (`a.bb_instructions`, `xs`) >> Induct >> simp[] >>
  Cases_on `xs` >> gvs[]
QED

val block_param_layout = ``\e bb.
  pseudos_prefix bb /\
  (bb.bb_label <> e ==> no_param_insts bb.bb_instructions) /\
  (bb.bb_label = e ==> no_phis bb)``;

Theorem scfg_layout_blocks_iff[local]:
  ^param_layout e f <=> EVERY (^block_param_layout e) f.fn_blocks
Proof
  BETA_TAC >> simp[fn_pseudos_prefix_def, no_phis_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem scfg_block_layout_map[local]:
  (!i. MEM i bb.bb_instructions ==> (f i).inst_opcode = i.inst_opcode) /\
  ^block_param_layout e bb ==>
  ^block_param_layout e (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  BETA_TAC >> strip_tac >> conj_tac
  >- (irule scfg_pseudos_prefix_map >> simp[] >> metis_tac[]) >>
  gvs[no_param_insts_def, no_phis_def, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem scfg_update_succ_layout[local]:
  EVERY (^block_param_layout e) bbs ==>
  EVERY (^block_param_layout e) (update_succ_phi_labels old new bbs succs)
Proof
  strip_tac >> irule scfg_update_succ_block_predicate >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >> irule scfg_block_layout_map >>
  conj_tac >- (rpt strip_tac >> Cases_on `i.inst_opcode = PHI` >>
               simp[subst_label_inst_def]) >> (first_assum ACCEPT_TAC)
QED

Theorem scfg_chain_merge_layout[local]:
  f.fn_blocks <> [] /\ first_block_no_preds f /\
  (HD f.fn_blocks).bb_label = e /\ ^param_layout e f /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  ^param_layout e (f with fn_blocks := update_succ_phi_labels next lbl
    (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
    (bb_succs (merge_blocks a b)))
Proof
  strip_tac >>
  `a.bb_label = lbl /\ b.bb_label = next /\
   MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `b.bb_label <> e` by
    (drule_all can_merge_blocks_not_entry >> simp[]) >>
  gvs[scfg_layout_blocks_iff] >>
  irule scfg_update_succ_layout >> irule replace_block_every >> conj_tac
  >- (BETA_TAC >> irule scfg_merge_block_layout >>
      gvs[can_merge_blocks_def, EVERY_MEM] >> metis_tac[]) >>
  irule remove_block_every >> simp[]
QED

Theorem simplify_cfg_fn_param_prefix:
  o1_fn_shape C fn /\ fn_pseudos_prefix fn /\
  EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks) ==>
  fn_pseudos_prefix (simplify_cfg_fn fn) /\
  EVERY (\bb. no_param_insts bb.bb_instructions)
    (TL (simplify_cfg_fn fn).fn_blocks)
Proof
  cheat
QED
