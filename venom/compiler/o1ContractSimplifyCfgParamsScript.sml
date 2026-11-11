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
  o1PassContract simplifyCfgCollapseShape simplifyCfgGraphShape
  simplifyCfgInvariant simplifyCfgDefs unitShapeDefs callLayoutDefs
  venomWf venomInst cfgTransform list rich_list arithmetic

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
  !bb h e.
  (!i. MEM i bb.bb_instructions ==>
       (is_param_opcode (h i).inst_opcode <=> is_param_opcode i.inst_opcode) /\
       ((h i).inst_opcode = PHI <=> i.inst_opcode = PHI)) /\
  pseudos_prefix bb /\
  (bb.bb_label <> e ==> no_param_insts bb.bb_instructions) /\
  (bb.bb_label = e ==> no_phis bb) ==>
  pseudos_prefix (bb with bb_instructions := MAP h bb.bb_instructions) /\
  (bb.bb_label <> e ==> no_param_insts (MAP h bb.bb_instructions)) /\
  (bb.bb_label = e ==>
     no_phis (bb with bb_instructions := MAP h bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule scfg_pseudos_prefix_map >> simp[scfg_pseudo_classification] >>
      metis_tac[]) >>
  gvs[no_param_insts_def, no_phis_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem scfg_update_succ_layout[local]:
  EVERY (^block_param_layout e) bbs ==>
  EVERY (^block_param_layout e) (update_succ_phi_labels old new bbs succs)
Proof
  strip_tac >> irule scfg_update_succ_block_predicate >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> simp[] >>
  irule scfg_block_layout_map >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `i.inst_opcode = PHI` >>
  simp[subst_label_inst_def]
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
    (gvs[] >> drule_all can_merge_blocks_not_entry >> simp[]) >>
  gvs[scfg_layout_blocks_iff] >>
  irule (BETA_RULE scfg_update_succ_layout) >> irule replace_block_every >>
  conj_tac
  >- (BETA_TAC >> irule scfg_merge_block_layout >>
      gvs[can_merge_blocks_def, EVERY_MEM] >> metis_tac[]) >>
  irule remove_block_every >> simp[]
QED

Theorem scfg_bypass_layout[local]:
  ^param_layout e f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  ^param_layout e g
Proof
  rewrite_tac[scfg_layout_blocks_iff] >> BETA_TAC >> strip_tac >>
  `MEM a f.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `!i. (update_phi_bypass a.bb_label b.bb_label i).inst_opcode =
       i.inst_opcode` by rw[update_phi_bypass_def] >>
  `!l1 l2 i. (is_param_opcode
       (canon_jnz_inst (subst_label_inst l1 l2 i)).inst_opcode <=>
       is_param_opcode i.inst_opcode) /\
     ((canon_jnz_inst (subst_label_inst l1 l2 i)).inst_opcode = PHI <=>
       i.inst_opcode = PHI)` by
    (rpt gen_tac >> simp[canon_jnz_inst_def, subst_label_inst_def] >>
     BasicProvers.every_case_tac >> rw[] >> gvs[is_param_opcode_def]) >>
  qpat_x_assum `do_merge_jump _ _ _ _ = _` mp_tac >>
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `MEM target f.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `pseudos_prefix target /\
   (target.bb_label <> e ==> no_param_insts target.bb_instructions) /\
   (target.bb_label = e ==> no_phis target)` by gvs[EVERY_MEM] >>
  `pseudos_prefix a /\
   (a.bb_label <> e ==> no_param_insts a.bb_instructions) /\
   (a.bb_label = e ==> no_phis a)` by gvs[EVERY_MEM] >>
  qmatch_goalsub_abbrev_tac `replace_block a.bb_label a1 _` >>
  `pseudos_prefix a1 /\
   (a1.bb_label <> e ==> no_param_insts a1.bb_instructions) /\
   (a1.bb_label = e ==> no_phis a1)` by
    (qunabbrev_tac `a1` >>
     Cases_on `target_lbl = a.bb_label` >> simp[]
     >- (qmatch_goalsub_abbrev_tac `MAP h a.bb_instructions` >>
         `pseudos_prefix (a with bb_instructions := MAP h a.bb_instructions) /\
          (a.bb_label <> e ==> no_param_insts (MAP h a.bb_instructions)) /\
          (a.bb_label = e ==>
            no_phis (a with bb_instructions := MAP h a.bb_instructions))` by
           (irule scfg_block_layout_map >> simp[Abbr `h`] >> rw[]) >>
         qspecl_then [`a with bb_instructions := MAP h a.bb_instructions`,
           `update_phi_bypass a.bb_label b.bb_label`, `e`]
           mp_tac scfg_block_layout_map >>
         simp[] >> rpt strip_tac >> gvs[Abbr `h`]) >>
     qmatch_goalsub_abbrev_tac `MAP h a.bb_instructions` >>
     irule scfg_block_layout_map >> simp[Abbr `h`] >> rw[]) >>
  irule replace_block_every >> conj_tac >- simp[] >>
  irule replace_block_every >> reverse conj_tac
  >- (irule remove_block_every >> simp[]) >>
  qspecl_then [`target`, `update_phi_bypass a.bb_label b.bb_label`, `e`]
    mp_tac scfg_block_layout_map >>
  simp[]
QED

(* Proof notation copied from simplifyCfgCollapseShapeScript.sml. *)
val collapse_shape = ``\e f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  first_block_no_preds f /\ fn_succs_closed f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) /\
  (HD f.fn_blocks).bb_label = e``;

val structural_shape = ``\e f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  first_block_no_preds f /\ fn_succs_closed f /\
  (HD f.fn_blocks).bb_label = e``;

val iteration_shape = ``\e f. ^structural_shape e f /\ fn_label_refs_ok f /\
  EVERY (\i. i.inst_opcode <> PHI) (HD f.fn_blocks).bb_instructions``;

Theorem scfg_collapse_layout[local]:
  !f lm vis lbl. ^collapse_shape e f /\ ^param_layout e f ==>
    ^param_layout e (FST (collapse_dfs f lm vis lbl))
Proof
  mp_tac (Q.INST [`Q` |-> `\f. ^collapse_shape e f /\ ^param_layout e f`]
    collapse_dfs_preserves_predicate) >>
  reverse impl_tac
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (qspecl_then [`f`, `lm`, `vis`, `lbl`] mp_tac) >>
      simp[]) >>
  conj_tac >>
  rpt gen_tac >> BETA_TAC >> strip_tac
  >- (drule_all (BETA_RULE do_merge_jump_collapse_shape) >> strip_tac >>
      drule_all (BETA_RULE scfg_bypass_layout) >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all (BETA_RULE chain_merge_collapse_shape) >> strip_tac >>
  drule_all (BETA_RULE scfg_chain_merge_layout) >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem scfg_round_layout[local]:
  ^structural_shape e f /\ ^param_layout e f ==>
  ^param_layout e (FST (simplify_cfg_round_with_labels f))
Proof
  strip_tac >>
  `^structural_shape e (remove_unreachable_blocks f)` by
    (irule remove_unreachable_blocks_structural_shape >> simp[]) >>
  `^collapse_shape e (fix_all_phis (remove_unreachable_blocks f))` by
    (irule fix_all_phis_collapse_shape >> simp[]) >>
  `^param_layout e (fix_all_phis (remove_unreachable_blocks f))` by
    (irule scfg_fix_all_phis_layout >> irule scfg_remove_unreachable_layout >>
     simp[]) >>
  Cases_on `fn_entry_label f`
  >- gvs[simplify_cfg_round_with_labels_def] >>
  Cases_on `collapse_dfs (fix_all_phis (remove_unreachable_blocks f)) [] [] x` >>
  PairCases_on `r` >>
  `^param_layout e q` by
    (`q = FST (collapse_dfs (fix_all_phis (remove_unreachable_blocks f))
        [] [] x)` by simp[] >>
     pop_assum SUBST1_TAC >> irule scfg_collapse_layout >> simp[]) >>
  `^param_layout e (subst_block_labels_fn r0 q)` by
    (irule scfg_subst_labels_layout >> first_assum ACCEPT_TAC) >>
  `^param_layout e (if r0 = [] then q else subst_block_labels_fn r0 q)` by
    (Cases_on `r0 = []` >> gvs[]) >>
  `^param_layout e (fix_all_phis (remove_unreachable_blocks
     (if r0 = [] then q else subst_block_labels_fn r0 q)))` by
    (irule scfg_fix_all_phis_layout >> irule scfg_remove_unreachable_layout >>
     first_assum ACCEPT_TAC) >>
  gvs[simplify_cfg_round_with_labels_def]
QED

Theorem scfg_iter_layout[local]:
  !n f. ^iteration_shape e f /\ ^param_layout e f ==>
    ^param_layout e (FST (simplify_cfg_iter_with_labels n f))
Proof
  Induct_on `n` >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  `^structural_shape e f` by gvs[] >>
  `^iteration_shape e (FST (simplify_cfg_round_with_labels f))` by
    (drule simplify_cfg_round_collapse_shape >> strip_tac >>
     drule simplify_cfg_round_label_refs_ok >> strip_tac >> gvs[]) >>
  `^param_layout e (FST (simplify_cfg_round_with_labels f))` by
    (irule scfg_round_layout >> simp[]) >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  Cases_on `simplify_cfg_round_with_labels f` >> simp[] >>
  Cases_on `q.fn_blocks = f.fn_blocks` >- gvs[] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> simp[] >>
  first_x_assum (qspec_then `q` mp_tac) >> gvs[]
QED

Theorem simplify_cfg_fn_param_prefix:
  o1_fn_shape C fn /\ fn_pseudos_prefix fn /\
  EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks) ==>
  fn_pseudos_prefix (simplify_cfg_fn fn) /\
  EVERY (\bb. no_param_insts bb.bb_instructions)
    (TL (simplify_cfg_fn fn).fn_blocks)
Proof
  strip_tac >>
  `^iteration_shape (HD fn.fn_blocks).bb_label fn` by
    (BETA_TAC >>
     gvs[o1_fn_shape_def, wf_function_def, fn_has_entry_def,
         fn_inst_wf_def, fn_shape_ok_def, inst_shape_ok_def,
         first_block_no_phi_def, EVERY_MEM, fn_insts_def,
         fn_insts_blocks_MEM] >> metis_tac[]) >>
  `first_block_no_phi fn` by gvs[o1_fn_shape_def] >>
  mp_tac (Q.INST [`e` |-> `(HD fn.fn_blocks).bb_label`]
    scfg_entry_layout_iff) >>
  impl_tac >- gvs[] >> strip_tac >>
  `^param_layout (HD fn.fn_blocks).bb_label fn` by (BETA_TAC >> gvs[]) >>
  `^iteration_shape (HD fn.fn_blocks).bb_label
     (FST (simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn))` by
    (irule simplify_cfg_iter_structural_shape >> simp[]) >>
  `^param_layout (HD fn.fn_blocks).bb_label
     (FST (simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn))` by
    (irule scfg_iter_layout >> simp[]) >>
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  qabbrev_tac `g = FST (simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn)` >>
  mp_tac (Q.INST [`e` |-> `(HD fn.fn_blocks).bb_label`, `fn` |-> `g`]
    scfg_entry_layout_iff) >>
  impl_tac >- gvs[] >> strip_tac >> gvs[]
QED
