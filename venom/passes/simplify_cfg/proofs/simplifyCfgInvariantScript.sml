(* Parametric preservation separates DFS control from instruction properties. *)
Theory simplifyCfgInvariant
Ancestors
  simplifyCfgDefs simplifyCfgShape cfgTransform venomInst ctxLookupAgreeHelpers list rich_list

Theorem try_bypass_preserves_predicate:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) ==>
  !succs f lm a.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a ==>
    Q (FST (try_bypass f lm a succs))
Proof
  strip_tac >> Induct_on `succs` >> simp[try_bypass_def] >>
  rpt gen_tac >> strip_tac >>
  simp[Once try_bypass_def] >>
  Cases_on `lookup_block h f.fn_blocks` >> simp[] >>
  rename1 `lookup_block h f.fn_blocks = SOME b` >>
  Cases_on `can_bypass_jump f a b` >> simp[] >>
  Cases_on `lookup_block (HD (bb_succs b)) f.fn_blocks` >> simp[] >>
  rename1 `lookup_block (HD (bb_succs b)) f.fn_blocks = SOME target` >>
  Cases_on `phi_values_agree a.bb_label b.bb_label target.bb_instructions` >>
  simp[] >>
  Cases_on `do_merge_jump f a b lm` >> simp[] >>
  PairCases_on `x` >> simp[] >> metis_tac[]
QED

Theorem collapse_dfs_preserves_predicate_joint:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) /\
  (!f lbl next a b.
    Q f /\ lookup_block lbl f.fn_blocks = SOME a /\
    lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
    Q (f with fn_blocks := update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))) ==>
  (!f lm vis lbl. Q f ==> Q (FST (collapse_dfs f lm vis lbl))) /\
  (!f lm vis succs. Q f ==> Q (FST (collapse_dfs_succs f lm vis succs)))
Proof
  strip_tac >> ho_match_mp_tac collapse_dfs_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      simp[NoAsms, Once collapse_dfs_def] >>
      Cases_on `lookup_block lbl f.fn_blocks` >> simp[] >>
      rename1 `lookup_block lbl f.fn_blocks = SOME bb` >>
      Cases_on `bb_succs bb`
      >- (gvs[try_bypass_def] >> Cases_on `MEM lbl vis` >> simp[] >>
          metis_tac[]) >>
      rename1 `bb_succs bb = next::rest` >> Cases_on `rest`
      >- (simp[] >> Cases_on `lookup_block next f.fn_blocks` >> simp[]
          >- (Cases_on `MEM lbl vis` >> simp[]) >>
          rename1 `lookup_block next f.fn_blocks = SOME b` >>
          Cases_on `can_merge_blocks f bb b`
          >- (gvs[] >> first_x_assum irule >> simp[] >>
              first_x_assum irule >> simp[] >> metis_tac[]) >>
          Cases_on `MEM lbl vis` >> simp[] >> gvs[]) >>
      `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
        metis_tac[lookup_block_member_label] >>
      `Q (FST (try_bypass f lm bb (next::h::t)))` by
        (irule try_bypass_preserves_predicate >> simp[] >> metis_tac[]) >>
      Cases_on `try_bypass f lm bb (next::h::t)` >>
      PairCases_on `r` >> Cases_on `r1` >> gvs[] >>
      Cases_on `MEM lbl vis` >> simp[] >> gvs[]) >>
  conj_tac
  >- simp[NoAsms, Once collapse_dfs_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs f lm vis lbl` >> PairCases_on `r` >> gvs[]
QED

Theorem collapse_dfs_preserves_predicate:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) /\
  (!f lbl next a b.
    Q f /\ lookup_block lbl f.fn_blocks = SOME a /\
    lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
    Q (f with fn_blocks := update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))) ==>
  !f lm vis lbl. Q f ==> Q (FST (collapse_dfs f lm vis lbl))
Proof
  strip_tac >> drule collapse_dfs_preserves_predicate_joint >> simp[]
QED

Theorem collapse_dfs_succs_preserves_predicate:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) /\
  (!f lbl next a b.
    Q f /\ lookup_block lbl f.fn_blocks = SOME a /\
    lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
    Q (f with fn_blocks := update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))) ==>
  !f lm vis succs. Q f ==> Q (FST (collapse_dfs_succs f lm vis succs))
Proof
  strip_tac >> drule collapse_dfs_preserves_predicate_joint >> simp[]
QED

Theorem remove_block_every:
  EVERY P bbs ==> EVERY P (remove_block lbl bbs)
Proof
  simp[remove_block_def, EVERY_MEM, MEM_FILTER]
QED

Theorem replace_block_every:
  EVERY P bbs /\ P bb ==> EVERY P (replace_block lbl bb bbs)
Proof
  simp[replace_block_def, EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
  gvs[] >> Cases_on `bb'.bb_label = lbl` >> gvs[]
QED

Theorem remove_unreachable_blocks_every:
  EVERY P (fn_insts f) ==> EVERY P (fn_insts (remove_unreachable_blocks f))
Proof
  Cases_on `fn_entry_label f` >>
  simp[remove_unreachable_blocks_def] >>
  rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >>
  simp[EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem fix_phis_in_block_every:
  (!ps i. P i ==> P (fix_phi_inst ps i)) /\
  EVERY P bb.bb_instructions ==>
  EVERY P (fix_phis_in_block ps bb).bb_instructions
Proof
  simp[fix_phis_in_block_def, EVERY_APPEND, EVERY_MEM, MEM_FILTER, MEM_MAP] >>
  metis_tac[]
QED

Theorem fix_all_phis_every:
  (!ps i. P i ==> P (fix_phi_inst ps i)) /\ EVERY P (fn_insts f) ==>
  EVERY P (fn_insts (fix_all_phis f))
Proof
  simp[fix_all_phis_def] >>
  rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >>
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  metis_tac[fix_phis_in_block_every, EVERY_MEM]
QED

Theorem merge_blocks_every:
  EVERY P a.bb_instructions /\ EVERY P b.bb_instructions ==>
  EVERY P (merge_blocks a b).bb_instructions
Proof
  strip_tac >> simp[merge_blocks_def, EVERY_APPEND] >>
  qpat_x_assum `EVERY P a.bb_instructions` mp_tac >>
  Q.SPEC_TAC (`a.bb_instructions`, `xs`) >>
  Induct >> simp[] >> Cases_on `xs` >> gvs[]
QED

Theorem subst_block_labels_fn_every:
  (!lm i. P i ==> P (subst_block_labels_inst lm i)) /\
  EVERY P (fn_insts f) ==>
  EVERY P (fn_insts (subst_block_labels_fn lm f))
Proof
  simp[subst_block_labels_fn_def] >>
  rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >>
  simp[subst_block_labels_block_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]
QED

Theorem update_succ_phi_labels_every:
  (!old new i. P i ==> P (subst_label_inst old new i)) ==>
  !succs bbs. EVERY (\bb. EVERY P bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY P bb.bb_instructions)
    (update_succ_phi_labels old new bbs succs)
Proof
  strip_tac >> Induct_on `succs` >>
  gvs[update_succ_phi_labels_def] >> rpt strip_tac >>
  first_x_assum irule >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >>
  irule replace_block_every >> simp[] >>
  `EVERY P bb.bb_instructions` by
    (drule lookup_block_member_label >> strip_tac >>
     qpat_x_assum `EVERY _ bbs` mp_tac >> simp[EVERY_MEM] >>
     disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[EVERY_MEM]
QED

Theorem chain_merge_every:
  (!old new i. P i ==> P (subst_label_inst old new i)) /\
  EVERY P (fn_insts f) /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b ==>
  EVERY P (fn_insts (f with fn_blocks :=
    update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b))))
Proof
  strip_tac >> rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >> simp[] >>
  irule update_succ_phi_labels_every >> simp[] >>
  irule replace_block_every >> reverse conj_tac
  >- (irule remove_block_every >>
      gvs[fn_insts_def, fn_insts_EVERY_block]) >>
  simp[] >> irule merge_blocks_every >>
  metis_tac[EVERY_fn_lookup_block]
QED

Theorem do_merge_jump_every:
  (!old new i. P i ==> P (subst_label_inst old new i)) /\
  (!i. P i ==> P (canon_jnz_inst i)) /\
  (!al bl i. P i ==> P (update_phi_bypass al bl i)) /\
  EVERY P (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  EVERY P (fn_insts g)
Proof
  strip_tac >>
  qpat_x_assum `do_merge_jump _ _ _ _ = _` mp_tac >>
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >> simp[] >>
  irule replace_block_every >> reverse conj_tac
  >- (irule replace_block_every >> reverse conj_tac
      >- (irule remove_block_every >>
          gvs[fn_insts_def, fn_insts_EVERY_block]) >>
      simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
      metis_tac[EVERY_fn_lookup_block, EVERY_MEM]) >>
  `EVERY P a.bb_instructions` by metis_tac[EVERY_fn_lookup_block] >>
  simp[] >> Cases_on `target_lbl = a.bb_label` >>
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  gvs[EVERY_MEM]
QED

Theorem collapse_dfs_every:
  (!al bl i. P i ==> P (subst_label_inst al bl i)) /\
  (!al bl i. P i ==> P (update_phi_bypass al bl i)) /\
  (!i. P i ==> P (canon_jnz_inst i)) ==>
  !f lm vis lbl. EVERY P (fn_insts f) ==>
  EVERY P (fn_insts (FST (collapse_dfs f lm vis lbl)))
Proof
  strip_tac >>
  ho_match_mp_tac collapse_dfs_preserves_predicate >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule do_merge_jump_every >> metis_tac[]) >>
  rpt strip_tac >> irule chain_merge_every >> metis_tac[]
QED

Theorem simplify_cfg_round_with_labels_every:
  (!ps i. P i ==> P (fix_phi_inst ps i)) /\
  (!al bl i. P i ==> P (subst_label_inst al bl i)) /\
  (!al bl i. P i ==> P (update_phi_bypass al bl i)) /\
  (!i. P i ==> P (canon_jnz_inst i)) /\
  (!lm i. P i ==> P (subst_block_labels_inst lm i)) /\
  EVERY P (fn_insts f) ==>
  EVERY P (fn_insts (FST (simplify_cfg_round_with_labels f)))
Proof
  strip_tac >>
  `EVERY P (fn_insts (fix_all_phis (remove_unreachable_blocks f)))` by
    metis_tac[fix_all_phis_every, remove_unreachable_blocks_every] >>
  simp[NoAsms, simplify_cfg_round_with_labels_def] >>
  Cases_on `fn_entry_label f` >> simp[] >>
  Cases_on `collapse_dfs (fix_all_phis (remove_unreachable_blocks f)) [] [] x` >>
  PairCases_on `r` >> gvs[] >>
  `EVERY P (fn_insts q)` by metis_tac[collapse_dfs_every, pairTheory.FST] >>
  irule fix_all_phis_every >> simp[] >>
  irule remove_unreachable_blocks_every >>
  Cases_on `r0 = []` >> simp[] >>
  irule subst_block_labels_fn_every >> simp[]
QED

Theorem simplify_cfg_iter_with_labels_every:
  (!ps i. P i ==> P (fix_phi_inst ps i)) /\
  (!al bl i. P i ==> P (subst_label_inst al bl i)) /\
  (!al bl i. P i ==> P (update_phi_bypass al bl i)) /\
  (!i. P i ==> P (canon_jnz_inst i)) /\
  (!lm i. P i ==> P (subst_block_labels_inst lm i)) ==>
  !n f. EVERY P (fn_insts f) ==>
  EVERY P (fn_insts (FST (simplify_cfg_iter_with_labels n f)))
Proof
  strip_tac >> Induct_on `n` >> simp[simplify_cfg_iter_with_labels_def] >>
  rpt strip_tac >>
  Cases_on `simplify_cfg_round_with_labels f` >>
  rename1 `simplify_cfg_round_with_labels f = (g,lm)` >> simp[] >>
  Cases_on `g.fn_blocks = f.fn_blocks` >> simp[] >>
  `EVERY P (fn_insts g)` by
    metis_tac[simplify_cfg_round_with_labels_every, pairTheory.FST] >>
  Cases_on `simplify_cfg_iter_with_labels n g` >> gvs[] >>
  first_x_assum (qspec_then `g` mp_tac) >> simp[]
QED

Theorem simplify_cfg_fn_with_labels_every:
  (!ps i. P i ==> P (fix_phi_inst ps i)) /\
  (!al bl i. P i ==> P (subst_label_inst al bl i)) /\
  (!al bl i. P i ==> P (update_phi_bypass al bl i)) /\
  (!i. P i ==> P (canon_jnz_inst i)) /\
  (!lm i. P i ==> P (subst_block_labels_inst lm i)) /\
  EVERY P (fn_insts f) ==>
  EVERY P (fn_insts (FST (simplify_cfg_fn_with_labels f)))
Proof
  strip_tac >> simp[simplify_cfg_fn_with_labels_def] >>
  irule simplify_cfg_iter_with_labels_every >> simp[]
QED

Theorem simplify_cfg_fn_with_labels_ids:
  MEM id (MAP (\i. i.inst_id)
    (fn_insts (FST (simplify_cfg_fn_with_labels f)))) ==>
  MEM id (MAP (\i. i.inst_id) (fn_insts f))
Proof
  `EVERY (\i. MEM i.inst_id (MAP (\j. j.inst_id) (fn_insts f)))
     (fn_insts (FST (simplify_cfg_fn_with_labels f)))` suffices_by
    (simp[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  irule simplify_cfg_fn_with_labels_every >>
  simp[fix_phi_inst_id, update_phi_bypass_id, canon_jnz_inst_id,
       subst_label_inst_def, subst_block_labels_inst_def,
       subst_label_map_inst_def, EVERY_MEM, MEM_MAP] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `is_block_label_opcode i.inst_opcode` >> simp[]) >>
  metis_tac[]
QED

Theorem simplify_cfg_fn_with_labels_opcodes:
  R NOP /\ R ASSIGN /\ R JMP /\
  EVERY (\i. R i.inst_opcode) (fn_insts f) ==>
  EVERY (\i. R i.inst_opcode)
    (fn_insts (FST (simplify_cfg_fn_with_labels f)))
Proof
  strip_tac >> irule simplify_cfg_fn_with_labels_every >>
  simp[subst_label_inst_def, subst_block_labels_inst_def,
       update_phi_bypass_opcode] >>
  conj_tac >- metis_tac[canon_jnz_inst_opcode_property] >>
  conj_tac >- metis_tac[fix_phi_inst_opcode_property] >>
  rpt gen_tac >> Cases_on `is_block_label_opcode i.inst_opcode` >>
  simp[subst_label_map_inst_def]
QED
