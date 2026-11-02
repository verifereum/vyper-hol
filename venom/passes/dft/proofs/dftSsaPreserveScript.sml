(*
 * A DFT schedule of an SSA function is SSA.
 *
 * The schedule (dft_block_rel) keeps each block's label, its pseudo prefix
 * and its terminator last, so the CFG and dominance are unchanged; it
 * permutes the other instructions keeping every use after the in-block
 * definition it reads.  The CFGNormalization stage after DFT needs wf_ssa
 * on its input.
 *)
Theory dftSsaPreserve
Ancestors
  dftScheduleOrder dftStructural dftDefs venomWf venomInst list
  venomEffects passSharedDefs sorting dftCorrectness dftHelpers

Theorem flip_operands_var_mem:
  !i v. MEM (Var v) (flip_operands i).inst_operands <=>
        MEM (Var v) i.inst_operands
Proof
  rpt gen_tac >> simp[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem ssa_flippable_classes:
  !op. is_flippable op ==>
       ~is_pseudo op /\ ~is_terminator op /\ op <> PHI
Proof
  Cases >> simp[is_flippable_def, is_commutative_def,
                is_comparator_def, is_pseudo_def, is_terminator_def]
QED

Theorem flip_operands_phi_test:
  !i. ((flip_operands i).inst_opcode = PHI <=> i.inst_opcode = PHI)
Proof
  gen_tac >> rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def]
QED

Theorem dft_block_rel_origin:
  !bb bb' y. dft_block_rel bb bb' /\ MEM y bb'.bb_instructions ==>
    ?x. MEM x bb.bb_instructions /\ y.inst_id = x.inst_id /\
        (y = x \/ (is_flippable x.inst_opcode /\ y = flip_operands x))
Proof
  rw[dft_block_rel_def] >>
  gvs[MEM_FILTER, EVERY_MEM, from_block_def] >>
  metis_tac[flip_operands_inst_id]
QED

Theorem dft_block_rel_ids_perm:
  !bb bb'. dft_block_rel bb bb' ==>
    PERM (MAP (\i. i.inst_id) bb'.bb_instructions)
         (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rw[dft_block_rel_def, MAP_APPEND] >>
  irule PERM_TRANS >>
  qexists_tac `MAP (\i. i.inst_id)
    (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
     FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` >>
  conj_tac >- simp[MAP_APPEND, PERM_APPEND_IFF] >>
  irule PERM_MAP >> once_rewrite_tac[PERM_SYM] >>
  qspec_then `\i (h:instruction). is_pseudo i.inst_opcode` mp_tac
    (GEN_ALL sortingTheory.PERM3_FILTER) >>
  disch_then (qspecl_then [`bb.bb_instructions`, `ARB:instruction`] mp_tac) >>
  Cases_on `is_pseudo (ARB:instruction).inst_opcode` >> simp[]
QED

Theorem dft_block_rel_ids_distinct:
  !bb bb'. dft_block_rel bb bb' /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)
Proof
  metis_tac[dft_block_rel_ids_perm, ALL_DISTINCT_PERM, PERM_SYM]
QED

Theorem dft_block_rel_member:
  !bb bb' x. dft_block_rel bb bb' /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    MEM x bb.bb_instructions ==>
    ?y. MEM y bb'.bb_instructions /\ y.inst_id = x.inst_id /\
        (y = x \/ (is_flippable x.inst_opcode /\ y = flip_operands x))
Proof
  rpt strip_tac >>
  drule dft_block_rel_ids_perm >>
  disch_then (mp_tac o Q.SPEC `x.inst_id` o MATCH_MP PERM_MEM_EQ) >>
  simp[MEM_MAP] >> strip_tac >>
  `?y. MEM y bb'.bb_instructions /\ y.inst_id = x.inst_id`
    by metis_tac[] >>
  drule_all dft_block_rel_origin >> strip_tac >>
  rename1 `MEM z bb.bb_instructions` >>
  `z = x` by metis_tac[all_distinct_map_mem_inj] >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem dft_block_rel_outputs_perm:
  !bb bb'. dft_block_rel bb bb' /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
    PERM (MAP (\i. i.inst_outputs) bb'.bb_instructions)
         (MAP (\i. i.inst_outputs) bb.bb_instructions)
Proof
  rpt strip_tac >> irule PERM_TRANSFER_inst_id_inst_outputs >>
  simp[dft_block_rel_ids_perm] >>
  conj_tac >- (
    rpt strip_tac >> drule_all dft_block_rel_origin >> strip_tac >>
    metis_tac[all_distinct_map_mem_inj, flip_operands_inst_outputs]) >>
  metis_tac[dft_block_rel_ids_distinct]
QED

Theorem dft_blocks_outputs_perm:
  !bs cs. LIST_REL dft_block_rel bs cs /\
    EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) bs ==>
    PERM (FLAT (MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) cs))
         (FLAT (MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bs))
Proof
  Induct >> Cases_on `cs` >> simp[] >> rpt strip_tac >>
  irule PERM_CONG >> conj_tac
  >- metis_tac[dft_block_rel_outputs_perm] >>
  first_x_assum irule >> simp[]
QED

Theorem dft_block_rel_ssa_form:
  !fn bbs. wf_function fn /\ ssa_form fn /\
    LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    ssa_form (fn with fn_blocks := bbs)
Proof
  rpt strip_tac >>
  `EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      fn.fn_blocks` by
    (simp[EVERY_MEM] >> metis_tac[bb_inst_ids_distinct]) >>
  `!bs. MAP (\i. i.inst_outputs) (fn_insts_blocks bs) =
     FLAT (MAP (\bb. MAP (\i. i.inst_outputs) bb.bb_instructions) bs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  drule_all dft_blocks_outputs_perm >>
  gvs[ssa_form_def, fn_insts_def] >> strip_tac >>
  drule PERM_FLAT >>
  metis_tac[ALL_DISTINCT_PERM, PERM_SYM]
QED

Theorem id_before_cons:
  !h l a b. id_before (h::l) a b <=>
    (h = a /\ MEM b l) \/ id_before l a b
Proof
  rpt gen_tac >> eq_tac
  >- (rw[id_before_def] >> Cases_on `i` >> Cases_on `j` >>
      gvs[] >- metis_tac[MEM_EL] >>
      disj2_tac >> qexistsl [`n`, `n'`] >> simp[]) >>
  strip_tac
  >- (gvs[MEM_EL, id_before_def] >>
      qexistsl [`0`, `SUC n`] >> simp[]) >>
  gvs[id_before_def] >> qexistsl [`SUC i`, `SUC j`] >> simp[]
QED

Theorem id_before_append:
  !l r a b. id_before (l ++ r) a b <=>
    id_before l a b \/ id_before r a b \/ (MEM a l /\ MEM b r)
Proof
  Induct >- simp[id_before_def] >>
  simp[id_before_cons, MEM_APPEND] >> metis_tac[]
QED

Theorem id_before_filter:
  !l P a b. P a /\ P b /\ id_before l a b ==>
    id_before (FILTER P l) a b
Proof
  Induct >- simp[id_before_def] >>
  rpt gen_tac >> Cases_on `P h` >>
  simp[id_before_cons, MEM_FILTER] >> metis_tac[]
QED

Theorem id_before_map:
  !l f a b. id_before l a b ==> id_before (MAP f l) (f a) (f b)
Proof
  rpt strip_tac >> gvs[id_before_def] >>
  qexistsl [`i`, `j`] >> simp[EL_MAP]
QED

Theorem id_before_ids_invert:
  !l x y. ALL_DISTINCT (MAP (\i. i.inst_id) l) /\ MEM x l /\ MEM y l /\
    id_before (MAP (\i. i.inst_id) l) x.inst_id y.inst_id ==>
    id_before l x y
Proof
  rpt strip_tac >> gvs[id_before_def, EL_MAP] >>
  `i < LENGTH l` by decide_tac >>
  `EL i l = x /\ EL j l = y` by
    metis_tac[all_distinct_map_mem_inj, EL_MEM] >>
  qexistsl [`i`, `j`] >> simp[]
QED

Theorem dft_block_rel_data_ids:
  !bb bb' x y v. dft_block_rel bb bb' /\ pseudos_prefix bb /\
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    id_before bb.bb_instructions x y /\ MEM v x.inst_outputs /\
    MEM (Var v) y.inst_operands ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id
Proof
  rpt strip_tac >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id`
    by metis_tac[id_before_map] >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >>
  simp[MAP_APPEND, id_before_append] >>
  Cases_on `is_pseudo y.inst_opcode`
  >- (`is_pseudo x.inst_opcode` by
        (gvs[pseudos_prefix_def, id_before_def] >> metis_tac[]) >>
      disj1_tac >> ho_match_mp_tac id_before_map >>
      irule id_before_filter >> simp[]) >>
  Cases_on `is_pseudo x.inst_opcode`
  >- (disj2_tac >> disj2_tac >> simp[MEM_MAP, MEM_FILTER] >>
      conj_tac >- metis_tac[] >>
      drule PERM_MEM_EQ >> disch_then (qspec_then `y.inst_id` mp_tac) >>
      simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> first_x_assum irule >> simp[] >>
  simp[dft_must_order_def, inst_defs_def, inst_uses_def] >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION, MEM_operand_vars_iff] >> metis_tac[]
QED

Theorem dft_block_rel_data_order:
  !bb bb' x y x' y' v.
    dft_block_rel bb bb' /\ pseudos_prefix bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    MEM x' bb'.bb_instructions /\ MEM y' bb'.bb_instructions /\
    x'.inst_id = x.inst_id /\ y'.inst_id = y.inst_id /\
    id_before bb.bb_instructions x y /\ MEM v x.inst_outputs /\
    MEM (Var v) y.inst_operands ==>
    id_before bb'.bb_instructions x' y'
Proof
  rpt strip_tac >> irule id_before_ids_invert >>
  simp[] >> conj_tac >- metis_tac[dft_block_rel_ids_distinct] >>
  metis_tac[dft_block_rel_data_ids]
QED

Theorem id_before_last:
  !l x. l <> [] /\ MEM x l /\ x <> LAST l ==> id_before l x (LAST l)
Proof
  rpt strip_tac >> gvs[MEM_EL, id_before_def] >>
  qexistsl [`n`, `PRE (LENGTH l)`] >>
  `0 < LENGTH l` by (Cases_on `l` >> gvs[]) >>
  `EL (PRE (LENGTH l)) l = LAST l` by metis_tac[LAST_EL] >>
  `n <> PRE (LENGTH l)` by metis_tac[] >> simp[]
QED

Theorem id_before_not_last:
  !l x. l <> [] /\ ALL_DISTINCT l ==> ~id_before l (LAST l) x
Proof
  rpt strip_tac >> gvs[id_before_def] >>
  `0 < LENGTH l` by (Cases_on `l` >> gvs[]) >>
  `EL (PRE (LENGTH l)) l = LAST l` by metis_tac[LAST_EL] >>
  `i < LENGTH l /\ PRE (LENGTH l) < LENGTH l` by decide_tac >>
  `i = PRE (LENGTH l)` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  decide_tac
QED

Theorem dft_block_rel_term_order:
  !bb bb' x t. dft_block_rel bb bb' /\ MEM x bb.bb_instructions /\
    MEM t bb.bb_instructions /\ is_terminator t.inst_opcode /\
    id_before bb.bb_instructions x t ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id t.inst_id
Proof
  rpt strip_tac >>
  `~is_pseudo t.inst_opcode` by
    (Cases_on `t.inst_opcode` >> gvs[is_terminator_def, is_pseudo_def]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id t.inst_id`
    by metis_tac[id_before_map] >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >>
  simp[MAP_APPEND, id_before_append] >>
  Cases_on `is_pseudo x.inst_opcode`
  >- (disj2_tac >> disj2_tac >> simp[MEM_MAP, MEM_FILTER] >>
      conj_tac >- metis_tac[] >>
      drule PERM_MEM_EQ >> disch_then (qspec_then `t.inst_id` mp_tac) >>
      simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> first_x_assum irule >>
  simp[dft_must_order_def]
QED

Theorem dft_block_rel_last:
  !bb bb'. dft_block_rel bb bb' /\ bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
    bb'.bb_instructions <> [] /\
    LAST bb'.bb_instructions = LAST bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
    (simp[MEM_EL] >> qexists_tac `PRE (LENGTH bb.bb_instructions)` >>
     simp[LAST_EL] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule_all dft_block_rel_member >> strip_tac >>
  `y = LAST bb.bb_instructions` by metis_tac[ssa_flippable_classes] >>
  gvs[] >>
  `bb'.bb_instructions <> []` by metis_tac[MEM] >> simp[] >>
  `MEM (LAST bb'.bb_instructions) bb'.bb_instructions` by
    (simp[MEM_EL] >> qexists_tac `PRE (LENGTH bb'.bb_instructions)` >>
     simp[LAST_EL] >> Cases_on `bb'.bb_instructions` >> gvs[]) >>
  `~is_flippable (LAST bb.bb_instructions).inst_opcode` by
    metis_tac[ssa_flippable_classes] >>
  drule_all dft_block_rel_origin >> strip_tac >>
  Cases_on `x = LAST bb.bb_instructions` >> fs[] >>
  `id_before bb.bb_instructions x (LAST bb.bb_instructions)` by
    metis_tac[id_before_last] >>
  drule_all dft_block_rel_term_order >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)` by
    metis_tac[dft_block_rel_ids_distinct] >>
  `MAP (\i. i.inst_id) bb'.bb_instructions <> []` by simp[] >>
  `LAST (MAP (\i. i.inst_id) bb'.bb_instructions) = x.inst_id` by
    simp[LAST_MAP] >>
  metis_tac[id_before_not_last]
QED

Theorem dft_block_rel_label:
  !bb bb'. dft_block_rel bb bb' ==> bb'.bb_label = bb.bb_label
Proof
  simp[dft_block_rel_def]
QED

Theorem dft_block_rel_succs:
  !bb bb'. dft_block_rel bb bb' /\ bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
    bb_succs bb' = bb_succs bb
Proof
  rpt strip_tac >> drule_all dft_block_rel_last >> strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  simp[bb_succs_def] >>
  Cases_on `bb'.bb_instructions` >> Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem dft_blocks_member_left:
  !bs cs bb. LIST_REL dft_block_rel bs cs /\ MEM bb bs ==>
    ?bb'. MEM bb' cs /\ dft_block_rel bb bb'
Proof
  Induct >> Cases_on `cs` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem dft_blocks_member_right:
  !bs cs bb'. LIST_REL dft_block_rel bs cs /\ MEM bb' cs ==>
    ?bb. MEM bb bs /\ dft_block_rel bb bb'
Proof
  Induct >> Cases_on `cs` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem dft_blocks_source_unique:
  !fn bbs bb1 bb2 bb'. wf_function fn /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    dft_block_rel bb1 bb' /\ dft_block_rel bb2 bb' ==> bb1 = bb2
Proof
  rpt strip_tac >>
  `bb1.bb_label = bb2.bb_label` by metis_tac[dft_block_rel_label] >>
  metis_tac[all_distinct_map_mem_inj, wf_function_def, fn_labels_def]
QED

Theorem dft_block_rel_cfg:
  !fn bbs. wf_function fn /\ LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    fn_cfg_edge (fn with fn_blocks := bbs) = fn_cfg_edge fn
Proof
  rpt strip_tac >> simp[FUN_EQ_THM, fn_cfg_edge_def] >> rpt gen_tac >>
  eq_tac >> strip_tac
  >- (drule_all dft_blocks_member_right >> strip_tac >>
      `bb_succs bb = bb_succs bb'` by
        metis_tac[dft_block_rel_succs, bb_inst_ids_distinct, wf_function_def] >>
      metis_tac[dft_block_rel_label]) >>
  drule_all dft_blocks_member_left >> strip_tac >>
  `bb_succs bb' = bb_succs bb` by
    metis_tac[dft_block_rel_succs, bb_inst_ids_distinct, wf_function_def] >>
  metis_tac[dft_block_rel_label]
QED

Theorem dft_block_rel_entry:
  !fn bbs. LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    fn_entry_label (fn with fn_blocks := bbs) = fn_entry_label fn
Proof
  rpt strip_tac >> Cases_on `fn.fn_blocks` >> Cases_on `bbs` >>
  gvs[fn_entry_label_def, entry_block_def] >>
  metis_tac[dft_block_rel_label]
QED

Theorem dft_block_rel_path:
  !fn bbs p. wf_function fn /\ LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    (is_fn_path (fn with fn_blocks := bbs) p <=> is_fn_path fn p)
Proof
  rpt gen_tac >> strip_tac >>
  `fn_cfg_edge (fn with fn_blocks := bbs) = fn_cfg_edge fn` by
    metis_tac[dft_block_rel_cfg] >>
  Induct_on `p` >> simp[is_fn_path_def] >>
  Cases_on `p` >> gvs[is_fn_path_def]
QED

Theorem dft_block_rel_reachable:
  !fn bbs n. wf_function fn /\ LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    (fn_reachable (fn with fn_blocks := bbs) n <=> fn_reachable fn n)
Proof
  rpt strip_tac >>
  drule_all dft_block_rel_cfg >> drule dft_block_rel_entry >>
  simp[fn_reachable_def]
QED

Theorem dft_block_rel_dominates:
  !fn bbs d n. wf_function fn /\ LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    (fn_dominates (fn with fn_blocks := bbs) d n <=> fn_dominates fn d n)
Proof
  rpt strip_tac >>
  simp[fn_dominates_def, dft_block_rel_reachable,
       dft_block_rel_path, dft_block_rel_entry]
QED

Theorem dft_block_rel_available_end:
  !fn bbs bb bb' v. wf_function fn /\
    LIST_REL dft_block_rel fn.fn_blocks bbs /\
    dft_block_rel bb bb' /\ def_available_at fn bb NONE v ==>
    def_available_at (fn with fn_blocks := bbs) bb' NONE v
Proof
  rpt strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  drule_all dft_blocks_member_left >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) def_bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  drule_all dft_block_rel_member >> strip_tac >>
  simp[def_available_at_def] >>
  qexistsl [`bb''`, `y`] >>
  simp[] >>
  metis_tac[dft_block_rel_label, dft_block_rel_dominates,
            flip_operands_inst_outputs]
QED

Theorem dft_block_rel_available_use:
  !fn bbs bb bb' u u' v. wf_function fn /\ fn_pseudos_prefix fn /\
    LIST_REL dft_block_rel fn.fn_blocks bbs /\
    MEM bb fn.fn_blocks /\ dft_block_rel bb bb' /\
    MEM u bb.bb_instructions /\ MEM u' bb'.bb_instructions /\
    u'.inst_id = u.inst_id /\ MEM (Var v) u.inst_operands /\
    def_available_at fn bb (SOME u) v ==>
    def_available_at (fn with fn_blocks := bbs) bb' (SOME u') v
Proof
  rpt strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def, GSYM id_before_def] >> strip_tac >>
  drule_all dft_blocks_member_left >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) def_bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  drule_all dft_block_rel_member >> strip_tac >>
  `y.inst_outputs = def_inst.inst_outputs` by
    metis_tac[flip_operands_inst_outputs] >>
  `fn_dominates (fn with fn_blocks := bbs) bb''.bb_label bb'.bb_label` by
    metis_tac[dft_block_rel_label, dft_block_rel_dominates] >>
  simp[def_available_at_def, GSYM id_before_def] >>
  qexistsl [`bb''`, `y`] >> simp[] >> strip_tac >>
  `def_bb = bb` by metis_tac[dft_blocks_source_unique] >>
  gvs[fn_pseudos_prefix_def] >>
  irule dft_block_rel_data_order >>
  simp[] >> qexistsl [`bb`, `v`, `def_inst`, `u`] >> simp[]
QED

(* Why it holds (unchecked notes):
   - ssa_form: the same instructions up to flip_operands, which keeps
     outputs.
   - bb_succs reads the last instruction: the terminator in both
     (bb_well_formed puts it last in the input; dft_must_order keeps every
     instruction before it), and terminators are not flippable.  So
     fn_cfg_edge, fn_reachable, fn_dominates and fn_entry_label agree.
   - def_dominates_uses: PHIs are unchanged; a flipped instruction uses
     the same variables; a use in the same block as its definition stays
     after it (the data clause of dft_must_order). *)
Theorem dft_block_rel_wf_ssa:
  !fn bbs.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    wf_ssa (fn with fn_blocks := bbs)
Proof
  cheat
QED
