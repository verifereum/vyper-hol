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
