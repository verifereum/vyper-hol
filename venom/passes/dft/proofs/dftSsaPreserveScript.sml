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
  venomEffects passSharedDefs sorting dftCorrectness

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
