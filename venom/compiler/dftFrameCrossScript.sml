(* Source-target inversions carry the local directed crossing certificate. *)
Theory dftFrameCross
Ancestors
  dftFrameSwap dftFrameNormalize dftFrameOrder dftScheduleOrder
  dftWf dftCorrectness dftCorrectnessFinal dftIdempotent dftTopoSort
  dftDefs venomWf venomInst venomEffects sorting list relation

Theorem id_before_asymmetric:
  ALL_DISTINCT l /\ id_before l a b ==> ~id_before l b a
Proof
  pure_rewrite_tac[id_before_def] >> rpt strip_tac >>
  `j = i'` by metis_tac[ALL_DISTINCT_EL_IMP, arithmeticTheory.LESS_TRANS] >>
  `i = j'` by metis_tac[ALL_DISTINCT_EL_IMP, arithmeticTheory.LESS_TRANS] >>
  decide_tac
QED

Theorem ssa_block_def_order:
  wf_function f /\ wf_ssa f /\ MEM bb f.fn_blocks /\
  MEM a bb.bb_instructions /\ MEM b bb.bb_instructions /\
  ~is_pseudo a.inst_opcode /\
  MEM v (inst_defs b) /\ MEM v (inst_uses a) ==>
  id_before bb.bb_instructions b a
Proof
  strip_tac >>
  `np_defs_before_uses bb.bb_instructions` by
    metis_tac[wf_ssa_defs_before_uses] >>
  `producing_inst bb.bb_instructions v = SOME b` by
    (irule producing_inst_unique_definer >> simp[GSYM inst_defs_def] >>
     rpt strip_tac >>
     `DISJOINT (set (inst_defs j)) (set (inst_defs b))` by
       metis_tac[ssa_disjoint_defs, wf_ssa_def] >>
     fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `MEM a _` mp_tac >> simp[MEM_EL] >> strip_tac >>
  qpat_x_assum `np_defs_before_uses _` mp_tac >>
  simp[np_defs_before_uses_def] >>
  disch_then (qspecl_then [`n`, `v`, `b`] mp_tac) >>
  simp[GSYM dftCorrectnessTheory.MEM_operand_vars_iff, GSYM inst_uses_def] >>
  strip_tac >> simp[id_before_def] >> metis_tac[]
QED

Theorem ssa_block_reverse_independent:
  wf_function f /\ wf_ssa f /\ MEM bb f.fn_blocks /\
  ~is_pseudo a.inst_opcode /\ id_before bb.bb_instructions a b ==>
  DISJOINT (set (inst_defs b)) (set (inst_uses a))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  `MEM a bb.bb_instructions /\ MEM b bb.bb_instructions` by
    metis_tac[id_before_mem] >>
  spose_not_then assume_tac >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  `id_before bb.bb_instructions b a` by metis_tac[ssa_block_def_order] >>
  metis_tac[id_before_asymmetric]
QED

Theorem normalized_pseudo_order:
  PERM s n /\
  n = FILTER (\i. is_pseudo i.inst_opcode) s ++
      FILTER (\i. ~is_pseudo i.inst_opcode) n /\
  id_before s a b /\ is_pseudo a.inst_opcode ==>
  id_before n a b
Proof
  strip_tac >>
  `MEM a s /\ MEM b s /\ MEM a n /\ MEM b n` by
    metis_tac[id_before_mem, PERM_MEM_EQ] >>
  Cases_on `is_pseudo b.inst_opcode`
  >- (`id_before (FILTER (\i. is_pseudo i.inst_opcode) s) a b` by
        (irule dftSsaPreserveTheory.id_before_filter >> simp[]) >>
      metis_tac[dftSsaPreserveTheory.id_before_append]) >>
  qpat_x_assum `n = _` (fn th => once_rewrite_tac[th]) >>
  simp[dftSsaPreserveTheory.id_before_append, MEM_FILTER]
QED

Theorem inversion_nonpseudo:
  pseudos_prefix bb /\ ALL_DISTINCT bb.bb_instructions /\
  PERM bb.bb_instructions n /\
  n = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
      FILTER (\i. ~is_pseudo i.inst_opcode) n /\
  id_before bb.bb_instructions a b /\ id_before n b a ==>
  ~is_pseudo a.inst_opcode /\ ~is_pseudo b.inst_opcode
Proof
  strip_tac >>
  `ALL_DISTINCT n` by metis_tac[ALL_DISTINCT_PERM] >>
  `~is_pseudo a.inst_opcode` by
    (strip_tac >>
     `id_before n a b` by metis_tac[normalized_pseudo_order] >>
     metis_tac[id_before_asymmetric]) >> simp[] >>
  qpat_x_assum `pseudos_prefix _` mp_tac >>
  qpat_x_assum `id_before bb.bb_instructions _ _` mp_tac >>
  simp[pseudos_prefix_def, id_before_def] >>
  metis_tac[]
QED

Theorem bb_before_nonterminator:
  bb_well_formed bb /\ id_before bb.bb_instructions a b ==>
  ~is_terminator a.inst_opcode
Proof
  pure_rewrite_tac[bb_well_formed_def, id_before_def] >> rpt strip_tac >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> decide_tac
QED

Theorem normalized_inversion_unordered:
  dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  PERM bb.bb_instructions n /\
  MAP (\i. i.inst_id) n = MAP (\i. i.inst_id) bb'.bb_instructions /\
  ~is_pseudo a.inst_opcode /\ ~is_pseudo b.inst_opcode /\
  id_before bb.bb_instructions a b /\ id_before n b a ==>
  ~dft_must_order a b
Proof
  strip_tac >> strip_tac >>
  `id_before n a b` by metis_tac[dft_normalize_must_order] >>
  `ALL_DISTINCT n` by metis_tac[ALL_DISTINCT_MAP, ALL_DISTINCT_PERM] >>
  metis_tac[id_before_asymmetric]
QED

Theorem normalized_inversion_compatible:
  ALL_DISTINCT (MAP (\i. i.inst_id) s) /\ PERM s n /\
  MAP (\i. i.inst_id) n = MAP (\i. i.inst_id) t /\
  (!x y. MEM x s /\ MEM y s /\
    ~abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) s) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) t) x.inst_id y.inst_id) /\
  id_before s a b /\ id_before n b a ==>
  abort_compatible a.inst_opcode b.inst_opcode
Proof
  strip_tac >> spose_not_then assume_tac >>
  `MEM a s /\ MEM b s` by metis_tac[id_before_mem] >>
  `id_before (MAP (\i. i.inst_id) s) a.inst_id b.inst_id` by
    metis_tac[dftSsaPreserveTheory.id_before_map] >>
  `id_before (MAP (\i. i.inst_id) n) b.inst_id a.inst_id` by
    metis_tac[dftSsaPreserveTheory.id_before_map] >>
  `id_before (MAP (\i. i.inst_id) n) a.inst_id b.inst_id` by metis_tac[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) n)` by metis_tac[PERM_MAP, ALL_DISTINCT_PERM] >>
  metis_tac[id_before_asymmetric]
QED

Theorem dft_normalized_inversion_cross:
  wf_function f /\ wf_ssa f /\ fn_inst_wf f /\ fn_pseudos_prefix f /\
  MEM bb f.fn_blocks /\ dft_block_rel bb bb' /\
  PERM bb.bb_instructions n /\
  MAP (\i. i.inst_id) n = MAP (\i. i.inst_id) bb'.bb_instructions /\
  n = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
      FILTER (\i. ~is_pseudo i.inst_opcode) n /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id) /\
  id_before bb.bb_instructions a b /\ id_before n b a ==>
  dft_cross a b
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  `MEM a bb.bb_instructions /\ MEM b bb.bb_instructions` by
    metis_tac[id_before_mem] >>
  `~is_pseudo a.inst_opcode /\ ~is_pseudo b.inst_opcode` by
    (irule inversion_nonpseudo >> qexistsl [`bb`, `n`] >>
     simp[] >> metis_tac[fn_pseudos_prefix_def]) >>
  `~dft_must_order a b` by metis_tac[normalized_inversion_unordered] >>
  `abort_compatible a.inst_opcode b.inst_opcode` by
    metis_tac[normalized_inversion_compatible] >>
  `a.inst_id <> b.inst_id` by
    metis_tac[dftSsaPreserveTheory.id_before_map, id_before_distinct_endpoints] >>
  `~is_terminator a.inst_opcode` by
    metis_tac[bb_before_nonterminator, wf_function_def] >>
  `DISJOINT (set (inst_defs b)) (set (inst_uses a))` by
    metis_tac[ssa_block_reverse_independent] >>
  `DISJOINT (set (inst_defs a)) (set (inst_defs b))` by
    metis_tac[ssa_disjoint_defs, wf_ssa_def] >>
  `inst_wf a /\ inst_wf b` by metis_tac[fn_inst_wf_def] >>
  `~(is_fallible a /\ is_fallible b) \/
    (a.inst_opcode = RETURNDATACOPY /\ b.inst_opcode = ASSERT_UNREACHABLE)` by
    metis_tac[dft_unordered_compatible_fallibles] >>
  gvs[dft_cross_def, dft_must_order_def]
QED
