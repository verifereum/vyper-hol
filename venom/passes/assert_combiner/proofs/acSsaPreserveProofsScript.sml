(*
 * Assert Combiner — the transform preserves ssa_form
 *
 * Why it holds: every output of the transformed function is either an
 * original output (kept, or cleared when the assert is NOP'd) or a fresh
 * ac_or_var i / ac_iz_var i for the id i of a rewritten assert, which lies
 * in ac_fresh_vars_fn fn (same dfg, same ac_scan_block candidates). The
 * premise keeps fresh names apart from original outputs; "ac_or_" and
 * "ac_iz_" differ and toString is injective (ASCIInumbersTheory.toString_inj),
 * and distinct ids (wf_function) give distinct fresh names.
 * ac_transform_block_shape (acShapeProofs) gives the per-instruction shape.
 *)

Theory acSsaPreserveProofs
Ancestors
  acShapeProofs acChainProofs assertCombinerDefs venomWf list pred_set

Definition ac_ssa_output_shape_def:
  ac_ssa_output_shape fresh inst ys <=>
    (ys = [] \/ ys = inst.inst_outputs) \/
    (ac_or_var inst.inst_id IN fresh /\ ac_iz_var inst.inst_id IN fresh /\
     (ys = [ac_or_var inst.inst_id; ac_iz_var inst.inst_id] \/
      ys = [ac_or_var inst.inst_id; ac_iz_var inst.inst_id] ++ inst.inst_outputs))
End

Theorem ac_ssa_output_provenance[local]:
  ac_ssa_output_shape fresh i ys /\ MEM x ys ==>
  MEM x i.inst_outputs \/
  (x IN fresh /\ (x = ac_or_var i.inst_id \/ x = ac_iz_var i.inst_id))
Proof
  rw[ac_ssa_output_shape_def] >> gvs[] >> metis_tac[]
QED

Theorem ac_ssa_output_distinct[local]:
  ac_ssa_output_shape fresh i ys /\ ALL_DISTINCT i.inst_outputs /\
  (!x. MEM x i.inst_outputs ==> x NOTIN fresh) ==> ALL_DISTINCT ys
Proof
  rw[ac_ssa_output_shape_def] >>
  simp[ALL_DISTINCT_APPEND] >> metis_tac[ac_or_iz_distinct]
QED

Theorem ac_ssa_shape_outputs[local]:
  MEM bb fn.fn_blocks /\
  ac_out_shape id_base
    (ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE) inst out ==>
  ac_ssa_output_shape (ac_fresh_vars_fn fn) inst
    (FLAT (MAP (\i. i.inst_outputs) out))
Proof
  rw[ac_out_shape_def] >> gvs[ac_ssa_output_shape_def] >>
  simp[ac_fresh_vars_fn_def, ac_fresh_vars_block_def,
       IN_BIGUNION, MEM_MAP, MEM_FLAT, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem ac_ssa_chunks_disjoint[local]:
  ac_ssa_output_shape fresh i xs /\ ac_ssa_output_shape fresh j ys /\
  i.inst_id <> j.inst_id /\
  (!x. MEM x i.inst_outputs ==> ~MEM x j.inst_outputs) /\
  (!x. MEM x i.inst_outputs ==> x NOTIN fresh) /\
  (!x. MEM x j.inst_outputs ==> x NOTIN fresh) ==>
  !x. MEM x xs ==> ~MEM x ys
Proof
  rpt strip_tac >>
  `MEM x i.inst_outputs \/
   (x IN fresh /\ (x = ac_or_var i.inst_id \/ x = ac_iz_var i.inst_id))`
    by (irule ac_ssa_output_provenance >> metis_tac[]) >>
  `MEM x j.inst_outputs \/
   (x IN fresh /\ (x = ac_or_var j.inst_id \/ x = ac_iz_var j.inst_id))`
    by (irule ac_ssa_output_provenance >> metis_tac[]) >>
  qpat_x_assum `ac_ssa_output_shape fresh i xs` kall_tac >>
  qpat_x_assum `ac_ssa_output_shape fresh j ys` kall_tac >>
  gvs[ac_or_var_inj, ac_or_iz_distinct, ac_or_var_def, ac_iz_var_def,
      ASCIInumbersTheory.toString_inj]
QED

Theorem ac_ssa_flat_distinct[local]:
  !insts chunks.
  LIST_REL (ac_ssa_output_shape fresh) insts chunks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  (!i x. MEM i insts /\ MEM x i.inst_outputs ==> x NOTIN fresh) ==>
  ALL_DISTINCT (FLAT chunks)
Proof
  Induct_on `insts` >- simp[] >>
  qx_gen_tac `inst` >> qx_gen_tac `outs` >>
  namedCases_on `outs` ["", "head_outputs tail_chunks"] >>
  simp[ALL_DISTINCT_APPEND] >> rpt strip_tac
  >- (irule ac_ssa_output_distinct >> metis_tac[]) 
  >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[MEM_FLAT] >> rename1 `MEM chunk tail_chunks` >>
  drule_all LIST_REL_MEM_IMP_R >>
  disch_then (qx_choose_then `other` strip_assume_tac) >>
  `!v. MEM v head_outputs ==> ~MEM v chunk` by
    (gen_tac >> strip_tac >> irule ac_ssa_chunks_disjoint >>
     qexistsl_tac [`fresh`, `inst`, `other`] >>
     simp[] >> gvs[MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ac_ssa_block_outputs[local]:
  MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  ?chunks.
    LIST_REL (ac_ssa_output_shape (ac_fresh_vars_fn fn))
      bb.bb_instructions chunks /\
    FLAT chunks = FLAT (MAP (\i. i.inst_outputs)
      (ac_transform_block (dfg_build_function fn) id_base bb).bb_instructions)
Proof
  rpt strip_tac >> drule ac_transform_block_shape >>
  disch_then (qspecl_then [`dfg_build_function fn`, `id_base`] strip_assume_tac) >>
  qexists_tac `MAP (\out. FLAT (MAP (\i. i.inst_outputs) out)) outs` >>
  conj_tac
  >- (simp[LIST_REL_MAP2] >>
      irule LIST_REL_mono >> goal_assum (drule_at Any) >>
      rpt strip_tac >> BETA_TAC >> irule ac_ssa_shape_outputs >> metis_tac[]) >>
  simp[] >> rpt (pop_assum kall_tac) >>
  Induct_on `outs` >> simp[MAP_APPEND, FLAT_APPEND]
QED

Theorem ac_ssa_blocks_outputs[local]:
  !bbs.
  EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)) ==>
  ?chunks.
    LIST_REL (ac_ssa_output_shape (ac_fresh_vars_fn fn))
      (fn_insts_blocks bbs) chunks /\
    FLAT chunks = FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (ac_transform_block (dfg_build_function fn) id_base) bbs)))
Proof
  Induct >- simp[venomInstTheory.fn_insts_blocks_def] >>
  simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  rename1 `MEM bb fn.fn_blocks` >>
  drule_all ac_ssa_block_outputs >>
  disch_then (qspec_then `id_base`
    (qx_choose_then `head_chunks` strip_assume_tac)) >>
  first_x_assum drule >> simp[] >>
  disch_then (qx_choose_then `tail_chunks` strip_assume_tac) >>
  qexists_tac `head_chunks ++ tail_chunks` >>
  simp[venomInstTheory.fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  irule LIST_REL_APPEND_suff >> simp[]
QED

Theorem ac_ssa_function_outputs[local]:
  fn_inst_ids_distinct fn ==>
  ?chunks.
    LIST_REL (ac_ssa_output_shape (ac_fresh_vars_fn fn)) (fn_insts fn) chunks /\
    FLAT chunks = FLAT (MAP (\i. i.inst_outputs)
      (fn_insts (ac_transform_function fn)))
Proof
  simp[fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def,
       ac_transform_function_def] >> strip_tac >>
  irule ac_ssa_blocks_outputs >> simp[EVERY_MEM]
QED

Theorem ac_preserves_ssa_form_proof:
  ∀fn.
    wf_function fn ∧ ssa_form fn ∧
    (∀bb inst x.
       MEM bb fn.fn_blocks ∧ MEM inst bb.bb_instructions ∧
       MEM x inst.inst_outputs ⇒ x ∉ ac_fresh_vars_fn fn) ⇒
    ssa_form (ac_transform_function fn)
Proof
  rpt strip_tac >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  drule ac_ssa_function_outputs >> strip_tac >>
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[venomInstTheory.fn_insts_blocks_def, MAP_APPEND]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    gvs[fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def] >>
  `!bbs i. MEM i (fn_insts_blocks bbs) <=>
     ?bb. MEM bb bbs /\ MEM i bb.bb_instructions` by
    (Induct >> simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]) >>
  `!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
     x NOTIN ac_fresh_vars_fn fn` by
    (gvs[venomInstTheory.fn_insts_def] >> metis_tac[]) >>
  gvs[ssa_form_def] >> drule_all ac_ssa_flat_distinct >> simp[]
QED
