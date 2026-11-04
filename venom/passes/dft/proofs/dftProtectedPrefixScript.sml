Theory dftProtectedPrefix
Ancestors
  dftAvailability dftScheduleEdits dftSsaPreserve
  dftScheduleOrder venomWf venomInst list sorting dftDefs dftHelpers
  dftWf dftCorrectness sccpCorrectnessProofs venomState finite_map

Theorem dft_protected_prefix_producer:
  !fn bb pp done y todo d v.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    pp = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
    PERM (done ++ y::todo)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) /\
    schedule_edges bb.bb_instructions dft_must_order
      (pp ++ done ++ y::todo) /\
    MEM d bb.bb_instructions /\ MEM v d.inst_outputs /\
    MEM (Var v) y.inst_operands /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions)
      d.inst_id y.inst_id ==>
    MEM d pp \/ MEM d done
Proof
  rpt gen_tac >> strip_tac >>
  `MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `y` mp_tac) >>
     simp[MEM_FILTER]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  `ALL_DISTINCT (done ++ y::todo)` by
    metis_tac[FILTER_ALL_DISTINCT, ALL_DISTINCT_PERM] >>
  `~MEM y todo /\ ~MEM y done` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `~MEM y pp` by gvs[MEM_FILTER] >>
  `id_before bb.bb_instructions d y` by metis_tac[id_before_ids_invert] >>
  `dft_must_order d y` by
    (simp[dft_must_order_def, inst_defs_def, inst_uses_def,
          pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
          MEM_operand_vars_iff] >> metis_tac[]) >>
  `id_before (pp ++ done ++ y::todo) d y` by
    metis_tac[schedule_edges_def] >>
  gvs[dftSsaPreserveTheory.id_before_append,
      dftSsaPreserveTheory.id_before_cons] >>
  metis_tac[id_before_mem]
QED

Theorem dft_protected_prefix_operand_defined:
  !fn bb pp done y todo s t fuel C.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    pp = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
    PERM (done ++ y::todo)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) /\
    schedule_edges bb.bb_instructions dft_must_order
      (pp ++ done ++ y::todo) /\
    bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
    (!d v. MEM d pp /\ MEM v d.inst_outputs ==> v IN FDOM s.vs_vars) /\
    EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
               ~is_terminator i.inst_opcode) done /\
    FOLDR (dft_exec_cons fuel C) OK done s = OK t ==>
    !v. MEM (Var v) y.inst_operands ==> v IN FDOM t.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `y` mp_tac) >>
     simp[MEM_FILTER]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (cj 1 dft_prefix_frame) >>
     qexistsl_tac [`C`, `fuel`, `done`] >> simp[EVERY_MEM] >> fs[EVERY_MEM]) >>
  `strict_dom_vars_defined fn t` by metis_tac[dft_prefix_dominators] >>
  `y.inst_opcode <> PHI` by (strip_tac >> gvs[is_pseudo_def]) >>
  drule_all dft_prefix_fdom >> strip_tac >>
  rpt strip_tac >> irule dft_ready_operand_defined >>
  qexistsl_tac [`bb`, `fn`, `y`] >> simp[] >>
  simp[is_pseudo_def] >> rpt strip_tac >>
  `MEM d pp \/ MEM d done` by
    (drule_all dft_protected_prefix_producer >> simp[]) >>
  simp[] >> fs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
