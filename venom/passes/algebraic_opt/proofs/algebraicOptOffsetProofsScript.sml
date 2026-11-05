Theory algebraicOptOffsetProofs
Ancestors
  algebraicOptMainShapeProofs algebraicOptShapeProofs algebraicOptDefs venomWf venomInst
  venomExecProps
Libs
  listTheory

Theorem ao_offset_cfg_edge:
  !fn a b.
    fn_cfg_edge (fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) a b <=>
    fn_cfg_edge fn a b
Proof
  simp[fn_cfg_edge_def, MEM_MAP] >> rpt gen_tac >> eq_tac
  >- (rpt strip_tac >> gvs[ao_offset_block_successors] >> metis_tac[]) >>
  strip_tac >> qexists `bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions` >>
  simp[ao_offset_block_successors] >> metis_tac[]
QED

Theorem ao_offset_entry_label:
  !fn. fn_entry_label (fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) = fn_entry_label fn
Proof
  simp[fn_entry_label_def, entry_block_def] >> gen_tac >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

Theorem ao_offset_path:
  !path fn. is_fn_path (fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) path =
    is_fn_path fn path
Proof
  Induct >> simp[is_fn_path_def] >> Cases_on `path` >>
  simp[is_fn_path_def, ao_offset_cfg_edge]
QED

Theorem ao_offset_dominates:
  !fn a b. fn_dominates (fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) a b =
    fn_dominates fn a b
Proof
  rpt gen_tac >>
  `fn_cfg_edge (fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) =
    fn_cfg_edge fn` by simp[FUN_EQ_THM, ao_offset_cfg_edge] >>
  simp[fn_dominates_def, fn_reachable_def, ao_offset_path,
    ao_offset_entry_label]
QED

Theorem ao_offset_available:
  !fn bb use_opt x.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    def_available_at fn bb use_opt x ==>
    def_available_at
      (fn with fn_blocks := MAP (\b. b with bb_instructions :=
        MAP ao_handle_offset_inst b.bb_instructions) fn.fn_blocks)
      (bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions)
      (OPTION_MAP ao_handle_offset_inst use_opt) x
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  qexistsl [`def_bb with bb_instructions := MAP ao_handle_offset_inst def_bb.bb_instructions`,
    `ao_handle_offset_inst def_inst`] >>
  simp[MEM_MAP, ao_handle_offset_inst_shape, ao_offset_dominates] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  strip_tac >>
  `def_bb.bb_label = bb.bb_label` by
    (qpat_x_assum `_ with bb_instructions := _ = _` 
      (mp_tac o AP_TERM ``\b:basic_block. b.bb_label``) >> simp[]) >>
  `def_bb = bb` by
    (`lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb /\
      lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       (conj_tac >> irule MEM_lookup_block >>
        gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  gvs[] >> Cases_on `use_opt` >> gvs[] >>
  qexistsl [`i`,`j`] >> simp[EL_MAP]
QED

Theorem ao_offset_var_operands:
  !inst v. MEM (Var v) (ao_handle_offset_inst inst).inst_operands =
    MEM (Var v) inst.inst_operands
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = ADD` >>
  simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t'` >> simp[]
QED

Theorem ao_offset_phi:
  !inst. inst.inst_opcode = PHI ==> ao_handle_offset_inst inst = inst
Proof
  simp[ao_handle_offset_inst_def]
QED

Theorem ao_offset_phi_uses:
  !fn bb inst.
    wf_function fn /\ MEM bb fn.fn_blocks /\ phi_edge_uses_wf fn bb inst ==>
    phi_edge_uses_wf
      (fn with fn_blocks := MAP (\b. b with bb_instructions :=
        MAP ao_handle_offset_inst b.bb_instructions) fn.fn_blocks)
      (bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions) inst
Proof
  rpt gen_tac >> simp[phi_edge_uses_wf_def, ao_offset_cfg_edge] >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists `pred_bb with bb_instructions := MAP ao_handle_offset_inst pred_bb.bb_instructions` >>
  simp[MEM_MAP, ao_offset_cfg_edge] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  drule_all ao_offset_available >> simp[]
QED

Theorem ao_offset_function_ssa:
  !fn fn0.
    wf_function fn /\ wf_ssa fn /\
    fn0 = fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
    wf_ssa fn0
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_offset_function_ids_outputs >> strip_tac >>
  rewrite_tac[wf_ssa_def] >> conj_tac
  >- gvs[ssa_form_def, wf_ssa_def] >>
  gvs[def_dominates_uses_def, MEM_MAP, wf_ssa_def] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM original bb.bb_instructions` >>
  Cases_on `original.inst_opcode = PHI`
  >- (gvs[ao_offset_phi] >> irule ao_offset_phi_uses >>
      simp[] >> metis_tac[]) >>
  simp[ao_handle_offset_inst_shape] >> rpt strip_tac >>
  `MEM (Var v) original.inst_operands` by
    metis_tac[ao_offset_var_operands] >>
  `def_available_at fn bb (SOME original) v` by metis_tac[] >>
  drule_all ao_offset_available >> simp[]
QED
