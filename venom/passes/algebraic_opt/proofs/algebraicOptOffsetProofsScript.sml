Theory algebraicOptOffsetProofs
Ancestors
  algebraicOptMainShapeProofs algebraicOptShapeProofs algebraicOptDefs venomWf venomInst
  venomExecProps venomExecSemantics list

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

Theorem ao_offset_step:
  !fuel ctx inst s.
    step_inst fuel ctx (ao_handle_offset_inst inst) s = step_inst fuel ctx inst s
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = ADD` >>
  simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t'` >> simp[] >>
  once_rewrite_tac[step_inst_def] >> simp[] >>
  simp[step_inst_base_def] >>
  simp[exec_pure2_def,
       venomStateTheory.eval_operand_def, wordsTheory.WORD_ADD_COMM] >>
  rename1 `FLOOKUP s.vs_labels lbl` >>
  Cases_on `FLOOKUP s.vs_labels lbl` >> simp[wordsTheory.WORD_ADD_COMM]
QED

Theorem ao_offset_phi_prefix:
  !insts. phi_prefix_length (MAP ao_handle_offset_inst insts) = phi_prefix_length insts
Proof
  Induct >> simp[phi_prefix_length_def, ao_handle_offset_inst_shape]
QED

Theorem ao_offset_eval_phis:
  !insts s. eval_phis s (MAP ao_handle_offset_inst insts) = eval_phis s insts
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[ao_handle_offset_inst_shape, ao_offset_phi]
QED

Theorem ao_offset_get_instruction:
  !bb idx. get_instruction
    (bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions) idx =
    OPTION_MAP ao_handle_offset_inst (get_instruction bb idx)
Proof
  rpt gen_tac >> simp[get_instruction_def, EL_MAP] >> IF_CASES_TAC >> simp[]
QED

Theorem ao_offset_exec_block:
  !fuel ctx bb s. exec_block fuel ctx
    (bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions) s =
    exec_block fuel ctx bb s
Proof
  rpt gen_tac >> measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >>
  once_rewrite_tac[exec_block_def] >>
  simp[ao_offset_get_instruction] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  simp[ao_offset_step, ao_handle_offset_inst_shape] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK next` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  first_x_assum irule >>
  gvs[get_instruction_def, AllCaseEqs()] >> decide_tac
QED

Theorem ao_offset_lookup_block:
  !bbs lbl. lookup_block lbl
    (MAP (\bb. bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions) bbs) =
    OPTION_MAP (\bb. bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions)
      (lookup_block lbl bbs)
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> rpt gen_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def]
QED

Theorem ao_offset_run_blocks:
  !fuel ctx fn s.
    run_blocks fuel ctx
      (fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) s =
    run_blocks fuel ctx fn s
Proof
  Induct >- (once_rewrite_tac[run_blocks_def] >> simp[]) >> rpt gen_tac >>
  once_rewrite_tac[run_blocks_def] >> simp[ao_offset_lookup_block] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  simp[ao_offset_eval_phis, ao_offset_phi_prefix, ao_offset_exec_block] >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK p` >>
  Cases_on `exec_block fuel ctx bb
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]
QED

Theorem ao_offset_function_well_formed:
  !fn fn0.
  wf_function fn /\
  fn0 = fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
  wf_function fn0
Proof
  rpt gen_tac >> strip_tac >>
  `fn_labels fn0 = fn_labels fn` by
    gvs[fn_labels_def, MAP_MAP_o, combinTheory.o_DEF] >>
  `fn_has_entry fn0 = fn_has_entry fn` by
    gvs[fn_has_entry_def] >>
  `!bb. MEM bb fn0.fn_blocks ==> bb_well_formed bb` by
    (gvs[MEM_MAP] >> rpt strip_tac >> gvs[] >>
     irule ao_offset_block_well_formed >> fs[wf_function_def]) >>
  `fn_succs_closed fn0` by
    (gvs[fn_succs_closed_def, MEM_MAP] >> rpt strip_tac >>
     gvs[ao_offset_block_successors] >>
     metis_tac[wf_function_def, fn_succs_closed_def]) >>
  drule ao_offset_function_ids_outputs >> strip_tac >>
  fs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
     rtaSupplyProofsTheory.fn_insts_blocks_inst_ids, lambdify irSupplyTheory.block_ir_inst_ids_def]
QED

Theorem ao_offset_function_coverage:
  !fn fn0 supply.
  ir_supply_covers_fn supply fn /\ EVERY label_positions_ok (fn_insts fn) /\
  fn0 = fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
  ir_supply_covers_fn supply fn0
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_offset_function_label_contract >> strip_tac >>
  drule_all ao_offset_function_vars >> strip_tac >>
  drule ao_offset_function_ids_outputs >> strip_tac >>
  gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
      irSupplyTheory.fn_ir_inst_ids_def,
      GSYM rtaSupplyProofsTheory.fn_insts_blocks_inst_ids, GSYM fn_insts_def] >>
  simp[irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
       venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >>
  gvs[EVERY_MEM, pred_setTheory.SUBSET_DEF, fn_insts_def,
      unitShapeDefsTheory.MEM_fn_insts_blocks_iff, MEM_FLAT, MEM_MAP] >>
  qpat_x_assum `!inst. _ ==> !x. _` (qspec_then `ao_handle_offset_inst y'` mp_tac) >>
  (impl_tac >- (
    qexists_tac `bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions` >>
    simp[MEM_MAP] >> metis_tac[])) >>
  disch_then drule >> simp[]
QED

Theorem ao_offset_function_initial_absence:
  fn0 = fn with fn_blocks := MAP (\bb. bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> lookup_var x s = NONE) ==>
  !i x. MEM i (fn_insts fn0) /\ MEM x i.inst_outputs ==> lookup_var x s = NONE
Proof
  strip_tac >> drule ao_offset_function_insts >> strip_tac >>
  simp[MEM_MAP] >> rpt strip_tac >> gvs[ao_handle_offset_inst_shape] >> metis_tac[]
QED
