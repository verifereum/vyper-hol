(*
 * CFG normalization against the O1 pass contract: the step part.
 *
 * The dispatched transform is cfg_norm_function_supply, which splits each
 * critical edge with a fresh block (fresh label, fresh forwarding
 * variables and instruction ids from the supply) and keeps every original
 * block's label.  So one run keeps the O1 function shape, its new names
 * are fresh against the supply it was given, its label map is empty, the
 * supply it returns still has its used ids below its next one, and it
 * adds no ALLOCA (o1_fn_row).
 *)
Theory o1ContractCfgNormStep
Ancestors
  o1PassContract cfgNormSupplyProofs cfgNormSupplySim cfgNormDefs
  venomPassDispatcher venomWf venomInst unitShapeDefs fmpStepCallEnvironment
  cfgTransform dretDesugarDefs venomFnScheduleRunner fmpStepBridge
  venomWfProps

Theorem insert_split_supply_opaque_use_ok:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') /\ opaque_use_ok fn ==>
  opaque_use_ok fn'
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  rewrite_tac[opaque_use_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all insert_split_supply_inst_image >> strip_tac
  >- (drule_all supply_split_inst_source >> strip_tac >>
      gvs[gas_use_ok_def, retpc_use_ok_def]) >>
  drule supply_inst_image_metadata >> strip_tac >>
  Cases_on `old.inst_opcode = PHI`
  >- gvs[gas_use_ok_def, retpc_use_ok_def] >>
  `MEM (Var x) old.inst_operands` by
    metis_tac[supply_inst_image_nonphi_vars] >>
  `MEM x (irSupply$fn_ir_vars fn)` by
    metis_tac[supply_inst_operand_ir_var] >>
  strip_tac >>
  `copy_phi_var RETPC_PARAM fn x` by
    (irule insert_split_supply_copy_phi_old_var >>
     simp[] >> goal_assum (drule_at Any) >>
     gvs[retpc_var_def] >> metis_tac[]) >>
  irule supply_inst_image_retpc_use >> goal_assum (drule_at Any) >>
  irule opaque_use_ok_retpc_use >> simp[retpc_var_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem insert_split_supply_dalloca_opaque:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') /\
  (!inst x. MEM inst (fn_insts fn) /\ inst.inst_opcode = DALLOCA /\
    MEM x inst.inst_outputs ==> ~gas_var fn x /\ ~retpc_var fn x) ==>
  (!inst x. MEM inst (fn_insts fn') /\ inst.inst_opcode = DALLOCA /\
    MEM x inst.inst_outputs ==> ~gas_var fn' x /\ ~retpc_var fn' x)
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  drule_all insert_split_supply_inst_image >> strip_tac
  >- (drule_all supply_split_inst_replacement >> simp[]) >>
  drule supply_inst_image_metadata >> strip_tac >>
  `old.inst_opcode = DALLOCA` by metis_tac[] >>
  `MEM x (irSupply$fn_ir_vars fn)` by
    metis_tac[supply_inst_output_ir_var] >>
  `~gas_var fn x /\ ~retpc_var fn x` by metis_tac[] >>
  gvs[gas_var_def, retpc_var_def] >>
  `GAS <> ASSIGN /\ GAS <> PHI /\ GAS <> JMP /\
   RETPC_PARAM <> ASSIGN /\ RETPC_PARAM <> PHI /\ RETPC_PARAM <> JMP` by simp[] >>
  conj_tac >> strip_tac >>
  metis_tac[insert_split_supply_copy_phi_old_var]
QED

Theorem supply_shaped_revert_successors:
  bb.bb_instructions <> [] /\ EVERY label_positions_ok bb.bb_instructions /\
  (LAST bb.bb_instructions).inst_opcode = REVERT ==> num_succs bb = 0
Proof
  strip_tac >>
  `label_positions_ok (LAST bb.bb_instructions)` by
    (gvs[listTheory.EVERY_EL, listTheory.LAST_EL] >>
     first_x_assum irule >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `get_successors (LAST bb.bb_instructions) = []` by
    (irule supply_get_successors_no_labels >> gvs[label_positions_ok_def]) >>
  Cases_on `bb.bb_instructions` >> gvs[cfgTransformTheory.num_succs_def, bb_succs_def]
QED

Theorem supply_shaped_jump_successors:
  bb.bb_instructions <> [] /\ EVERY inst_wf bb.bb_instructions /\
  EVERY label_positions_ok bb.bb_instructions /\
  (LAST bb.bb_instructions).inst_opcode = JMP ==> num_succs bb = 1
Proof
  strip_tac >>
  `label_positions_ok (LAST bb.bb_instructions)` by
    (gvs[listTheory.EVERY_EL, listTheory.LAST_EL] >>
     first_x_assum irule >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[listTheory.EVERY_EL, listTheory.LAST_EL] >>
     first_x_assum irule >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `?lab. (LAST bb.bb_instructions).inst_operands = [Label lab]` by
    gvs[inst_wf_def] >>
  `get_successors (LAST bb.bb_instructions) = [lab]` by
    simp[get_successors_def, is_terminator_def, venomStateTheory.get_label_def] >>
  Cases_on `bb.bb_instructions` >>
  gvs[cfgTransformTheory.num_succs_def, bb_succs_def, listTheory.nub_def]
QED

Theorem supply_revert_witness_not_pred:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  MEM bb fn.fn_blocks /\ MEM pred fn.fn_blocks /\
  1 < cfgTransform$num_succs pred /\ bb.bb_instructions <> [] /\
  ((LAST bb.bb_instructions).inst_opcode = REVERT \/
   (LAST bb.bb_instructions).inst_opcode = JMP) ==>
  bb.bb_label <> pred.bb_label
Proof
  strip_tac >> strip_tac >>
  `bb = pred` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  qpat_x_assum `bb = pred` SUBST_ALL_TAC >>
  `EVERY inst_wf pred.bb_instructions` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY label_positions_ok pred.bb_instructions` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum irule >> simp[fn_insts_def] >>
     irule MEM_fn_insts_blocks >> goal_assum (drule_at Any) >> simp[]) >>
  `cfgTransform$num_succs pred = 0 \/ cfgTransform$num_succs pred = 1` by
    metis_tac[supply_shaped_revert_successors, supply_shaped_jump_successors] >>
  gvs[]
QED

Theorem supply_block_image_revert_last:
  bb.bb_label <> pred.bb_label /\ bb.bb_instructions <> [] /\
  (LAST bb.bb_instructions).inst_opcode <> PHI ==>
  LAST (supply_block_image pred target split repls bb).bb_instructions =
    LAST bb.bb_instructions
Proof
  strip_tac >> simp[supply_block_image_def] >>
  Cases_on `bb.bb_label = target.bb_label` >> simp[] >>
  simp[cfgNormDefsTheory.update_phis_for_split_def, listTheory.LAST_MAP] >>
  simp[]
QED

Theorem insert_split_supply_revert_block_witness:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  1 < cfgTransform$num_succs pred /\
  insert_split_supply s fn pred target = (fn',s') ==>
  !bb. MEM bb fn.fn_blocks /\ bb.bb_instructions <> [] /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    ((LAST bb.bb_instructions).inst_opcode = REVERT \/
     (LAST bb.bb_instructions).inst_opcode = JMP) ==>
    ?bb'. MEM bb' fn'.fn_blocks /\ bb'.bb_label = bb.bb_label /\
      bb'.bb_instructions <> [] /\
      EVERY (\i. i.inst_opcode <> INVOKE) bb'.bb_instructions /\
      LAST bb'.bb_instructions = LAST bb.bb_instructions
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  gen_tac >> strip_tac >> (
  `bb.bb_label <> pred.bb_label` by
    metis_tac[supply_revert_witness_not_pred] >>
  `split.bb_label <> bb.bb_label` by
    (drule_all supply_split_label_not_old >> strip_tac >>
     gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule_all insert_split_supply_image_lookup >> strip_tac >>
  qexists `supply_block_image pred target split repls bb` >>
  conj_tac
  >- metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  simp[] >> conj_tac
  >- metis_tac[supply_block_image_length, listTheory.LENGTH_NIL] >>
  conj_tac
  >- (qpat_x_assum `EVERY (\i. i.inst_opcode <> INVOKE) _` mp_tac >>
      simp[listTheory.EVERY_EL] >> strip_tac >> rpt strip_tac >>
      drule supply_block_image_index >> strip_tac >>
      gvs[] >> metis_tac[]) >>
  irule supply_block_image_revert_last >> simp[])
QED

Theorem insert_split_supply_revert_path:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  1 < cfgTransform$num_succs pred /\
  insert_split_supply s fn pred target = (fn',s') ==>
  !n l. revert_path fn.fn_blocks n l ==> revert_path fn'.fn_blocks n l
Proof
  strip_tac >> match_mp_tac revert_path_block_witness_transport >>
  match_mp_tac insert_split_supply_revert_block_witness >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem insert_split_supply_block_count:
  insert_split_supply s fn pred target = (fn',s') ==>
  LENGTH fn'.fn_blocks = SUC (LENGTH fn.fn_blocks)
Proof
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  simp[insert_split_supply_def] >> strip_tac >> gvs[] >>
  simp[cfgTransformProofsTheory.LENGTH_replace_block]
QED

Theorem supply_split_revert_jump:
  build_split_block_supply s pred target = (split,repls,s') ==>
  split.bb_instructions <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE) split.bb_instructions /\
  (LAST split.bb_instructions).inst_opcode = JMP /\
  (LAST split.bb_instructions).inst_operands = [Label target.bb_label]
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE) split.bb_instructions` by
    (drule supply_split_opcodes >> simp[listTheory.EVERY_MEM] >>
     rpt strip_tac >> `i.inst_opcode = ASSIGN \/ i.inst_opcode = JMP` by metis_tac[] >>
     gvs[]) >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >> Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def]
QED

Theorem supply_first_block_no_preds_iff:
  fn.fn_blocks <> [] ==>
  (first_block_no_preds fn <=>
    ~?a. fn_cfg_edge fn a (HD fn.fn_blocks).bb_label)
Proof
  simp[unitShapeDefsTheory.first_block_no_preds_def, listTheory.EVERY_MEM, fn_cfg_edge_def] >>
  metis_tac[]
QED

(* The new label must not already label an incoming edge of a PHI, or the
   renamed PHI would list it twice. *)
Theorem supply_update_phis_inst_shape:
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. i.inst_opcode = PHI ==> ~MEM (Label new) i.inst_operands)
    bb.bb_instructions ==>
  EVERY inst_shape_ok
    (update_phis_for_split old new repls bb).bb_instructions
Proof
  rewrite_tac[update_phis_for_split_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  rename1 `MEM inst _` >>
  `inst_shape_ok inst` by metis_tac[] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  `~MEM (Label new) inst.inst_operands` by metis_tac[] >>
  qpat_x_assum `!e. _` kall_tac >>
  qpat_x_assum `!e. _` kall_tac >>
  `ALL_DISTINCT
     (MAP FST (phi_pairs (update_phi_ops old new repls inst.inst_operands)))` by
    (irule supply_phi_pairs_update_distinct >>
     gvs[inst_shape_ok_def, listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
     metis_tac[cfgNormBaseTheory.phi_pairs_mem_label]) >>
  gvs[inst_shape_ok_def, supply_phi_pairs_update, label_positions_ok_def,
      is_read0_opcode_def]
QED

Theorem supply_subst_terminator_inst_shape:
  EVERY inst_wf bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  ~MEM new (block_ir_labels bb) ==>
  EVERY inst_shape_ok (subst_label_terminator old new bb).bb_instructions
Proof
  rpt strip_tac >>
  `EVERY label_positions_ok
     (subst_label_terminator old new bb).bb_instructions` by
    (irule supply_subst_terminator_label_positions >>
     gvs[listTheory.EVERY_MEM, inst_shape_ok_def]) >>
  pop_assum mp_tac >>
  rewrite_tac[cfgTransformTheory.subst_label_terminator_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  rename1 `MEM inst _` >>
  `inst_shape_ok inst` by metis_tac[listTheory.EVERY_MEM] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (`label_positions_ok (cfgTransform$subst_label_inst old new inst)` by
        (first_x_assum (qspec_then `inst` mp_tac) >> simp[]) >>
      `~is_read0_opcode inst.inst_opcode /\ inst.inst_opcode <> PHI` by
        (Cases_on `inst.inst_opcode` >>
         gvs[is_terminator_def, is_read0_opcode_def]) >>
      gvs[inst_shape_ok_def, cfgTransformTheory.subst_label_inst_def]) >>
  simp[]
QED

Theorem supply_split_inst_shape:
  build_split_block_supply s pred target = (split,repls,s') ==>
  EVERY inst_shape_ok split.bb_instructions
Proof
  strip_tac >> drule supply_split_opcodes >>
  drule supply_split_label_positions >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM inst split.bb_instructions` >>
  `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = JMP` by metis_tac[] >>
  gvs[inst_shape_ok_def, is_read0_opcode_def]
QED

Theorem supply_block_image_inst_shape:
  EVERY inst_wf bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  ~MEM split.bb_label (block_ir_labels bb) ==>
  EVERY inst_shape_ok
    (supply_block_image pred target split repls bb).bb_instructions
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI ==> ~MEM (Label split.bb_label) i.inst_operands)
     bb.bb_instructions` by
    (gvs[listTheory.EVERY_MEM, irSupplyTheory.block_ir_labels_def,
         irSupplyTheory.inst_ir_labels_def, irSupplyTheory.MEM_operand_ir_labels,
         listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
     metis_tac[]) >>
  `EVERY (\i. i.inst_opcode = PHI ==> ~MEM (Label split.bb_label) i.inst_operands)
     (subst_label_terminator target.bb_label split.bb_label bb).bb_instructions` by
    (gvs[cfgTransformTheory.subst_label_terminator_def, listTheory.EVERY_MAP] >>
     gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     rename1 `MEM inst bb.bb_instructions` >>
     Cases_on `is_terminator inst.inst_opcode` >>
     gvs[cfgTransformTheory.subst_label_inst_def,
         venomInstTheory.is_terminator_def] >>
     metis_tac[]) >>
  simp[supply_block_image_def] >>
  rpt IF_CASES_TAC >>
  metis_tac[supply_update_phis_inst_shape, supply_subst_terminator_inst_shape]
QED

Theorem insert_split_supply_inst_shape:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  EVERY inst_shape_ok (fn_insts fn')
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `~MEM split.bb_label (fn_ir_labels fn)` by
    (`~MEM split.bb_label s.irs_used_labels` by
       metis_tac[build_split_block_supply_label_fresh] >>
     gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
         venomFnScheduleRunnerTheory.list_subset_def,
         listTheory.EVERY_MEM] >> metis_tac[]) >>
  fs[fn_insts_def] >>
  fs[ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM inst bb.bb_instructions` >>
  drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[] >> metis_tac[supply_split_inst_shape, listTheory.EVERY_MEM]) >>
  gvs[] >>
  `EVERY inst_shape_ok
     (supply_block_image pred target split repls bb').bb_instructions` by
    (irule supply_block_image_inst_shape >>
     gvs[venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM,
         irSupplyTheory.fn_ir_labels_def, listTheory.MEM_FLAT,
         listTheory.MEM_MAP] >> metis_tac[]) >>
  metis_tac[listTheory.EVERY_MEM]
QED

Theorem supply_formal_label_not_reserved:
  ~reserved_label (STRCAT "formal_label_" suffix)
Proof
  simp[reserved_label_def, stringTheory.STRCAT_def,
       listTheory.isPREFIX]
QED

Theorem supply_split_not_reserved:
  build_split_block_supply s pred target = (split,repls,s') ==>
  ~reserved_label split.bb_label
Proof
  strip_tac >> Cases_on `irSupply$fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lbl,s1)` >>
  drule irSupplyTheory.fresh_ir_label_contract >> strip_tac >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >> Cases_on `irSupply$fresh_inst_id r1` >>
  gvs[build_split_block_supply_def] >>
  simp[reserved_label_def, listTheory.isPREFIX]
QED

Theorem insert_split_supply_no_reserved:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  EVERY (\bb. ~reserved_label bb.bb_label) fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  EVERY (\bb. ~reserved_label bb.bb_label) fn'.fn_blocks
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[] >> metis_tac[supply_split_not_reserved]) >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem insert_split_supply_first_block_no_phi:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  first_block_no_phi fn /\
  insert_split_supply s fn pred target = (fn',s') ==>
  first_block_no_phi fn'
Proof
  strip_tac >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[insert_split_supply_entry] >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `MEM (HD fn'.fn_blocks) fn'.fn_blocks` by
    (Cases_on `fn'.fn_blocks` >> gvs[]) >>
  drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[first_block_no_phi_def] >>
      drule supply_split_opcodes >> simp[listTheory.EVERY_MEM] >>
      rpt strip_tac >> rename1 `MEM inst _` >>
      first_x_assum (qspec_then `inst` mp_tac) >> simp[]) >>
  `bb = HD fn.fn_blocks` by
    (irule venomExecProofsTheory.same_label_same_block >>
     conj_tac >- gvs[] >>
     qexists `fn` >> simp[] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  gvs[first_block_no_phi_def] >>
  `EVERY (\op. op <> PHI)
    (MAP (\i. i.inst_opcode)
      (supply_block_image pred target split repls (HD fn.fn_blocks)).bb_instructions)` by
    (pure_rewrite_tac[supply_block_image_opcodes] >>
     simp[listTheory.EVERY_MAP]) >>
  pop_assum mp_tac >> simp[listTheory.EVERY_MAP]
QED

Theorem supply_block_image_invoke_mem:
  MEM inst (supply_block_image pred target split repls bb).bb_instructions /\
  inst.inst_opcode = INVOKE ==>
  MEM inst bb.bb_instructions
Proof
  strip_tac >>
  drule (iffLR listTheory.MEM_EL) >> strip_tac >>
  `n < LENGTH bb.bb_instructions` by gvs[] >>
  drule supply_block_image_index >> strip_tac >>
  ` (EL n bb.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
  drule supply_block_image_body_index >>
  simp[is_terminator_def] >>
  metis_tac[listTheory.MEM_EL]
QED

Theorem insert_split_supply_invoke_mem:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts fn') /\ inst.inst_opcode = INVOKE ==>
  MEM inst (fn_insts fn)
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  gvs[fn_insts_def, fn_insts_blocks_MEM] >>
  drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[] >> drule supply_split_opcodes >>
      simp[listTheory.EVERY_MEM] >>
      disch_then (qspec_then `inst` mp_tac) >> simp[]) >>
  gvs[] >>
  `MEM inst bb'.bb_instructions` by
    metis_tac[supply_block_image_invoke_mem] >>
  metis_tac[]
QED

Theorem insert_split_supply_fn_invoke_ok:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_invoke_ok names fn /\
  insert_split_supply s fn pred target = (fn',s') ==>
  fn_invoke_ok names fn'
Proof
  simp[fn_invoke_ok_def] >>
  metis_tac[insert_split_supply_invoke_mem]
QED

Theorem insert_split_supply_fn_label_refs_ok:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ fn_label_refs_ok fn /\
  insert_split_supply s fn pred target = (fn',s') ==>
  fn_label_refs_ok fn'
Proof
  strip_tac >> drule insert_split_supply_labels >> strip_tac >>
  `MEM target.bb_label (fn_labels fn')` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM split_bb.bb_label (fn_labels fn')` by simp[] >>
  simp[fn_label_refs_ok_def, fn_insts_def, fn_insts_blocks_MEM] >>
  rpt strip_tac >> drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[] >>
      `EVERY (\i. i.inst_opcode <> INVOKE ==>
         !l. MEM (Label l) i.inst_operands ==>
           MEM l (fn_labels fn') \/ reserved_label l) bb.bb_instructions` by
        (ho_match_mp_tac supply_split_label_refs >> simp[] >> metis_tac[]) >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  gvs[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE ==>
     !l. MEM (Label l) i.inst_operands ==>
       MEM l (fn_labels fn') \/ reserved_label l) bb'.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     gvs[fn_label_refs_ok_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE ==>
     !l. MEM (Label l) i.inst_operands ==>
       MEM l (fn_labels fn') \/ reserved_label l)
     (supply_block_image pred target split_bb repls bb').bb_instructions` by
    (ho_match_mp_tac supply_block_image_label_refs >> simp[]) >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem supply_revert_path_suc:
  !n l. revert_path bbs n l ==> revert_path bbs (SUC n) l
Proof
  Induct >- simp[revert_path_def] >>
  simp[revert_path_def, listTheory.EXISTS_MEM] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  first_x_assum (drule_then mp_tac) >>
  simp[revert_path_def, listTheory.EXISTS_MEM]
QED

Theorem insert_split_supply_revert_destination:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  1 < cfgTransform$num_succs pred /\
  insert_split_supply s fn pred target = (fn',s') /\
  revert_path fn.fn_blocks (LENGTH fn.fn_blocks) l ==>
  revert_path fn'.fn_blocks (LENGTH fn'.fn_blocks) l
Proof
  strip_tac >> drule_all insert_split_supply_block_count >> strip_tac >>
  simp[] >> irule supply_revert_path_suc >>
  irule insert_split_supply_revert_path >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem insert_split_supply_revert_split_destination:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  1 < cfgTransform$num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  revert_path fn.fn_blocks (LENGTH fn.fn_blocks) target.bb_label ==>
  revert_path fn'.fn_blocks (LENGTH fn'.fn_blocks) split.bb_label
Proof
  strip_tac >>
  `revert_path fn'.fn_blocks (LENGTH fn.fn_blocks) target.bb_label` by
    (irule insert_split_supply_revert_path >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all insert_split_supply_block_count >> strip_tac >>
  drule supply_split_revert_jump >> strip_tac >>
  `MEM split fn'.fn_blocks` by gvs[insert_split_supply_def] >>
  simp[revert_path_def, listTheory.EXISTS_MEM] >>
  qexists `split` >> simp[]
QED

Theorem supply_flag_path_map:
  (!i. MEM i insts ==>
     (f i).inst_opcode = i.inst_opcode /\
     (f i).inst_outputs = i.inst_outputs /\
     (i.inst_opcode = ASSIGN ==> (f i).inst_operands = i.inst_operands) /\
     (!vs. flag_fails bbs vs i ==> flag_fails bbs' vs (f i))) ==>
  !vs. flag_path bbs vs insts ==> flag_path bbs' vs (MAP f insts)
Proof
  Induct_on `insts` >- simp[flag_path_def] >>
  gen_tac >> disch_tac >> gen_tac >>
  ` (f h).inst_opcode = h.inst_opcode /\
    (f h).inst_outputs = h.inst_outputs /\
    (h.inst_opcode = ASSIGN ==> (f h).inst_operands = h.inst_operands)` by
    metis_tac[listTheory.MEM] >>
  `(!vs. flag_path bbs vs insts ==> flag_path bbs' vs (MAP f insts))` by
    (first_x_assum match_mp_tac >> metis_tac[listTheory.MEM]) >>
  `(!ops. h.inst_opcode <> ASSIGN ==>
    (case (h.inst_opcode,ops) of
       (ASSIGN,[Var u]) => if MEM u vs then h.inst_outputs ++ vs
                          else FILTER (\x. ~MEM x h.inst_outputs) vs
       | _ => FILTER (\x. ~MEM x h.inst_outputs) vs) =
       FILTER (\x. ~MEM x h.inst_outputs) vs)` by
    (Cases_on `h.inst_opcode` >> simp[]) >>
  Cases_on `h.inst_opcode = ASSIGN` >>
  asm_rewrite_tac[listTheory.MAP, flag_path_def] >>
  metis_tac[listTheory.MEM]
QED


Theorem supply_subst_flag_fails:
  (!l. revert_path bbs (LENGTH bbs) l ==>
       revert_path bbs' (LENGTH bbs') (if l = old then new else l)) ==>
  !vs i. flag_fails bbs vs i ==>
    flag_fails bbs' vs
      (if is_terminator i.inst_opcode then subst_label_inst old new i else i)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `i.inst_opcode` >>
  simp[flag_fails_def, is_terminator_def, subst_label_inst_def] >>
  strip_tac >>
  Cases_on `i.inst_operands` >> gvs[] >>
  rename1 `i.inst_operands = a::ops` >> Cases_on `a` >> gvs[] >>
  Cases_on `ops` >> gvs[subst_label_op_def]
  >- (Cases_on `s = old` >> gvs[] >> metis_tac[]) >>
  rename1 `i.inst_operands = _::a::ops` >> Cases_on `a` >> gvs[] >>
  Cases_on `ops` >> gvs[] >>
  rename1 `i.inst_operands = _::_::a::ops` >> Cases_on `a` >> gvs[] >>
  Cases_on `ops` >> gvs[subst_label_op_def] >>
  Cases_on `s' = old` >> Cases_on `s'' = old` >> gvs[] >> metis_tac[]
QED


(* Arity well-formedness alone does not bound a REVERT's syntactic successors. *)
Theorem supply_revert_multisucc_probe[local]:
  inst_wf <|inst_id := 0; inst_opcode := REVERT;
    inst_operands := [Label "a"; Label "b"]; inst_outputs := []|> /\
  num_succs <|bb_label := "p"; bb_instructions :=
    [<|inst_id := 0; inst_opcode := REVERT;
      inst_operands := [Label "a"; Label "b"]; inst_outputs := []|>]|> = 2
Proof
  CONV_TAC EVAL
QED

Theorem insert_split_supply_inst_id_inj:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM i (fn_insts fn') /\ MEM j (fn_insts fn') /\ i.inst_id = j.inst_id ==>
  i = j
Proof
  strip_tac >>
  `fn_inst_ids_distinct fn'` by metis_tac[insert_split_supply_ids_distinct] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn'))` by
    gvs[fn_inst_ids_distinct_def, fn_insts_def, venomWfPropsTheory.fn_insts_blocks_flat,
        listTheory.MAP_FLAT, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule (ISPEC ``\i:instruction. i.inst_id`` all_distinct_map_mem_inj_cfg) >>
  simp[] >> qexists `fn_insts fn'` >> simp[]
QED

Theorem supply_split_output_inj:
  ir_supply_inst_ok s /\ build_split_block_supply s pred target = (split,repls,s') /\
  MEM i split.bb_instructions /\ MEM j split.bb_instructions /\
  MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >> drule_all supply_split_outputs_distinct >> strip_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp[cfg_block_decl_vars_def] >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `build_split_block_supply _ _ _ = _` kall_tac >>
  qpat_x_assum `MEM i _` mp_tac >> qpat_x_assum `MEM j _` mp_tac >>
  qspec_tac (`split.bb_instructions`, `insts`) >> Induct >>
  simp[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem insert_split_supply_retpc_definitions:
  wf_function fn /\ retpc_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts fn') /\ MEM x inst.inst_outputs /\ retpc_var fn' x ==>
  inst.inst_opcode = RETPC_PARAM \/
  (inst.inst_opcode = ASSIGN /\ ?y. inst.inst_operands = [Var y] /\ retpc_var fn' y) \/
  (inst.inst_opcode = PHI /\
   (?y. MEM (Var y) inst.inst_operands /\ retpc_var fn' y) /\
   (!y. MEM (Var y) inst.inst_operands ==> retpc_var fn' y))
Proof
  strip_tac >> drule_all insert_split_supply_inst_image >> strip_tac
  >- suspend "fresh" >>
  drule supply_inst_image_metadata >> strip_tac >>
  `MEM x (irSupply$fn_ir_vars fn)` by metis_tac[supply_inst_output_ir_var] >>
  `retpc_var fn x` by metis_tac[insert_split_supply_retpc_old_var] >>
  `old.inst_opcode = RETPC_PARAM \/
   (old.inst_opcode = ASSIGN /\ ?y. old.inst_operands = [Var y] /\ retpc_var fn y) \/
   (old.inst_opcode = PHI /\
    (?y. MEM (Var y) old.inst_operands /\ retpc_var fn y) /\
    (!y. MEM (Var y) old.inst_operands ==> retpc_var fn y))` by
    (gvs[retpc_shape_ok_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac
  >- simp[]
  >- suspend "assign"
  >> suspend "phi"
QED

Resume insert_split_supply_retpc_definitions[fresh]:
  drule_all supply_split_inst_replacement >> strip_tac >>
  `retpc_var fn v` by metis_tac[insert_split_supply_retpc_replacement] >>
  `retpc_var fn' v` by
    (simp[retpc_var_def] >> irule insert_split_supply_copy_phi_forward >>
     simp[is_terminator_def] >> metis_tac[retpc_var_def]) >>
  simp[] >> metis_tac[]
QED

Resume insert_split_supply_retpc_definitions[assign]:
  `inst = old` by metis_tac[supply_inst_image_assign] >>
  `retpc_var fn' y` by
    (simp[retpc_var_def] >> irule insert_split_supply_copy_phi_forward >>
     simp[is_terminator_def] >> metis_tac[retpc_var_def]) >>
  metis_tac[]
QED

Resume insert_split_supply_retpc_definitions[phi]:
  `!z. MEM (Var z) old.inst_operands ==> retpc_var fn' z` by
    (rpt strip_tac >> simp[retpc_var_def] >>
     irule insert_split_supply_copy_phi_forward >> simp[is_terminator_def] >>
     metis_tac[retpc_var_def]) >>
  `!v w. MEM (v,w) repls /\ MEM (Var v) old.inst_operands ==> retpc_var fn' w` by
    (rpt strip_tac >> metis_tac[insert_split_supply_retpc_replacement]) >>
  qpat_x_assum `supply_inst_image _ _ _ _ _ _` mp_tac >>
  simp[supply_inst_image_def, is_terminator_def] >> strip_tac
  >- metis_tac[] >>
  gvs[] >> conj_tac
  >- (drule supply_update_phi_ops_var_forward >>
      disch_then (qspecl_then [`pred.bb_label`, `split.bb_label`, `repls`] mp_tac) >>
      metis_tac[]) >>
  rpt strip_tac >> drule supply_update_phi_ops_var_origin >> metis_tac[]
QED

Finalise insert_split_supply_retpc_definitions

Theorem insert_split_supply_retpc_unique:
  wf_function fn /\ retpc_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM i (fn_insts fn') /\ MEM j (fn_insts fn') /\
  MEM x i.inst_outputs /\ MEM x j.inst_outputs /\ retpc_var fn' x ==> i = j
Proof
  strip_tac >>
  Cases_on `MEM i split.bb_instructions`
  >- (Cases_on `MEM j split.bb_instructions`
      >- (irule supply_split_output_inj >> metis_tac[]) >>
      `?b. MEM b (fn_insts fn) /\
           supply_inst_image pred.bb_label target.bb_label split.bb_label repls b j` by
        metis_tac[insert_split_supply_inst_image] >>
      suspend "fresh_old") >>
  `?a. MEM a (fn_insts fn) /\
       supply_inst_image pred.bb_label target.bb_label split.bb_label repls a i` by
    metis_tac[insert_split_supply_inst_image] >>
  Cases_on `MEM j split.bb_instructions`
  >- suspend "old_fresh" >>
  `?b. MEM b (fn_insts fn) /\
       supply_inst_image pred.bb_label target.bb_label split.bb_label repls b j` by
    metis_tac[insert_split_supply_inst_image] >>
  suspend "old_old"
QED

Resume insert_split_supply_retpc_unique[old_fresh]:
  drule_all supply_split_inst_replacement >> strip_tac >>
  drule supply_inst_image_metadata >> strip_tac >>
  `MEM x (irSupply$fn_ir_vars fn)` by metis_tac[supply_inst_output_ir_var] >>
  metis_tac[supply_split_replacement_not_old]
QED

Resume insert_split_supply_retpc_unique[fresh_old]:
  drule_all supply_split_inst_replacement >> strip_tac >>
  drule supply_inst_image_metadata >> strip_tac >>
  `MEM x (irSupply$fn_ir_vars fn)` by metis_tac[supply_inst_output_ir_var] >>
  metis_tac[supply_split_replacement_not_old]
QED

Resume insert_split_supply_retpc_unique[old_old]:
  `i.inst_outputs = a.inst_outputs /\ j.inst_outputs = b.inst_outputs` by
    metis_tac[supply_inst_image_metadata] >>
  `MEM x (irSupply$fn_ir_vars fn)` by metis_tac[supply_inst_output_ir_var] >>
  `retpc_var fn x` by metis_tac[insert_split_supply_retpc_old_var] >>
  `a = b` by (gvs[retpc_shape_ok_def] >> metis_tac[]) >>
  `i.inst_id = j.inst_id` by
    (gvs[supply_inst_image_def, subst_label_inst_def] >> metis_tac[]) >>
  irule insert_split_supply_inst_id_inj >> metis_tac[]
QED

Finalise insert_split_supply_retpc_unique

(* A split block copies PHI values of its edge by ASSIGN and jumps on, so a
   copy of a return-PC variable is one too and keeps a single definition. *)
Theorem insert_split_supply_reachable_return:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts (reachable_fn fn')) /\
  MEM inst.inst_opcode [RET; RETFMP; DRET] ==>
  ?i. MEM i (fn_insts (reachable_fn fn)) /\
      i.inst_opcode = inst.inst_opcode /\ i.inst_operands = inst.inst_operands
Proof
  strip_tac >> drule_all insert_split_supply_reachable_inst_cases >> strip_tac
  >- (drule_all supply_split_inst_source >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `inst = reachable_inst fn' bb.bb_label j` >>
  qabbrev_tac `i = EL n bb.bb_instructions` >>
  `supply_inst_image pred.bb_label target.bb_label split.bb_label repls i j` by
    (simp[Abbr `i`, Abbr `j`] >> irule supply_block_image_index_image >> simp[]) >>
  `MEM i bb.bb_instructions` by
    (simp[Abbr `i`, listTheory.MEM_EL] >> metis_tac[]) >>
  `MEM i (fn_insts fn)` by
    (rewrite_tac[fn_insts_def] >> irule MEM_fn_insts_blocks >>
     qexists `bb` >> simp[]) >>
  `label_positions_ok i` by
    (gvs[fn_shape_ok_def, listTheory.EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `MEM i.inst_opcode [RET; RETFMP; DRET]` by
    metis_tac[supply_inst_image_metadata, reachable_inst_fields] >>
  `j = i` by
    (qpat_x_assum `supply_inst_image _ _ _ _ _ _` mp_tac >>
     simp[supply_inst_image_def] >> strip_tac >> gvs[] >>
     irule supply_subst_label_nonjump_terminator >> simp[] >> gvs[]) >>
  qexists `reachable_inst fn bb.bb_label i` >>
  conj_tac
  >- (rewrite_tac[MEM_reachable_fn_insts] >> qexistsl [`bb`, `i`] >> simp[]) >>
  gvs[reachable_inst_fields]
QED

Theorem insert_split_supply_retpc_returns:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  insert_split_supply s fn pred target = (fn',s') ==>
  !inst. MEM inst (fn_insts (reachable_fn fn')) /\
    MEM inst.inst_opcode [RET; RETFMP; DRET] ==>
    ?front x. inst.inst_operands = front ++ [Var x] /\ retpc_var (reachable_fn fn') x
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  rpt gen_tac >> disch_tac >>
  `MEM inst (fn_insts (reachable_fn fn')) /\ MEM inst.inst_opcode [RET; RETFMP; DRET]` by gvs[] >>
  drule_all insert_split_supply_reachable_return >> strip_tac >>
  `?front x. i.inst_operands = front ++ [Var x] /\ retpc_var (reachable_fn fn) x` by
    (qpat_x_assum `fn_shape_ok fn` mp_tac >>
     simp[fn_shape_ok_def, retpc_shape_ok_def] >> metis_tac[]) >>
  qexistsl [`front`, `x`] >> simp[] >>
  `MEM x (irSupply$fn_ir_vars fn)` by
    (irule supply_inst_operand_ir_var >>
     `MEM i (fn_insts fn)` by
       (irule reachable_fn_insts_nonphi >> simp[] >> gvs[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all insert_split_supply_reachable_retpc_old_var >> gvs[]
QED

Theorem insert_split_supply_retpc_phis:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  insert_split_supply s fn pred target = (fn',s') ==>
  !inst x y. MEM inst (fn_insts (reachable_fn fn')) /\ inst.inst_opcode = PHI /\
    MEM (Var x) inst.inst_operands /\ MEM (Var y) inst.inst_operands /\
    retpc_var (reachable_fn fn') x ==> retpc_var (reachable_fn fn') y
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  rpt strip_tac >> drule_all insert_split_supply_reachable_phi_backward_active >> strip_tac >>
  `!w. MEM (Var w) inst.inst_operands ==>
    ?v. MEM (Var v) i.inst_operands /\
      (retpc_var (reachable_fn fn') w <=> retpc_var (reachable_fn fn) v)` by
    (rpt strip_tac >>
     qpat_x_assum `!w. MEM (Var w) inst.inst_operands ==> _`
       (qspec_then `w` mp_tac) >> simp[] >> strip_tac
     >- (qexists `w` >> simp[] >>
         `MEM w (irSupply$fn_ir_vars fn)` by
           (drule_all reachable_fn_insts_operand >> strip_tac >>
            irule supply_inst_operand_ir_var >> metis_tac[]) >>
         irule insert_split_supply_reachable_retpc_old_var >> simp[] >> metis_tac[]) >>
     qexists `v` >> simp[] >>
     irule insert_split_supply_reachable_retpc_replacement >> simp[] >> metis_tac[]) >>
  qpat_assum `!w. _ ==> ?v. _ /\ (retpc_var _ w <=> _)`
    (qspec_then `x` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!w. _ ==> ?v. _ /\ (retpc_var _ w <=> _)`
    (qspec_then `y` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `fn_shape_ok fn` mp_tac >>
  simp[fn_shape_ok_def, retpc_shape_ok_def] >> metis_tac[]
QED

Theorem insert_split_supply_retpc_shape_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  insert_split_supply s fn pred target = (fn',s') ==>
  retpc_shape_ok fn'
Proof
  strip_tac >>
  `retpc_shape_ok fn` by gvs[fn_shape_ok_def] >>

  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  rewrite_tac[retpc_shape_ok_def] >> conj_tac
  >- (rpt gen_tac >> disch_tac >> irule insert_split_supply_retpc_returns >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule insert_split_supply_retpc_phis >> simp[] >> metis_tac[]) >>
  conj_tac >> rpt strip_tac
  >- (irule insert_split_supply_retpc_definitions >> simp[] >> metis_tac[]) >>
  irule insert_split_supply_retpc_unique >> simp[] >> metis_tac[]
QED

Theorem insert_split_supply_fn_shape_ok:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  insert_split_supply s fn pred target = (fn',s') ==>
  fn_shape_ok fn'
Proof
  strip_tac >>
  `retpc_shape_ok fn'` by metis_tac[insert_split_supply_retpc_shape_ok] >>
  `EVERY label_positions_ok (fn_insts fn)` by
    (gvs[fn_shape_ok_def, inst_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `fn'.fn_name = fn.fn_name` by metis_tac[insert_split_supply_name] >>
  `fn.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[insert_split_supply_entry] >>
  gvs[fn_shape_ok_def] >> rpt conj_tac
  >- metis_tac[insert_split_supply_opaque_use_ok]
  >- metis_tac[insert_split_supply_no_reserved]
  >> metis_tac[insert_split_supply_inst_shape]
QED

Theorem insert_split_supply_o1_fn_shape:
  o1_fn_shape ctx fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  insert_split_supply s fn pred target = (fn',s') ==>
  o1_fn_shape ctx fn'
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[o1_fn_shape_def] >>
  `fn'.fn_name = fn.fn_name` by metis_tac[insert_split_supply_name] >>
  `!P. P ASSIGN /\ P JMP /\ EVERY (\i. P i.inst_opcode) (fn_insts fn) ==>
        EVERY (\i. P i.inst_opcode) (fn_insts fn')` by
    (rpt strip_tac >> irule insert_split_supply_opcode_property >> metis_tac[]) >>
  gvs[o1_fn_shape_def] >> rpt conj_tac
  >- metis_tac[insert_split_supply_wf_function]
  >- metis_tac[insert_split_supply_fn_inst_wf]
  >- metis_tac[insert_split_supply_fn_shape_ok]
  >- metis_tac[insert_split_supply_first_block_no_preds]
  >- metis_tac[insert_split_supply_first_block_no_phi]
  >- metis_tac[insert_split_supply_fn_invoke_ok]
  >- metis_tac[insert_split_supply_fn_label_refs_ok]
  >- (`EVERY (\i. i.inst_opcode <> DRET) (fn_insts fn')` suffices_by
        simp[no_dret_def, listTheory.EVERY_MEM] >>
      first_x_assum ho_match_mp_tac >> gvs[no_dret_def, listTheory.EVERY_MEM])
  >- (match_mp_tac insert_split_supply_dalloca_opaque >> metis_tac[])
  >- (strip_tac >> gvs[entry_fn_no_return_def, entry_fn_no_params_def] >>
      first_x_assum ho_match_mp_tac >> simp[is_param_opcode_def]) >>
  strip_tac >> first_x_assum ho_match_mp_tac >> simp[]
QED

Theorem insert_split_supply_ir_covered:
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s'
Proof
  strip_tac >> drule_all insert_split_supply_contract >> strip_tac >>
  `ir_supply_inst_ok s'` by
    gvs[cfg_fn_supply_contract_def, cfg_supply_extends_def] >>
  `cfg_supply_covers_fn s fn` by
    gvs[cfg_supply_covers_fn_def, ir_supply_covers_fn_def,
        list_subset_def, listTheory.EVERY_MEM] >>
  `cfg_supply_covers_block s pred /\ cfg_supply_covers_block s target` by
    (gvs[cfg_supply_covers_fn_blocks, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all insert_split_supply_covered >> strip_tac >>
  gvs[cfg_supply_covers_fn_def, ir_supply_covers_fn_def,
      list_subset_def, irSupplyTheory.ir_supply_inst_ok_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Definition supply_o1_inv_def:
  supply_o1_inv ctx s fn <=>
    o1_fn_shape ctx fn /\ o1_fn_row 8 fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s
End

(* A split rewrites only the blocks, so it keeps the FMP convention. *)
Theorem insert_split_supply_fmp_signature:
  insert_split_supply s fn pred target = (fn',s') ==>
  fn'.fn_fmp_signature = fn.fn_fmp_signature
Proof
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  simp[insert_split_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem insert_split_supply_o1_inv:
  supply_o1_inv ctx s fn /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  insert_split_supply s fn pred target = (fn',s') ==>
  supply_o1_inv ctx s' fn'
Proof
  strip_tac >> gvs[supply_o1_inv_def] >>
  `o1_fn_shape ctx fn'` by metis_tac[insert_split_supply_o1_fn_shape] >>
  `ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s'` by
    metis_tac[insert_split_supply_ir_covered] >>
  `fmp_sig_no_param fn'` by
    (drule insert_split_supply_fmp_signature >>
     gvs[o1_fn_row_def, fmp_sig_no_param_def]) >>
  simp[] >> gvs[o1_fn_row_def] >>
  ho_match_mp_tac insert_split_supply_opcode_property >>
  gvs[o1_fn_shape_def] >> metis_tac[]
QED

Theorem cfg_norm_round_supply_o1_inv:
  supply_o1_inv ctx s fn /\ cfg_norm_round_supply s fn = (fn',changed,s') ==>
  supply_o1_inv ctx s' fn'
Proof
  strip_tac >> drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[] >>
  `fn_cfg_edge fn pred.bb_label target.bb_label` by
    (simp[fn_cfg_edge_def] >> qexists `pred` >> simp[]) >>
  irule insert_split_supply_o1_inv >> metis_tac[]
QED

Theorem cfg_norm_iter_supply_o1_inv:
  !n s fn fn' s'. supply_o1_inv ctx s fn /\
    cfg_norm_iter_supply n s fn = (fn',s') ==> supply_o1_inv ctx s' fn'
Proof
  Induct >- simp[cfg_norm_iter_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  `supply_o1_inv ctx s1 fn1` by metis_tac[cfg_norm_round_supply_o1_inv] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_o1_inv:
  supply_o1_inv ctx s fn /\ cfg_norm_function_supply s fn = (fn',s') ==>
  supply_o1_inv ctx s' fn'
Proof
  simp[cfg_norm_function_supply_def] >> metis_tac[cfg_norm_iter_supply_o1_inv]
QED

Theorem insert_split_supply_fresh_names:
  wf_function fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  fresh_names_ok s fn fn'
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all insert_split_supply_inst_ids >> strip_tac >>
  `~MEM split_bb.bb_label s.irs_used_labels` by
    metis_tac[build_split_block_supply_label_fresh] >>
  `EVERY (\id. ~MEM id s.irs_used_inst_ids) (block_ir_inst_ids split_bb)` by
    metis_tac[build_split_block_supply_ids_fresh] >>
  `fn_labels fn' = fn_labels fn ++ [split_bb.bb_label]` by
    (drule insert_split_supply_labels >> strip_tac >>
     `split_bb' = split_bb` by metis_tac[pairTheory.PAIR_EQ] >> gvs[]) >>
  gvs[fresh_names_ok_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem supply_fresh_names_trans:
  cfg_supply_extends s s1 /\ fresh_names_ok s fn fn1 /\
  fresh_names_ok s1 fn1 fn2 ==> fresh_names_ok s fn fn2
Proof
  strip_tac >> drule cfg_supply_extends_members >> strip_tac >>
  gvs[fresh_names_ok_def] >> metis_tac[]
QED

Theorem cfg_norm_round_supply_fresh_names:
  supply_o1_inv ctx s fn /\ cfg_norm_round_supply s fn = (fn',changed,s') ==>
  cfg_supply_extends s s' /\ fresh_names_ok s fn fn'
Proof
  strip_tac >>
  `ir_supply_inst_ok s /\ wf_function fn` by
    gvs[supply_o1_inv_def, o1_fn_shape_def] >>
  `cfg_supply_extends s s'` by
    metis_tac[cfg_norm_round_supply_contract, cfg_fn_supply_contract_def] >>
  simp[] >> drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[fresh_names_ok_def] >>
  metis_tac[insert_split_supply_fresh_names]
QED

Theorem cfg_norm_iter_supply_fresh_names:
  !n s fn fn' s'. supply_o1_inv ctx s fn /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    cfg_supply_extends s s' /\ fresh_names_ok s fn fn'
Proof
  Induct >- simp[cfg_norm_iter_supply_def, cfg_supply_extends_refl,
                   fresh_names_ok_def, supply_o1_inv_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  `supply_o1_inv ctx s1 fn1` by metis_tac[cfg_norm_round_supply_o1_inv] >>
  `cfg_supply_extends s s1 /\ fresh_names_ok s fn fn1` by
    metis_tac[cfg_norm_round_supply_fresh_names] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def] >>
  metis_tac[cfg_supply_extends_trans, supply_fresh_names_trans]
QED

Theorem cfg_norm_function_supply_fresh_names:
  supply_o1_inv ctx s fn /\ cfg_norm_function_supply s fn = (fn',s') ==>
  fresh_names_ok s fn fn'
Proof
  simp[cfg_norm_function_supply_def] >> metis_tac[cfg_norm_iter_supply_fresh_names]
QED

Theorem cfg_norm_step_contract:
  o1_step_contract_at 8 rpolicy (CFP_Simple VP_CFGNormalization)
Proof
  rewrite_tac[o1_step_contract_at_def] >> rpt gen_tac >> strip_tac >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >> drule venomFnScheduleRunnerPropsTheory.lookup_unique_function_member >> simp[]) >>
  `o1_fn_shape observed.cu_context fn` by
    gvs[o1_ctx_shape_def, listTheory.EVERY_MEM] >>
  `ir_supply_covers_fn s fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >> gvs[fn_pass_step_def]) >>
  `cfg_norm_function_supply s fn = (out.fpo_function,out.fpo_supply) /\
   out.fpo_label_map = []` by
    (gvs[fn_pass_step_def, AllCaseEqs()] >> simp[]) >>
  `supply_o1_inv observed.cu_context s fn` by simp[supply_o1_inv_def] >>
  `supply_o1_inv observed.cu_context out.fpo_supply out.fpo_function` by
    metis_tac[cfg_norm_function_supply_o1_inv] >>
  `fresh_names_ok s fn out.fpo_function` by
    metis_tac[cfg_norm_function_supply_fresh_names] >>
  gvs[supply_o1_inv_def, label_map_sources_ok_def, o1_fn_row_def]
QED
