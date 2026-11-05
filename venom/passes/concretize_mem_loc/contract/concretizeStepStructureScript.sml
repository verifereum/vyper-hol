Theory concretizeStepStructure
Ancestors
  concretizeMemLocDefs passSimulationProps passSharedProps venomWf
  passSharedDefs passSimulationDefs venomInst list indexedLists unitLabelMapIdentity

Theorem concretize_positions_inst_id:
  (concretize_inst_with_positions p i).inst_id = i.inst_id
Proof
  rw[concretize_inst_with_positions_def] >>
  rpt CASE_TAC >> simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_terminator:
  is_terminator inst.inst_opcode ==>
  concretize_inst_with_positions positions inst = inst /\
  inst.inst_opcode <> NOP
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >>
  strip_tac >> gvs[is_terminator_def] >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem concretize_positions_nonterminator:
  ~is_terminator i.inst_opcode ==>
  ~is_terminator (concretize_inst_with_positions p i).inst_opcode
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def, is_terminator_def]
QED

Theorem concretize_positions_phi:
  ((concretize_inst_with_positions positions inst).inst_opcode = PHI <=>
   inst.inst_opcode = PHI) /\
  (inst.inst_opcode = PHI ==>
   concretize_inst_with_positions positions inst = inst)
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >>
  simp[concretize_inst_with_positions_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `out::rest` >> Cases_on `rest` >> simp[] >>
  Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
  simp[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_preserves_wf:
  wf_function fn ==> wf_function (concretize_function_with_positions p fn)
Proof
  strip_tac >> simp[concretize_function_with_positions_def] >>
  irule clear_nops_function_preserves_wf >>
  irule map_transform_preserves_wf >>
  simp[concretize_positions_inst_id, concretize_positions_terminator,
       concretize_positions_nonterminator, concretize_positions_phi]
QED

Theorem concretize_positions_missing:
  i.inst_opcode = ALLOCA /\ i.inst_outputs = [out] ==>
  concretize_inst_with_positions FEMPTY i = mk_nop_inst i
Proof
  simp[concretize_inst_with_positions_def]
QED

Theorem concretize_positions_nop:
  i.inst_opcode = NOP ==> concretize_inst_with_positions p i = i
Proof
  simp[concretize_inst_with_positions_def]
QED

Theorem concretize_positions_inst_wf:
  inst_wf i ==> inst_wf (concretize_inst_with_positions p i)
Proof
  Cases_on `i.inst_opcode = ALLOCA` >-
    (strip_tac >> `LENGTH i.inst_outputs = 1` by gvs[inst_wf_def] >>
     Cases_on `i.inst_outputs` >> gvs[] >>
     gvs[concretize_inst_with_positions_def] >>
     CASE_TAC >> simp[mk_assign_inst_def, mk_nop_inst_def, inst_wf_def]) >>
  simp[concretize_inst_with_positions_def]
QED

Theorem concretize_positions_inst_no_alloca:
  inst_wf i ==> (concretize_inst_with_positions p i).inst_opcode <> ALLOCA
Proof
  Cases_on `i.inst_opcode = ALLOCA` >-
    (strip_tac >> `LENGTH i.inst_outputs = 1` by gvs[inst_wf_def] >>
     Cases_on `i.inst_outputs` >> gvs[] >>
     gvs[concretize_inst_with_positions_def] >>
     CASE_TAC >> simp[mk_assign_inst_def, mk_nop_inst_def]) >>
  simp[concretize_inst_with_positions_def]
QED

Theorem concretize_positions_labels:
  fn_labels (concretize_function_with_positions p fn) = fn_labels fn
Proof
  simp[concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def, block_map_transform_def, clear_nops_block_def,
       fn_labels_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem concretize_positions_inst_preimage:
  MEM bb (concretize_function_with_positions p fn).fn_blocks /\
  MEM i bb.bb_instructions ==>
  ?oldbb oldi. MEM oldbb fn.fn_blocks /\ MEM oldi oldbb.bb_instructions /\
    i = concretize_inst_with_positions p oldi /\ i.inst_opcode <> NOP
Proof
  simp[concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def, block_map_transform_def, clear_nops_block_def,
       MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  rpt strip_tac >> gvs[MEM_FILTER, MEM_MAP] >> metis_tac[]
QED

Theorem concretize_positions_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (concretize_function_with_positions p fn)
Proof
  rw[fn_inst_wf_def] >> drule_all concretize_positions_inst_preimage >>
  strip_tac >> gvs[] >> irule concretize_positions_inst_wf >>
  metis_tac[]
QED

Theorem concretize_positions_no_alloca:
  fn_inst_wf fn ==>
  EVERY (\i. i.inst_opcode <> ALLOCA)
    (fn_insts (concretize_function_with_positions p fn))
Proof
  simp[EVERY_MEM, fn_insts_MEM, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> drule_all concretize_positions_inst_preimage >>
  strip_tac >> gvs[] >>
  `inst_wf oldi` by metis_tac[fn_inst_wf_def] >>
  drule concretize_positions_inst_no_alloca >>
  disch_then (qspec_then `p` mp_tac) >> simp[]
QED

Theorem concretize_positions_ids_source:
  MEM i (fn_insts (concretize_function_with_positions p fn)) ==>
  MEM i.inst_id (MAP (\j. j.inst_id) (fn_insts fn))
Proof
  simp[fn_insts_MEM, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> drule_all concretize_positions_inst_preimage >>
  strip_tac >> gvs[concretize_positions_inst_id] >> metis_tac[]
QED

Theorem concretize_positions_blocks:
  (concretize_function_with_positions p fn).fn_blocks =
  MAP (\bb. clear_nops_block
    (block_map_transform (concretize_inst_with_positions p) bb)) fn.fn_blocks
Proof
  simp[concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem concretize_positions_unchanged:
  i.inst_opcode <> ALLOCA ==> concretize_inst_with_positions p i = i
Proof
  simp[concretize_inst_with_positions_def]
QED

Theorem concretize_positions_block_label:
  (clear_nops_block
    (block_map_transform (concretize_inst_with_positions p) bb)).bb_label =
  bb.bb_label
Proof
  simp[clear_nops_block_def, block_map_transform_def]
QED

Theorem concretize_positions_block_count:
  LENGTH (concretize_function_with_positions p fn).fn_blocks = LENGTH fn.fn_blocks
Proof
  simp[concretize_positions_blocks]
QED

Theorem concretize_positions_map_succs:
  bb_succs (block_map_transform (concretize_inst_with_positions p) bb) = bb_succs bb
Proof
  rewrite_tac[block_map_transform_def] >>
  `MAP (concretize_inst_with_positions p) bb.bb_instructions =
   MAPi (\n i. concretize_inst_with_positions p i) bb.bb_instructions` by
    (simp[MAPi_EQ_MAP] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC) >>
  pop_assum SUBST1_TAC >> irule mapi_transform_bb_succs >>
  simp[concretize_positions_terminator, concretize_positions_nonterminator]
QED

Theorem concretize_positions_map_block_wf:
  bb_well_formed bb ==>
  bb_well_formed (block_map_transform (concretize_inst_with_positions p) bb)
Proof
  strip_tac >> rewrite_tac[block_map_transform_def] >>
  `MAP (concretize_inst_with_positions p) bb.bb_instructions =
   MAPi (\n i. concretize_inst_with_positions p i) bb.bb_instructions` by
    (simp[MAPi_EQ_MAP] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC) >>
  pop_assum SUBST1_TAC >> irule mapi_transform_bb_well_formed >>
  simp[concretize_positions_terminator, concretize_positions_nonterminator,
       concretize_positions_phi]
QED

Theorem concretize_positions_block_terminal_decomp:
  bb_well_formed bb ==>
  (clear_nops_block (block_map_transform (concretize_inst_with_positions p) bb)).bb_instructions =
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) (FRONT bb.bb_instructions)) ++
  [LAST bb.bb_instructions]
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> NOP` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
    simp[APPEND_FRONT_LAST] >>
  simp[clear_nops_block_def, block_map_transform_def] >>
  qpat_x_assum `_ = FRONT _ ++ _` (fn th =>
    CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV th))))) >>
  simp[MAP_APPEND, FILTER_APPEND_DISTRIB, concretize_positions_terminator]
QED

Theorem concretize_positions_block_last:
  bb_well_formed bb ==>
  LAST (clear_nops_block
    (block_map_transform (concretize_inst_with_positions p) bb)).bb_instructions =
  LAST bb.bb_instructions
Proof
  simp[concretize_positions_block_terminal_decomp]
QED

Theorem concretize_positions_block_succs:
  bb_well_formed bb ==>
  bb_succs (clear_nops_block
    (block_map_transform (concretize_inst_with_positions p) bb)) = bb_succs bb
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[bb_succs_def, concretize_positions_block_terminal_decomp] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `prefix ++ [last]` >>
  Cases_on `prefix` >> simp[LAST_DEF, LAST_APPEND_CONS]
QED

Theorem concretize_positions_var_operand:
  MEM (Var x) (concretize_inst_with_positions p i).inst_operands ==>
  concretize_inst_with_positions p i = i
Proof
  rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem concretize_positions_entry_label:
  fn_entry_label (concretize_function_with_positions positions fn) =
  fn_entry_label fn
Proof
  Cases_on `fn.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def,
       concretize_function_with_positions_def, clear_nops_function_def,
       function_map_transform_def, clear_nops_block_def, block_map_transform_def]
QED

Theorem concretize_positions_cfg_edge:
  EVERY bb_well_formed fn.fn_blocks ==>
  (fn_cfg_edge (concretize_function_with_positions positions fn) a b <=>
   fn_cfg_edge fn a b)
Proof
  strip_tac >>
  simp[fn_cfg_edge_def, concretize_function_with_positions_def,
       clear_nops_function_def, function_map_transform_def, MEM_MAP] >>
  eq_tac
  >- (rpt strip_tac >> gvs[] >>
      rename1 `MEM source fn.fn_blocks` >>
      `bb_well_formed source` by metis_tac[EVERY_MEM] >>
      drule concretize_positions_block_succs >>
      disch_then (qspec_then `positions` assume_tac) >>
      qexists `source` >>
      gvs[clear_nops_block_def, block_map_transform_def]) >>
  rpt strip_tac >>
  rename1 `MEM source fn.fn_blocks` >>
  `bb_well_formed source` by metis_tac[EVERY_MEM] >>
  drule concretize_positions_block_succs >>
  disch_then (qspec_then `positions` assume_tac) >>
  qexists `clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) source)` >>
  conj_tac
  >- (qexists `block_map_transform (concretize_inst_with_positions positions) source` >>
      simp[] >> qexists `source` >> simp[]) >>
  gvs[clear_nops_block_def, block_map_transform_def]
QED

Theorem concretize_positions_reachable:
  EVERY bb_well_formed fn.fn_blocks ==>
  (fn_reachable (concretize_function_with_positions positions fn) lbl <=>
   fn_reachable fn lbl)
Proof
  strip_tac >>
  `fn_cfg_edge (concretize_function_with_positions positions fn) = fn_cfg_edge fn`
    by (simp[FUN_EQ_THM, concretize_positions_cfg_edge]) >>
  simp[fn_reachable_def, concretize_positions_entry_label]
QED
