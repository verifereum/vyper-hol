(* Extensional analysis preservation: transformations are compared through
   their transfer functions, independently of the fixpoint implementation. *)
Theory deadStoreElimStructure
Ancestors
  deadStoreElimDefs deadStoreElimSafety basePtrDefs cfgAnalysisProps
  passSimulationDefs passSimulationProps passSharedDefs venomInst venomWf dfIterateDefs
  list rich_list finite_map venomExecProofs cfgDefs

Theorem bp_handle_inst_empty_outputs:
  inst.inst_outputs = [] ==> bp_handle_inst r inst = (F,r)
Proof
  simp[bp_handle_inst_def, inst_output_def]
QED

Theorem bp_process_block_map_cong:
  !insts f r.
    (!inst r. MEM inst insts ==>
       bp_handle_inst r (f inst) = bp_handle_inst r inst) ==>
    bp_process_block r (MAP f insts) = bp_process_block r insts
Proof
  Induct >> simp[bp_process_block_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `r` assume_tac) >>
  gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem bp_process_block_filter_cong:
  !insts P r.
    (!inst r. MEM inst insts /\ ~P inst ==>
       bp_handle_inst r inst = (F,r)) ==>
    bp_process_block r (FILTER P insts) = bp_process_block r insts
Proof
  Induct >> simp[bp_process_block_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `P h`
  >- (simp[bp_process_block_def] >> pairarg_tac >> gvs[] >>
      first_x_assum irule >> simp[]) >>
  `bp_handle_inst r h = (F,r)` by (first_x_assum irule >> simp[]) >>
  simp[] >> pairarg_tac >> simp[]
QED

Theorem bp_one_pass_aux_cong:
  !order fn fn' r.
    (!r lbl.
      OPTION_MAP (\bb. bp_process_block r bb.bb_instructions)
        (FIND (\bb. bb.bb_label = lbl) fn.fn_blocks) =
      OPTION_MAP (\bb. bp_process_block r bb.bb_instructions)
        (FIND (\bb. bb.bb_label = lbl) fn'.fn_blocks)) ==>
    bp_one_pass_aux fn r order = bp_one_pass_aux fn' r order
Proof
  Induct >> simp[bp_one_pass_aux_def] >> rpt gen_tac >> strip_tac >>
  first_assum (qspecl_then [`r`, `h`] mp_tac) >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn'.fn_blocks` >> simp[]
  >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  AP_TERM_TAC >> first_x_assum irule >> simp[]
QED

Theorem bp_analyze_cong:
  (!r lbl.
    OPTION_MAP (\bb. bp_process_block r bb.bb_instructions)
      (FIND (\bb. bb.bb_label = lbl) fn.fn_blocks) =
    OPTION_MAP (\bb. bp_process_block r bb.bb_instructions)
      (FIND (\bb. bb.bb_label = lbl) fn'.fn_blocks)) ==>
  bp_analyze cfg fn = bp_analyze cfg fn'
Proof
  strip_tac >> simp[bp_analyze_def, bp_one_pass_def] >>
  `(!r. bp_one_pass_aux fn r cfg.cfg_dfs_pre =
         bp_one_pass_aux fn' r cfg.cfg_dfs_pre)` by
    (gen_tac >> irule bp_one_pass_aux_cong >> simp[]) >>
  simp[]
QED

Theorem bp_analyze_block_transform:
  (!bb. (bt bb).bb_label = bb.bb_label) /\
  (!bb r. MEM bb fn.fn_blocks ==>
    bp_process_block r (bt bb).bb_instructions =
    bp_process_block r bb.bb_instructions) ==>
  bp_analyze cfg (function_map_transform bt fn) = bp_analyze cfg fn
Proof
  strip_tac >> irule bp_analyze_cong >> rpt gen_tac >>
  simp[function_map_transform_def, GSYM lookup_block_def, lookup_block_map] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  simp[]
QED

Theorem bp_analyze_inst_map:
  (!inst r. MEM inst (fn_insts fn) ==>
    bp_handle_inst r (f inst) = bp_handle_inst r inst) ==>
  bp_analyze cfg (function_map_transform (block_map_transform f) fn) =
  bp_analyze cfg fn
Proof
  strip_tac >> irule bp_analyze_block_transform >>
  simp[block_map_transform_def] >> rpt strip_tac >>
  irule bp_process_block_map_cong >> rpt strip_tac >>
  first_x_assum irule >>
  simp[fn_insts_def] >>
  qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
  Q.SPEC_TAC (`fn.fn_blocks`, `bbs`) >> Induct >>
  simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem bp_handle_inst_nop:
  inst.inst_opcode = NOP ==> bp_handle_inst r inst = (F,r)
Proof
  strip_tac >> simp[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> simp[]
QED

Theorem bp_analyze_clear_nops:
  bp_analyze cfg (clear_nops_function fn) = bp_analyze cfg fn
Proof
  pure_rewrite_tac [clear_nops_function_def, GSYM function_map_transform_def] >>
  irule bp_analyze_block_transform >>
  simp[clear_nops_block_def] >> rpt strip_tac >>
  irule bp_process_block_filter_cong >> rpt strip_tac >>
  irule bp_handle_inst_nop >> gvs[]
QED

Theorem bp_handle_inst_dse:
  (inst.inst_id IN dead_ids /\ is_memory_def_opcode space inst.inst_opcode ==>
    inst.inst_outputs = []) ==>
  bp_handle_inst r (dse_inst dead_ids space inst) = bp_handle_inst r inst
Proof
  strip_tac >> simp[dse_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  `inst.inst_outputs = []` by simp[] >>
  simp[bp_handle_inst_empty_outputs, mk_nop_inst_def]
QED

Theorem bp_analyze_dse_single_pass:
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_id IN dead_ids /\
    is_memory_def_opcode space inst.inst_opcode ==> inst.inst_outputs = []) ==>
  bp_analyze cfg (dse_single_pass dead_ids space fn) = bp_analyze cfg fn
Proof
  strip_tac >> simp[dse_single_pass_def] >>
  irule bp_analyze_inst_map >> rpt strip_tac >>
  irule bp_handle_inst_dse >> strip_tac >> first_x_assum irule >> simp[]
QED

Theorem cfg_analyze_block_transform:
  (!bb. (bt bb).bb_label = bb.bb_label) /\
  (!bb. bb_succs (bt bb) = bb_succs bb) ==>
  cfg_analyze (function_map_transform bt fn) = cfg_analyze fn
Proof
  strip_tac >>
  simp[cfg_analyze_def, function_map_transform_def,
       build_succs_def, build_preds_def, init_succs_def, init_preds_def,
       FOLDL_MAP, MAP_MAP_o, combinTheory.o_DEF, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED
