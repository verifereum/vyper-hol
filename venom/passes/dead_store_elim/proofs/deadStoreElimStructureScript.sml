(* Extensional analysis preservation: transformations are compared through
   their transfer functions, independently of the fixpoint implementation. *)
Theory deadStoreElimStructure
Ancestors
  deadStoreElimDefs deadStoreElimSafety basePtrDefs cfgAnalysisProps
  passSimulationDefs passSimulationProps passSharedDefs venomInst venomWf dfIterateDefs
  list rich_list indexedLists finite_map venomExecProofs cfgDefs venomEffects
  passSharedProps venomExecSemantics
  passTransform

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
  (!bb. MEM bb fn.fn_blocks ==> bb_succs (bt bb) = bb_succs bb) ==>
  cfg_analyze (function_map_transform bt fn) = cfg_analyze fn
Proof
  strip_tac >>
  `build_succs (MAP bt fn.fn_blocks) = build_succs fn.fn_blocks` by
    (simp[build_succs_def, init_succs_def, FOLDL_MAP] >>
     irule FOLDL_CONG >> simp[]) >>
  `!succs. build_preds (MAP bt fn.fn_blocks) succs =
           build_preds fn.fn_blocks succs` by
    simp[build_preds_def, init_preds_def, FOLDL_MAP] >>
  simp[cfg_analyze_def, function_map_transform_def,
       MAP_MAP_o, combinTheory.o_DEF, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

Theorem flat_map_occurrence_unique:
  !xs x y i j.
    ALL_DISTINCT (FLAT (MAP (MAP f o g) xs)) /\
    MEM x xs /\ MEM y xs /\ i < LENGTH (g x) /\ j < LENGTH (g y) /\
    f (EL i (g x)) = f (EL j (g y)) ==> x = y /\ i = j
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (qpat_x_assum `ALL_DISTINCT (FLAT _)` kall_tac >>
      drule ALL_DISTINCT_EL_IMP >> simp[EL_MAP] >> metis_tac[])
  >- (`MEM (f (EL i (g h))) (MAP f (g h))` by
        (simp[MEM_MAP] >> metis_tac[MEM_EL]) >>
      `MEM (f (EL j (g y))) (FLAT (MAP (MAP f o g) xs))` by
        (simp[MEM_FLAT, MEM_MAP] >>
         qexists_tac `MAP f (g y)` >> conj_tac
         >- (qexists_tac `y` >> simp[]) >>
         simp[MEM_MAP] >> qexists_tac `EL j (g y)` >> simp[EL_MEM]) >>
      metis_tac[])
  >- (`MEM (f (EL j (g h))) (MAP f (g h))` by
        (simp[MEM_MAP] >> metis_tac[MEM_EL]) >>
      `MEM (f (EL i (g x))) (FLAT (MAP (MAP f o g) xs))` by
        (simp[MEM_FLAT, MEM_MAP] >>
         qexists_tac `MAP f (g x)` >> conj_tac
         >- (qexists_tac `x` >> simp[]) >>
         simp[MEM_MAP] >> qexists_tac `EL i (g x)` >> simp[EL_MEM]) >>
      metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem wf_instruction_occurrence_unique:
  wf_function fn /\ MEM bb fn.fn_blocks /\ MEM bb' fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\ j < LENGTH bb'.bb_instructions /\
  (EL i bb.bb_instructions).inst_id = (EL j bb'.bb_instructions).inst_id ==>
  bb = bb' /\ i = j
Proof
  strip_tac >>
  irule (flat_map_occurrence_unique |> Q.GEN `f` |>
    Q.ISPEC `(\inst. inst.inst_id)` |> Q.GEN `g` |>
    Q.ISPEC `(\b. b.bb_instructions)`) >> simp[] >>
  qexists_tac `fn.fn_blocks` >>
  gvs[wf_function_def, fn_inst_ids_distinct_def, combinTheory.o_DEF]
QED

Theorem all_dead_stores_occurrence:
  wf_function fn /\ all_dead_stores dead_ids cfg aliases bp space fn /\
  MEM inst (fn_insts fn) /\ inst.inst_id IN dead_ids ==>
  ?bb idx. MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    is_memory_def_opcode space inst.inst_opcode /\ inst.inst_outputs = [] /\
    ~(bp_get_write_location bp inst space).ml_volatile /\
    ml_is_fixed (bp_get_write_location bp inst space) /\
    (bp_get_write_location bp inst space).ml_size <> SOME 0 /\
    outputs_unused inst fn /\ effects_in_space space inst /\
    ~dse_mem_def_live cfg aliases bp (bp_get_write_location bp inst space)
       space fn bb idx
Proof
  rpt strip_tac >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    gvs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
        MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  qpat_x_assum `all_dead_stores _ _ _ _ _ _` mp_tac >>
  simp[all_dead_stores_def] >> disch_then drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `other.inst_id = inst.inst_id` >>
  `MEM other (fn_insts fn)` by
    (simp[fn_insts_def, MEM_FLAT, MEM_MAP] >>
     qexists_tac `bb.bb_instructions` >> simp[] >>
     simp[Abbr `other`] >> metis_tac[MEM_EL]) >>
  `other = inst` by
    (qpat_x_assum `MEM inst _` mp_tac >>
     qpat_x_assum `MEM other _` mp_tac >> simp[MEM_EL] >>
     rpt strip_tac >>
     drule ALL_DISTINCT_EL_IMP >>
     simp[EL_MAP] >> metis_tac[]) >>
  gvs[] >> qexistsl_tac [`bb`, `inst_idx`] >> simp[markerTheory.Abbrev_def]
QED

Theorem all_dead_stores_at:
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\
  MEM bb fn.fn_blocks /\ get_instruction bb idx = SOME inst /\
  inst.inst_id IN ids ==>
  is_memory_def_opcode sp inst.inst_opcode /\ inst.inst_outputs = [] /\
  ~(bp_get_write_location bp inst sp).ml_volatile /\
  ml_is_fixed (bp_get_write_location bp inst sp) /\
  (bp_get_write_location bp inst sp).ml_size <> SOME 0 /\
  outputs_unused inst fn /\ effects_in_space sp inst /\
  ~dse_mem_def_live cfg aliases bp (bp_get_write_location bp inst sp) sp fn bb idx
Proof
  strip_tac >> gvs[get_instruction_def, AllCaseEqs()] >>
  qpat_x_assum `all_dead_stores _ _ _ _ _ _` mp_tac >>
  simp[all_dead_stores_def] >> disch_then drule >> strip_tac >>
  `bb = bb' /\ idx = inst_idx` by
    (irule wf_instruction_occurrence_unique >> simp[] >>
     qexists_tac `fn` >> simp[]) >>
  qpat_x_assum `bb = bb'` SUBST_ALL_TAC >>
  qpat_x_assum `idx = inst_idx` SUBST_ALL_TAC >>
  asm_rewrite_tac []
QED

Theorem dse_single_pass_preserves_wf:
  wf_function fn ==> wf_function (dse_single_pass dead_ids space fn)
Proof
  strip_tac >> simp[dse_single_pass_def] >>
  irule map_transform_preserves_wf >> simp[] >> rpt strip_tac >>
  Cases_on `inst.inst_id IN dead_ids /\ is_memory_def_opcode space inst.inst_opcode` >>
  gvs[dse_inst_def, mk_nop_inst_def, is_memory_def_opcode_def,
      is_terminator_def] >>
  Cases_on `space` >> gvs[write_effects_def, empty_effects_def]
QED

Theorem dse_single_pass_preserves_ssa:
  wf_function fn /\ ssa_form fn ==>
  ssa_form (dse_single_pass dead_ids space fn)
Proof
  strip_tac >> simp[dse_single_pass_def] >>
  irule map_transform_preserves_ssa >> simp[] >> rpt strip_tac >>
  simp[dse_inst_def] >> IF_CASES_TAC >> simp[mk_nop_inst_def]
QED

Theorem cfg_analyze_dse_single_pass:
  cfg_analyze (dse_single_pass dead_ids space fn) = cfg_analyze fn
Proof
  simp[dse_single_pass_def] >> irule cfg_analyze_block_transform >>
  simp[block_map_transform_def] >> gen_tac >> strip_tac >>
  rewrite_tac[GSYM MAPi_EQ_MAP] >>
  irule mapi_transform_bb_succs >>
  simp[dse_inst_def, mk_nop_inst_def, is_memory_def_opcode_def,
       is_terminator_def] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >> gvs[is_terminator_def]
QED

Theorem bp_analyze_dse_sound:
  wf_function fn /\ all_dead_stores dead_ids cfg aliases bp space fn ==>
  bp_analyze cfg' (dse_single_pass dead_ids space fn) = bp_analyze cfg' fn
Proof
  strip_tac >> irule bp_analyze_dse_single_pass >> rpt strip_tac >>
  drule_all all_dead_stores_occurrence >> strip_tac >> simp[]
QED


Theorem cfg_analyze_clear_nops:
  wf_function fn ==> cfg_analyze (clear_nops_function fn) = cfg_analyze fn
Proof
  strip_tac >>
  pure_rewrite_tac[clear_nops_function_def, GSYM function_map_transform_def] >>
  irule cfg_analyze_block_transform >> simp[clear_nops_block_def] >>
  rpt strip_tac >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  drule clear_nops_succs >> simp[clear_nops_block_def]
QED

Theorem dse_inst_phi:
  inst.inst_opcode = PHI ==> dse_inst dead_ids space inst = inst
Proof
  strip_tac >> Cases_on `space` >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def]
QED

Theorem phi_prefix_length_dse:
  !insts. phi_prefix_length (MAP (dse_inst dead_ids space) insts) =
    phi_prefix_length insts
Proof
  Induct >> simp[phi_prefix_length_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- simp[dse_inst_phi, phi_prefix_length_def] >>
  Cases_on `h.inst_id IN dead_ids /\ is_memory_def_opcode space h.inst_opcode` >>
  simp[dse_inst_def, mk_nop_inst_def, phi_prefix_length_def]
QED

Theorem eval_phis_dse:
  !insts. eval_phis s (MAP (dse_inst dead_ids space) insts) = eval_phis s insts
Proof
  Induct >> simp[eval_phis_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- simp[dse_inst_phi, eval_phis_def] >>
  Cases_on `h.inst_id IN dead_ids /\ is_memory_def_opcode space h.inst_opcode` >>
  simp[dse_inst_def, mk_nop_inst_def, eval_phis_def]
QED

(* Shared with the single-pass semantic simulation. *)
Theorem block_map_transform_label:
  !f bb. (block_map_transform f bb).bb_label = bb.bb_label
Proof
  simp[block_map_transform_def]
QED

Theorem lookup_block_dse_single_pass:
  !lbl fn dead_ids space.
    lookup_block lbl (dse_single_pass dead_ids space fn).fn_blocks =
    OPTION_MAP (block_map_transform (dse_inst dead_ids space))
      (lookup_block lbl fn.fn_blocks)
Proof
  simp[dse_single_pass_def, function_map_transform_def] >>
  rpt gen_tac >> irule lookup_block_map >> simp[block_map_transform_label]
QED

Theorem memory_def_opcode_not_terminator:
  !space op. is_memory_def_opcode space op ==> ~is_terminator op
Proof
  simp[is_memory_def_opcode_def] >> Cases_on `space` >> simp[]
QED

Theorem dse_inst_is_terminator:
  !dead_ids space inst.
    is_terminator (dse_inst dead_ids space inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[dse_inst_def] >>
  simp[mk_nop_inst_def, is_terminator_def] >>
  metis_tac[memory_def_opcode_not_terminator]
QED

Theorem get_instruction_dse:
  get_instruction (block_map_transform (dse_inst dead_ids space) bb) idx =
  OPTION_MAP (dse_inst dead_ids space) (get_instruction bb idx)
Proof
  simp[get_instruction_def, block_map_transform_def] >>
  IF_CASES_TAC >> simp[EL_MAP]
QED
