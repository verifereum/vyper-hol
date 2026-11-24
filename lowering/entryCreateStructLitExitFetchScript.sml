Theory entryCreateStructLitExitFetch
Ancestors
  entryCreateAddedFragMember entryCreateIntervalLayout exprSimAbiGasBridge
  abiEncoderProps exprLoweringProps fragExec venomFnInstsProofs venomExecProps
  venomWf venomInst list rich_list

Theorem frag_code_prefix_or_emitted[local]:
  MEM j (frag_code a b) ==>
  MEM j b.cs_current_insts \/
  ?blk. MEM blk (emitted_blocks a b) /\ MEM j blk.bb_instructions
Proof
  Cases_on `emitted_blocks a b = []`
  >- (simp[frag_code_def, emitted_insts_def] >> metis_tac[MEM_DROP_IMP]) >>
  fs[frag_code_def, NULL_EQ, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_DROP_IMP, MEM_LAST_NOT_NIL, MEM_FRONT_NOT_NIL]
QED

(* ALL_DISTINCT_APPEND separates the two occurrences in this block. *)
Theorem prefix_exit_id_distinct[local]:
  fn_inst_ids_distinct f /\ MEM bb f.fn_blocks /\
  isPREFIX pre bb.bb_instructions /\ get_instruction bb (LENGTH pre) = SOME i /\
  MEM j pre ==> j.inst_id <> i.inst_id
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    (irule all_distinct_flat_mem >>
     qexists_tac `MAP (\(blk:basic_block). MAP (\x. x.inst_id) blk.bb_instructions) f.fn_blocks` >>
     fs[fn_inst_ids_distinct_def, MEM_MAP] >> metis_tac[]) >>
  fs[IS_PREFIX_APPEND] >>
  rename1 `bb.bb_instructions = pre ++ rest` >>
  Cases_on `rest` >>
  gvs[get_instruction_def, el_append3, EL_LENGTH_APPEND_0, ALL_DISTINCT_APPEND] >>
  fs[MEM_MAP] >> metis_tac[]
QED

Theorem installed_covered_exit_fetch:
  entry_shape a b /\ create_layout a b /\ fn_has_code a b f /\
  fn_inst_ids_distinct f /\
  (!id. id IN frag_ids a b ==> ?j. MEM j (added_insts a b) /\ j.inst_id = id) ==>
  !bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
         i.inst_id NOTIN frag_ids a b
Proof
  rpt strip_tac >>
  qpat_x_assum `!id. _` (drule_then strip_assume_tac) >>
  drule_all entry_shape_added_frag_member >>
  disch_then (strip_assume_tac o MATCH_MP frag_code_prefix_or_emitted) >>
  `MEM bb f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  gvs[fn_has_code_def]
  >- metis_tac[prefix_exit_id_distinct] >>
  `bb.bb_label = b.cs_current_bb` by metis_tac[lookup_block_label] >>
  `blk.bb_label <> b.cs_current_bb` by
    (fs[create_layout_def] >> metis_tac[MEM_MAP]) >>
  `MEM blk f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by gvs[get_instruction_def, AllCaseEqs(), EL_MEM] >>
  `MEM i.inst_id (MAP (\x. x.inst_id) bb.bb_instructions) /\
   MEM i.inst_id (MAP (\x. x.inst_id) blk.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  `bb = blk` suffices_by (strip_tac >> gvs[]) >>
  fs[fn_inst_ids_distinct_def] >> drule all_distinct_flat_map_unique >>
  disch_then irule >> simp[] >> qexists_tac `i.inst_id` >> simp[]
QED
