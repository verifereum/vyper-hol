(* Per-conjunct structural output interfaces, built before the step contract. *)
Theory fmpStepShape
Ancestors
  fmpStepStructural fmpStepLayout fmpStepOpaque fmpStepRestrictions
  fmpStepRetpcShape
  fmpLowerProps fmpWfDefs venomWf venomInst unitShapeDefs o1PassContract
  venomFnScheduleRunner irSupply list rich_list

Theorem fmp_lower_function_wf_function:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  o1_fn_shape ctx fn /\ ir_supply_covers_fn s fn ==> wf_function fn'
Proof
  strip_tac >>
  `wf_function fn /\ first_block_no_phi fn` by gvs[o1_fn_shape_def] >>
  drule_all fmp_lower_function_blocks_well_formed >> strip_tac >>
  drule_all fmp_lower_function_succs_closed >> strip_tac >>
  drule fmp_lower_function_preserves_labels >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks))` by
    gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  `EVERY (\bb. EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions) fn.fn_blocks` by
    gvs[ir_supply_covers_fn_def, fn_ir_inst_ids_def, block_ir_inst_ids_def,
      EVERY_FLAT, EVERY_MAP] >>
  drule_all fmp_lower_function_ids_distinct >> strip_tac >>
  simp[wf_function_def, fn_inst_ids_distinct_def] >>
  gvs[wf_function_def, EVERY_MEM, fn_has_entry_def] >>
  Cases_on `fn'.fn_blocks` >> gvs[fn_labels_def]
QED

Theorem fmp_lower_function_fn_shape_ok:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==> fn_shape_ok fn'
Proof
  strip_tac >>
  drule_all fmp_lower_function_opaque_use_ok >> strip_tac >>
  drule_all fmp_lower_function_retpc_shape_ok >> strip_tac >>
  drule fmp_lower_function_preserves_nonfmp_metadata >> strip_tac >>
  drule fmp_lower_function_preserves_entry_label >> strip_tac >>
  drule fmp_lower_function_preserves_labels >> strip_tac >>
  `EVERY inst_shape_ok (fn_insts fn)` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule_all fmp_lower_function_inst_shape_ok >> strip_tac >>
  gvs[fn_shape_ok_def, fn_identity_metadata_eq_def, o1_fn_shape_def] >>
  gvs[EVERY_MEM, fn_labels_def] >> rpt strip_tac >>
  `MEM bb.bb_label (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (fn th => rewrite_tac[GSYM th]) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem fmp_lower_function_label_map_sources_ok:
  label_map_sources_ok fn fn' []
Proof
  simp[label_map_sources_ok_def]
QED

Theorem fmp_lower_function_entry_restrictions:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn ==>
  (ctx.ctx_entry = SOME fn'.fn_name ==>
    entry_fn_no_return fn' /\ entry_fn_no_params fn')
Proof
  strip_tac >> drule fmp_lower_function_preserves_nonfmp_metadata >> strip_tac >>
  gvs[fn_identity_metadata_eq_def] >> strip_tac >>
  `entry_fn_no_return fn /\ entry_fn_no_params fn` by gvs[o1_fn_shape_def] >>
  conj_tac
  >- metis_tac[fmp_lower_function_entry_no_return] >>
  irule fmp_lower_function_entry_no_params >>
  qexistsl [`ctx`, `fn`, `s`, `s'`] >> simp[fn_is_context_entry_def]
QED

Theorem fmp_lower_function_nonentry_restrictions:
  fmp_lower_function ctx s fn = SOME (fn',s') /\ o1_fn_shape ctx fn ==>
  (ctx.ctx_entry <> SOME fn'.fn_name ==>
    EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn'))
Proof
  strip_tac >> drule fmp_lower_function_preserves_nonfmp_metadata >> strip_tac >>
  gvs[fn_identity_metadata_eq_def] >> strip_tac >>
  irule (SRULE[] fmp_lower_function_no_halt) >>
  qexistsl [`ctx`, `fn`, `s`, `s'`] >> gvs[o1_fn_shape_def]
QED
