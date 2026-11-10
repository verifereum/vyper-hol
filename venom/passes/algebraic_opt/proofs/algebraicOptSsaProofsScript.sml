Theory algebraicOptSsaProofs
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner venomInst
  algebraicOptSupplyProofs algebraicOptShapeProofs
  algebraicOptSsaMainProofs algebraicOptSsaCmpProofs
  list pred_set

Theorem ao_offset_blocks_projection[local]:
  !bbs.
    MAP (\i. i.inst_id) (fn_insts_blocks
      (MAP (\bb. bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions) bbs)) =
      MAP (\i. i.inst_id) (fn_insts_blocks bbs) /\
    MAP (\i. i.inst_outputs) (fn_insts_blocks
      (MAP (\bb. bb with bb_instructions := MAP ao_handle_offset_inst bb.bb_instructions) bbs)) =
      MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF,
                 ao_handle_offset_inst_shape]
QED

Theorem ao_preserves_ssa_form_proof:
  !sup fn fn' sup'.
    wf_function fn /\
    ssa_form fn /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') ==>
    ssa_form fn'
Proof
  rpt gen_tac >> strip_tac >> rename1 `ir_supply_covers_fn s fn` >>
  drule ao_initial_output_coverage >> strip_tac >>
  drule ao_initial_inst_id_bound >> strip_tac >>
  drule ao_initial_inst_ids_distinct >> strip_tac >>
  qpat_x_assum `ao_transform_function_supply _ _ = _` mp_tac >>
  pure_rewrite_tac[ao_transform_function_supply_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `ao_transform_blocks_supply dfg ra targets s bbs` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s bbs = (bs,s1)` >>
  simp[] >> strip_tac >>
  drule ao_transform_blocks_supply_frame >>
  disch_then (qspecl_then [`{}`,`{}`] mp_tac) >>
  impl_tac >-
    (`EVERY (\id. id < s.irs_next_inst)
       (MAP (\i. i.inst_id) (fn_insts_blocks bbs))` by
       (simp[Abbr `bbs`, ao_offset_blocks_projection] >>
        gvs[fn_insts_def, EVERY_MAP]) >>
     gvs[Abbr `bbs`, ao_offset_blocks_projection, EVERY_MAP,
         ssa_form_def, fn_insts_def]) >>
  strip_tac >> drule ao_cmp_flip_function_supply_ssa >>
  simp[ssa_form_def, fn_insts_def]
QED
