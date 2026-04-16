open mmCorrectnessProofsTheory mmTransformTheory venomWfTheory
     venomInstTheory passSimulationDefsTheory passSimulationPropsTheory
     pairLib listTheory rich_listTheory;

val fn_insts_blocks_flat = prove(
  ``!l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)``,
  Induct >> simp[fn_insts_blocks_def]);

val flat_map_flat_map = prove(
  ``!f g l. FLAT (MAP f (FLAT (MAP g l))) =
            FLAT (MAP (FLAT o MAP f o g) l)``,
  gen_tac >> gen_tac >> Induct >>
  simp[FLAT_APPEND, MAP_APPEND]);

val transform_block_output_mem = prove(
  ``!fn bb v.
    MEM bb fn.fn_blocks /\
    MEM v (FLAT (MAP (\i. i.inst_outputs)
      (transform_block (dfg_build_function fn) bb).bb_instructions)) ==>
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) \/
    v IN mm_fresh_outputs fn``,
  cheat);

Theorem test:
  !fn. ssa_form fn /\ fn_inst_ids_distinct fn /\ mm_fresh_names_ok fn ==>
       ssa_form (transform_function fn)
Proof
  rpt strip_tac >>
  `transform_function fn =
   function_map_transform (transform_block (dfg_build_function fn)) fn`
    by simp[transform_function_eq] >>
  qabbrev_tac `dfg = dfg_build_function fn` >>
  fs[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
     function_map_transform_def, MAP_MAP_o, combinTheory.o_DEF] >>
  fs[flat_map_flat_map] >>
  pop_assum kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  cheat
QED
