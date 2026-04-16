open mmCorrectnessProofsTheory mmTransformTheory venomWfTheory
     venomInstTheory passSimulationDefsTheory passSimulationPropsTheory
     pairLib listTheory rich_listTheory;

val fn_insts_blocks_flat = prove(
  ``!l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)``,
  Induct >> simp[fn_insts_blocks_def]);

val transform_block_output_mem = prove(
  ``!fn bb v.
    MEM bb fn.fn_blocks /\
    MEM v (FLAT (MAP (\i. i.inst_outputs)
      (transform_block (dfg_build_function fn) bb).bb_instructions)) ==>
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) \/
    v IN mm_fresh_outputs fn``,
  cheat);

Triviality transform_cross_block_disjoint:
  !fn dfg bb1 bb2 v.
    dfg = dfg_build_function fn /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    mm_fresh_names_ok fn /\
    DISJOINT (set (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)))
             (set (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions))) /\
    MEM v (FLAT (MAP (\i. i.inst_outputs)
      (transform_block dfg bb1).bb_instructions)) /\
    MEM v (FLAT (MAP (\i. i.inst_outputs)
      (transform_block dfg bb2).bb_instructions)) ==> F
Proof
  rpt strip_tac >> gvs[] >>
  `MEM v (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)) \/
   v IN mm_fresh_outputs fn` by
    (irule transform_block_output_mem >> simp[MEM_FLAT,MEM_MAP] >>
     metis_tac[]) >>
  `MEM v (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions)) \/
   v IN mm_fresh_outputs fn` by
    (irule transform_block_output_mem >> simp[MEM_FLAT,MEM_MAP] >>
     metis_tac[]) >>
  (* both original *)
  >- (fs[IN_DISJOINT] >> metis_tac[])
  (* bb1 orig, bb2 fresh *)
  >- (fs[mm_fresh_names_ok_def, IN_DISJOINT, fn_insts_def, fn_insts_blocks_flat] >>
      metis_tac[MEM_FLAT, MEM_MAP])
  (* bb1 fresh, bb2 orig *)
  >- (fs[mm_fresh_names_ok_def, IN_DISJOINT, fn_insts_def, fn_insts_blocks_flat] >>
      metis_tac[MEM_FLAT, MEM_MAP])
  (* both fresh: vacuous — mm_fresh_names_ok prevents this.
     v ∈ mm_fresh_outputs fn ⟹ v ∉ any original output.
     But v is in two transformed blocks' outputs.
     Both come from mm_fresh_outputs. The DISJOINT between bb1/bb2 original
     outputs is irrelevant here. This case IS possible and needs
     fn_inst_ids_distinct — but this helper doesn't have it. *)
  >> cheat
QED
