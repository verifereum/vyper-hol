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

Theorem mm_preserves_ssa_form_test:
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
  gvs[ALL_DISTINCT_APPEND] >> rpt conj_tac
  (* 1. Per-block ALL_DISTINCT *)
  >- (
    (* Each output is original or fresh. Original outs are ALL_DISTINCT
       (from assumption). Fresh outs ∉ original (mm_fresh_names_ok).
       Show no output appears twice by showing the transformed output list
       is a sub-multiset of (original block outs ∪ mm_fresh_outputs). *)
    rw[ALL_DISTINCT_FILTER] >> rpt strip_tac >>
    `MEM x (FLAT (MAP (\i. i.inst_outputs) h.bb_instructions)) \/
     x IN mm_fresh_outputs fn` by
      (irule transform_block_output_mem >> simp[Abbr `dfg`] >>
       simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
    gvs[]
    (* x is an original output of h *)
    >- (`FILTER ($= x) (FLAT (MAP (\i. i.inst_outputs) h.bb_instructions)) = [x]`
          by fs[ALL_DISTINCT_FILTER] >>
        cheat (* need: count of x in transform ≤ count in original *))
    (* x is fresh — show it appears exactly once *)
    >> cheat)
  (* 2. Rest by IH *)
  >- (first_x_assum irule >> simp[] >> metis_tac[])
  (* 3. Cross-block: x in h's transform ⟹ x not in rest's transform *)
  >> rpt strip_tac >> spose_not_then strip_assume_tac >>
  `MEM e (FLAT (MAP (\i. i.inst_outputs) h.bb_instructions)) \/
   e IN mm_fresh_outputs fn` by
    (irule transform_block_output_mem >> simp[Abbr `dfg`] >>
     simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM bb2 bbs` >>
  `MEM e (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions)) \/
   e IN mm_fresh_outputs fn` by
    (irule transform_block_output_mem >> simp[Abbr `dfg`] >>
     simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  gvs[]
  (* Case: both original — contradicts cross-block disjoint *)
  >- metis_tac[MEM_FLAT, MEM_MAP]
  (* Case: h original, bb2 fresh — contradicts mm_fresh_names_ok *)
  >- (fs[mm_fresh_names_ok_def, IN_DISJOINT, fn_insts_def,
         fn_insts_blocks_flat] >> metis_tac[MEM_FLAT, MEM_MAP])
  (* Case: h fresh, bb2 original *)
  >- (fs[mm_fresh_names_ok_def, IN_DISJOINT, fn_insts_def,
         fn_insts_blocks_flat] >> metis_tac[MEM_FLAT, MEM_MAP])
  (* Case: both fresh — needs fn_inst_ids_distinct + naming *)
  >> cheat
QED
