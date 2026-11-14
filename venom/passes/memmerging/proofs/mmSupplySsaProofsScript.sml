(*
 * Memmerging — ssa_form preservation for the supply-threaded transform
 * (transform_function_supply).
 *)

Theory mmSupplySsaProofs
Ancestors
  mmTransform mmTransformSupply irSupply venomFnScheduleRunner venomWf venomInst
Libs
  listTheory

(* The inserted instructions (the load in front of a downsized 32-byte copy,
   the calldatasize in front of a memzero calldatacopy) take a fresh output
   var from the supply; every other instruction keeps its outputs or gets
   none. ir_supply_covers_fn puts the input's vars in irs_used_vars, and
   fresh_ir_var returns a name outside irs_used_vars and adds it there, so
   the fresh vars collide with nothing in the input or with each other. *)

Theorem mm_context_delete[local]:
  ALL_DISTINCT (L ++ X ++ R) ==> ALL_DISTINCT (L ++ R)
Proof
  simp[ALL_DISTINCT_APPEND, MEM_APPEND] >> metis_tac[]
QED

Theorem mm_context_fresh[local]:
  ALL_DISTINCT (L ++ X ++ R) /\
  list_subset (L ++ X ++ R) U /\ ~MEM v U ==>
  ALL_DISTINCT (L ++ [v] ++ R)
Proof
  simp[ALL_DISTINCT_APPEND, list_subset_def, EVERY_MEM, MEM_APPEND] >>
  metis_tac[]
QED

Theorem mm_context_coverage[local]:
  list_subset (L ++ X ++ R) U ==>
  list_subset (L ++ R) U /\
  list_subset (L ++ [v] ++ R) (v::U)
Proof
  simp[list_subset_def, EVERY_MEM, MEM_APPEND] >> metis_tac[]
QED

Theorem mm_outputs_covered_blocks:
  !bbs U.
  list_subset (FLAT (MAP block_ir_vars bbs)) U ==>
  list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) U
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND,
    list_subset_def, EVERY_APPEND, block_ir_vars_def] >>
  rpt strip_tac
  >- (rw[EVERY_MEM, MEM_FLAT, MEM_MAP] >>
      gvs[] >>
      qpat_x_assum `EVERY _ (FLAT (MAP inst_ir_vars _))` mp_tac >>
      simp[EVERY_MEM, MEM_FLAT, MEM_MAP, inst_ir_vars_def] >>
      disch_then (qspec_then `x` mp_tac) >>
      impl_tac >- (qexists_tac `i.inst_outputs ++ inst_uses i` >>
        simp[] >> metis_tac[MEM_APPEND]) >> simp[])
  >> gvs[GSYM list_subset_def] >> first_x_assum irule >> simp[]
QED

Theorem mm_outputs_covered_fn[local]:
  ir_supply_covers_fn s fn ==>
  list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))
    s.irs_used_vars
Proof
  simp[ir_supply_covers_fn_def, fn_ir_vars_def, fn_insts_def] >>
  metis_tac[mm_outputs_covered_blocks]
QED

Theorem mm_groups_supply_context[local]:
  apply_groups_inst_supply mode ns rm s inst = (out,t) /\
  ALL_DISTINCT (L ++ inst.inst_outputs ++ R) /\
  list_subset (L ++ inst.inst_outputs ++ R) s.irs_used_vars ==>
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) out) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) out) ++ R) t.irs_used_vars
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def,
      mk_load_inst_def, mk_mstore_from_load_def, fresh_inst_id_def]
  >- metis_tac[mm_context_delete]
  >- metis_tac[mm_context_coverage]
  >- metis_tac[mm_context_delete]
  >- metis_tac[mm_context_coverage]
  >- metis_tac[mm_context_delete]
  >- metis_tac[mm_context_coverage]
  >> drule fresh_ir_var_contract >> strip_tac >> gvs[] >>
  metis_tac[mm_context_fresh, mm_context_coverage]
QED

Theorem mm_memzero_supply_context[local]:
  apply_memzero_inst_supply ns rm s inst = (out,t) /\
  ALL_DISTINCT (L ++ inst.inst_outputs ++ R) /\
  list_subset (L ++ inst.inst_outputs ++ R) s.irs_used_vars ==>
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) out) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) out) ++ R) t.irs_used_vars
Proof
  rw[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def,
      mk_memzero_calldatacopy_def, fresh_inst_id_def]
  >- metis_tac[mm_context_delete]
  >- metis_tac[mm_context_coverage]
  >- metis_tac[mm_context_delete]
  >- metis_tac[mm_context_coverage]
  >> drule fresh_ir_var_contract >> strip_tac >> gvs[] >>
  metis_tac[mm_context_fresh, mm_context_coverage]
QED

Theorem mm_flat_map_supply_context[local]:
  (!s inst out t L R.
    f s inst = (out,t) /\
    ALL_DISTINCT (L ++ inst.inst_outputs ++ R) /\
    list_subset (L ++ inst.inst_outputs ++ R) s.irs_used_vars ==>
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) out) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) out) ++ R) t.irs_used_vars) ==>
  !xs s ys t L R.
    mm_flat_map_supply f s xs = (ys,t) /\
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) xs) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) xs) ++ R) s.irs_used_vars ==>
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) ys) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) ys) ++ R) t.irs_used_vars
Proof
  strip_tac >> Induct
  >- simp[mm_flat_map_supply_def] >>
  simp[mm_flat_map_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!s inst out t L R. _` drule >>
  disch_then (qspecl_then [`L`, `FLAT (MAP (\i. i.inst_outputs) xs) ++ R`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!s ys t L R. _` drule >>
  disch_then (qspecl_then [`L ++ FLAT (MAP (\i. i.inst_outputs) out)`, `R`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem mm_map_delete_context[local]:
  (!i. (g i).inst_outputs = i.inst_outputs \/ (g i).inst_outputs = []) ==>
  !xs L R U.
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) xs) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) xs) ++ R) U ==>
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) (MAP g xs)) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) (MAP g xs)) ++ R) U
Proof
  strip_tac >> Induct >- simp[] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `h` strip_assume_tac) >> simp[]
  >- (first_x_assum (qspecl_then [`L ++ h.inst_outputs`, `R`, `U`] mp_tac) >>
      simp[APPEND_ASSOC]) >>
  first_x_assum (qspecl_then [`L`, `R`, `U`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (gvs[ALL_DISTINCT_APPEND, MEM_APPEND] >> metis_tac[])
      >> gvs[list_subset_def, EVERY_MEM, MEM_APPEND] >> metis_tac[])
  >> simp[]
QED

Theorem mm_dload_context[local]:
  !L bb R U dfg.
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) U ==>
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs)
    (transform_block_dload dfg bb).bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs)
    (transform_block_dload dfg bb).bb_instructions) ++ R) U
Proof
  rpt gen_tac >> simp[transform_block_dload_def] >> strip_tac >>
  irule mm_map_delete_context >>
  conj_tac
  >- (gen_tac >> simp[transform_dload_inst_def] >>
      rpt CASE_TAC >> simp[mk_nop_from_def, mk_dloadbytes_inst_def]) >>
  simp[]
QED

Theorem mm_dload_blocks_context[local]:
  !bbs L R U.
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) ++ R) U ==>
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (transform_block_dload pairs) bbs))) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (transform_block_dload pairs) bbs))) ++ R) U
Proof
  Induct >- simp[fn_insts_blocks_def] >>
  simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  rpt gen_tac >> strip_tac >>
  qspecl_then [`L`, `h`,
    `FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) ++ R`, `U`, `pairs`]
    mp_tac mm_dload_context >>
  simp[APPEND_ASSOC] >> strip_tac >>
  first_x_assum (qspecl_then
    [`L ++ FLAT (MAP (\i. i.inst_outputs)
       (transform_block_dload pairs h).bb_instructions)`, `R`, `U`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem mm_mode_supply_context:
  transform_block_mode_supply dfg mode s bb = (bb',t) /\
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) s.irs_used_vars ==>
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions) ++ R) t.irs_used_vars
Proof
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule mm_flat_map_supply_context >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[mm_groups_supply_context]
QED

Theorem mm_memzero_supply_context_block:
  transform_block_memzero_supply dfg s bb = (bb',t) /\
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) s.irs_used_vars ==>
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions) ++ R) t.irs_used_vars
Proof
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule mm_flat_map_supply_context >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[mm_memzero_supply_context]
QED

Theorem mm_block_supply_context[local]:
  transform_block_supply dfg s bb = (bb',t) /\
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions) ++ R) s.irs_used_vars ==>
  ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions) ++ R) /\
  list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions) ++ R) t.irs_used_vars
Proof
  simp[transform_block_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all mm_memzero_supply_context_block >> strip_tac >>
  drule_all mm_mode_supply_context >> strip_tac >>
  drule_all mm_mode_supply_context >> strip_tac >>
  drule_all mm_mode_supply_context >> simp[]
QED

Theorem mm_index_supply_context:
  !bbs n s bb' t L R.
    n < LENGTH bbs /\
    transform_block_supply dfg s (EL n bbs) = (bb',t) /\
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) ++ R) s.irs_used_vars ==>
    ALL_DISTINCT (L ++ FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (LUPDATE bb' n bbs))) ++ R) /\
    list_subset (L ++ FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (LUPDATE bb' n bbs))) ++ R) t.irs_used_vars
Proof
  Induct >- simp[] >>
  Cases_on `n` >>
  simp[LUPDATE_def, fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  rpt gen_tac >> strip_tac
  >- (drule mm_block_supply_context >>
      disch_then (qspecl_then
        [`FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) ++ R`, `L`] mp_tac) >>
      simp[APPEND_ASSOC]) >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspecl_then
    [`L ++ FLAT (MAP (\i. i.inst_outputs) h.bb_instructions)`, `R`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem mm_function_supply_context[local]:
  transform_function_supply s fn = (fn',t) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
  list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) s.irs_used_vars ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn'))) /\
  list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn'))) t.irs_used_vars
Proof
  simp[transform_function_supply_def, transform_function_with_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL mmstep (fn,s) indices` >>
  qabbrev_tac `P = \(f,st).
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts f))) /\
    list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts f))) st.irs_used_vars` >>
  `!acc index. P acc ==> P (mmstep acc index)` by
    (qx_gen_tac `acc` >> PairCases_on `acc` >>
     simp[Abbr `P`, Abbr `mmstep`, fn_insts_def] >>
     rpt gen_tac >> strip_tac >>
     IF_CASES_TAC
     >- (qmatch_goalsub_abbrev_tac
           `MAP (transform_block_dload dps) acc0.fn_blocks` >>
         pairarg_tac >> simp[] >>
         qspecl_then [`acc0.fn_blocks`, `[]`, `[]`, `acc1.irs_used_vars`]
           mp_tac (Q.INST [`pairs` |-> `dps`] mm_dload_blocks_context) >>
         simp[] >> strip_tac >>
         gvs[AllCaseEqs()] >>
         `index < LENGTH (MAP (transform_block_dload dps) acc0.fn_blocks)` by simp[] >>
         drule mm_index_supply_context >>
         simp[EL_MAP] >> disch_then drule >>
         disch_then (qspecl_then [`[]`, `[]`] mp_tac) >> simp[]) >> simp[]) >>
  `!xs acc. P acc ==> P (FOLDL mmstep acc xs)` by
    (Induct >> simp[] >> metis_tac[]) >>
  strip_tac >>
  first_x_assum (qspecl_then [`COUNT_LIST (LENGTH fn.fn_blocks)`, `(fn,s)`] mp_tac) >>
  gvs[Abbr `P`]
QED

Theorem mm_preserves_ssa_form:
  ∀s fn fn' s'.
    ssa_form fn ∧ ir_supply_covers_fn s fn ∧
    transform_function_supply s fn = (fn', s') ⇒
    ssa_form fn'
Proof
  rpt gen_tac >> strip_tac >>
  drule mm_outputs_covered_fn >> strip_tac >>
  gvs[ssa_form_def] >> metis_tac[mm_function_supply_context]
QED
