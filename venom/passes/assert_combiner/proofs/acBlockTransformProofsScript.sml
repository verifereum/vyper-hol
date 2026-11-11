(* Supply-aware lookup boundaries for the assert combiner. *)
Theory acBlockTransformProofs
Ancestors
  acSupplyProofs assertCombinerDefs irSupplyFreshProps irSupply
  venomFnScheduleRunner venomInst passSharedDefs list pred_set
Libs
  listTheory

Theorem ac_transform_block_extends:
  ac_transform_block dfg su bb = (bb',su') ==>
  ir_supply_extends su su'
Proof
  simp[ac_transform_block_def] >>
  Cases_on `ac_merge_insts (ac_scan_block dfg bb.bb_instructions NONE) []
                su bb.bb_instructions` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ac_merge_insts_fresh >> simp[]
QED

(* The witnesses are the actual supplies at this block, not arbitrary
   supplies giving an extensionally equal transformed block. *)
Theorem ac_transform_blocks_lookup:
  !bbs su bbs' su' l bb.
  ac_transform_blocks dfg su bbs = (bbs',su') /\
  lookup_block l bbs = SOME bb ==>
  ?bb' s0 s1.
    lookup_block l bbs' = SOME bb' /\
    ac_transform_block dfg s0 bb = (bb',s1) /\
    ir_supply_extends su s0 /\ ir_supply_extends s0 s1 /\
    ir_supply_extends s1 su'
Proof
  Induct >> simp[ac_transform_blocks_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  Cases_on `ac_transform_block dfg su h` >> rename1 `_ = (bh,sh)` >>
  Cases_on `ac_transform_blocks dfg sh bbs` >> rename1 `_ = (bt,st)` >>
  simp[] >> strip_tac >> gvs[] >>
  `bh.bb_label = h.bb_label` by metis_tac[ac_transform_block_label] >>
  `ir_supply_extends su sh` by metis_tac[ac_transform_block_extends] >>
  `ir_supply_extends sh st` by metis_tac[ac_transform_blocks_fresh] >>
  Cases_on `h.bb_label = l` >> gvs[FIND_thm]
  >- (qexistsl [`su`, `sh`] >> simp[ir_supply_extends_refl]) >>
  first_x_assum drule >> simp[lookup_block_def] >>
  disch_then (qspecl_then [`l`,`bb`] mp_tac) >> simp[] >> strip_tac >>
  rename1 `ac_transform_block dfg s0 bb = (bx,s1)` >>
  qexistsl [`bx`, `s0`, `s1`] >> simp[] >>
  irule ir_supply_extends_trans >> qexists `sh` >> simp[]
QED

Theorem ac_transform_function_lookup:
  !su fn l bb.
  lookup_block l fn.fn_blocks = SOME bb ==>
  ?bb' s0 s1.
    lookup_block l (FST (ac_transform_function su fn)).fn_blocks = SOME bb' /\
    ac_transform_block (dfg_build_function fn) s0 bb = (bb',s1) /\
    bb'.bb_label = bb.bb_label /\
    ir_supply_extends su s0 /\ ir_supply_extends s0 s1 /\
    ir_supply_extends s1 (SND (ac_transform_function su fn)) /\
    (set s1.irs_used_vars DIFF set s0.irs_used_vars) SUBSET ac_fresh_vars su fn
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ac_transform_blocks (dfg_build_function fn) su fn.fn_blocks` >>
  rename1 `_ = (bbs,st)` >>
  drule ac_transform_blocks_lookup >> disch_then drule >> strip_tac >>
  rename1 `ac_transform_block (dfg_build_function fn) s0 bb = (bx,s1)` >>
  qexistsl [`bx`, `s0`, `s1`] >>
  simp[ac_transform_function_def, ac_fresh_vars_def] >>
  conj_tac >- metis_tac[ac_transform_block_label] >>
  fs[ir_supply_extends_def, list_subset_def, EVERY_MEM, SUBSET_DEF] >>
  metis_tac[]
QED

(* The original function remains covered by every later supply, whether or
   not those names were already bound in the initial machine state. *)
Theorem ac_supply_covers_fn_extends:
  ir_supply_covers_fn su fn /\ ir_supply_extends su su' ==>
  ir_supply_covers_fn su' fn
Proof
  simp[ir_supply_covers_fn_def, ir_supply_extends_def,
       list_subset_def, EVERY_MEM] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem ac_fresh_vars_original_operand:
  ir_supply_covers_fn su fn /\ MEM inst (fn_insts fn) /\
  MEM (Var v) inst.inst_operands ==>
  v NOTIN ac_fresh_vars su fn
Proof
  simp[ac_fresh_vars_def] >> rpt strip_tac >>
  `MEM v (fn_ir_vars fn)` by
    (fs[fn_ir_vars_def, blocks_ir_vars_flat, fn_insts_def] >>
     simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, inst_ir_vars_def,
          inst_uses_def, MEM_operand_vars_eq_Var] >> metis_tac[]) >>
  fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]
QED
