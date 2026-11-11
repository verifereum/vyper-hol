(* Multiplicity-aware charge of a compiler interval contained in one function. *)
Theory bodyIntCallCodeChargeBound
Ancestors
  bodyIntCallStagingCharge o1LowerDloadScratchCount
  fragExec loweringShapeDefs exprLoweringProps vyperCompiler list compileEnv rich_list

Theorem fn_has_code_added_inst:
  cs_extends sa sb /\ fn_has_code sa sb func /\
  MEM i (added_insts sa sb) ==> MEM i (fn_insts func)
Proof
  strip_tac >>
  qpat_x_assum `cs_extends sa sb` mp_tac >>
  simp[cs_extends_def] >> strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def, added_insts_def,
      state_insts_def, all_blocks_def] >>
  Cases_on `new = []`
  >- (gvs[IS_PREFIX_APPEND, DROP_APPEND2, MEM_APPEND] >>
      irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      simp[MEM_APPEND]) >>
  gvs[IS_PREFIX_APPEND, REVERSE_APPEND, MAP_APPEND, FLAT_APPEND,
      TAKE_LENGTH_APPEND, DROP_APPEND2] >>
  qpat_x_assum `MEM i (DROP _ _)` mp_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  pure_rewrite_tac[GSYM DROP_DROP_T] >>
  simp_tac std_ss [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  disch_then (mp_tac o MATCH_MP MEM_DROP_IMP) >>
  simp[MEM_APPEND, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  strip_tac
  >- (qpat_x_assum `!b. MEM b new ==> _` drule >>
      strip_tac >> irule lookup_block_fn_insts >> metis_tac[]) >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[MEM_APPEND]
QED

Theorem contained_interval_alloca_charge:
  cs_extends sa sb /\ fn_has_code sa sb func /\
  ALL_DISTINCT (added_insts sa sb) ==>
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (added_insts sa sb))) <=
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)))
Proof
  strip_tac >> irule ld_sum_members_bound >>
  conj_tac >- metis_tac[FILTER_ALL_DISTINCT] >>
  simp[EVERY_MEM, MEM_FILTER] >>
  metis_tac[fn_has_code_added_inst]
QED

Theorem function_alloca_charge_budget:
  MEM func ctx.ctx_functions ==>
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func))) <=
  unit_alloca_budget ctx
Proof
  strip_tac >> drule (iffLR MEM_SPLIT) >> strip_tac >>
  `alloca_size = alloca_lit_size` by
    simp[FUN_EQ_THM, alloca_size_def, alloca_lit_size_def] >>
  simp[unit_alloca_budget_def,
       MAP_APPEND, FLAT_APPEND, FILTER_APPEND_DISTRIB, SUM_APPEND,
       arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac
QED

Theorem compiler_interval_charge_budget:
  cs_extends sa sb /\ fn_has_code sa sb func /\
  ALL_DISTINCT (added_insts sa sb) /\ MEM func ctx.ctx_functions ==>
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sb))) <=
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sa))) +
  unit_alloca_budget ctx
Proof
  strip_tac >> drule_all contained_interval_alloca_charge >> strip_tac >>
  drule function_alloca_charge_budget >> strip_tac >>
  drule state_insts_cs_extends >>
  simp[FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND] >> decide_tac
QED
