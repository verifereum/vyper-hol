(* Count caller arguments using distinct explicit staging buffers. *)
Theory bodyIntCallArgumentCountInterface
Ancestors
  bodyIntCallStagingAllocationSelection bodyIntCallArgumentCount
  bodyIntCallCodeChargeBound o1LowerDloadScratchCount
  combinatorics sptree exprLoweringProps loweringShapeDefs list words
  bodyIntCallSeamPrefixSupport bodyIntCallPkgEntryMetadata bodySim
  compileVyper vyperCompiler

Theorem staging_selected_charge_lower:
  !ais. EVERY (\i. 32 <= alloca_lit_size i) ais ==>
    32 * LENGTH ais <= SUM (MAP alloca_lit_size ais)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum drule >>
  simp[arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem staging_argument_alloca_charge:
  compile_stage_intcall_args ce vals flags tys sa = (ops,sb) /\
  LENGTH vals = LENGTH flags /\ LENGTH vals = LENGTH tys /\
  EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256)) tys /\
  fn_has_code sa sb func ==>
  32 * LENGTH (FILTER (\b. ~b) flags) <=
    SUM (MAP alloca_lit_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)))
Proof
  strip_tac >> drule_all staging_explicit_allocations >> strip_tac >>
  `cs_extends sa sb` by
    metis_tac[ci_mono_compile_stage_intcall_args, ci_mono_def, pairTheory.SND] >>
  `EVERY (\i. 32 <= alloca_lit_size i) ais` by fs[EVERY_MEM] >>
  drule staging_selected_charge_lower >> strip_tac >>
  `SUM (MAP alloca_lit_size ais) <=
     SUM (MAP alloca_lit_size
       (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)))` by
    (irule ld_sum_members_bound >>
     conj_tac >- metis_tac[ALL_DISTINCT_MAP] >>
     fs[EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     irule fn_has_code_added_inst >> goal_assum (drule_at Any) >> simp[]) >>
  decide_tac
QED

Theorem staged_function_argument_count:
  compile_stage_intcall_args ce vals flags tys sa = (ops,sb) /\
  LENGTH vals = LENGTH flags /\ LENGTH vals = LENGTH tys /\
  EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256)) tys /\
  LENGTH (FILTER I flags) <= MAX_STACK_ARGS /\
  fn_has_code sa sb func /\ MEM func ctx.ctx_functions /\
  unit_alloca_budget ctx < dimword (:256) ==>
  1 + LENGTH tys < dimword (:256)
Proof
  strip_tac >> drule_all staging_argument_alloca_charge >> strip_tac >>
  drule function_alloca_charge_budget >> strip_tac >>
  irule staging_charge_argument_count >> qexists_tac `flags` >>
  simp[] >> decide_tac
QED

Theorem body_intcall_context_alloca_budget:
  !tops ctx ce cx. bodySim$body_inv tops ctx ce cx ==>
    unit_alloca_budget ctx < dimword (:256)
Proof
  simp[body_inv_def] >> rpt strip_tac >>
  Cases_on `cx.in_deploy` >> gvs[]
  >- (qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
      simp[lower_vyper_deploy_unit_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs()] >> strip_tac >>
      drule run_deploy_lowering_alloca_budget >> simp[]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >> strip_tac >>
  drule run_lowering_alloca_budget >> simp[]
QED

Theorem body_intcall_staging_argument_count:
  !tops ctx ce cx mut nr rr name args dflts ret bd rcn rbs flags
    es env es0 vals sa ops sb func s0.
  bodySim$body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret bd) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,flags) /\
  EVERY (\e. expr_body_pre ce cx env e es0 /\ ~expr_has_effect e) es /\
  LENGTH vals = LENGTH es /\ LENGTH es = LENGTH args /\
  compile_stage_intcall_args ce vals flags (MAP expr_type es) sa = (ops,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func ce cx es0 s0 ==>
  1 + LENGTH args < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_internal_decl_pass_flags >> strip_tac >>
  `LENGTH flags = LENGTH args` by simp[compileEnvTheory.LENGTH_compute_pass_via_stack] >>
  `LENGTH (FILTER I flags) <= MAX_STACK_ARGS` by
    (gvs[] >> qmatch_goalsub_abbrev_tac `compute_pass_via_stack ts n` >>
     qspecl_then [`ts`,`n`] mp_tac compute_pass_via_stack_true_bound >> decide_tac) >>
  `EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256))
     (MAP expr_type es)` by
    (fs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     drule intcall_arg_staging_layout >> simp[arithmeticTheory.MAX_DEF, dimword_def]) >>
  `MEM func ctx.ctx_functions` by
    metis_tac[stmt_state_rel_def, alloca_room_def, venomInstTheory.lookup_function_MEM] >>
  drule body_intcall_context_alloca_budget >> strip_tac >>
  `LENGTH vals = LENGTH flags /\ LENGTH vals = LENGTH (MAP expr_type es)` by simp[] >>
  drule_all staged_function_argument_count >> simp[]
QED
