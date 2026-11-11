(* Count caller arguments using distinct explicit staging buffers. *)
Theory bodyIntCallArgumentCountInterface
Ancestors
  bodyIntCallStagingAllocationSelection bodyIntCallArgumentCount
  bodyIntCallCodeChargeBound o1LowerDloadScratchCount
  combinatorics sptree exprLoweringProps loweringShapeDefs list words

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
