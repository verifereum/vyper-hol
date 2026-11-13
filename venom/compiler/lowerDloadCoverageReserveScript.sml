Theory lowerDloadCoverageReserve
Ancestors
  lowerDloadDynamicReserve lowerDloadConfiguredCaps lowerDloadAllocation
  lowerDloadStackBound lowerDloadDefs ptrDiscipline
  venomState finite_map pred_set list arithmetic words

Theorem ld_configured_insert_reserve:
  keys = set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts gn))) DIFF
    set (MAP (\j. j.inst_id) (fn_insts fn)) /\
  lower_dload_function_supply fa fn = (gn,fb) /\ q IN keys /\
  ld_alloc_account keys (32 * SUM (MAP CARD ss)) A s t /\
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) ss stk ==>
  CARD (q INSERT A) + SUM (MAP CARD ss) <= ctx_dload_count C
Proof
  strip_tac >>
  drule ld_alloc_account_capacity >> strip_tac >>
  `q INSERT A SUBSET keys` by ASM_SET_TAC[] >>
  `CARD (q INSERT A) <= CARD keys` by metis_tac[CARD_SUBSET] >>
  drule lower_dload_configured_cap_bound >> strip_tac >>
  `CARD (q INSERT A) <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn))` by
    (gvs[] >> decide_tac) >>
  drule_all ld_indexed_reserve_bound >> simp[]
QED

Theorem ld_configured_scratch_headroom:
  keys = set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts gn))) DIFF
    set (MAP (\j. j.inst_id) (fn_insts fn)) /\
  lower_dload_function_supply fa fn = (gn,fb) /\ q IN keys /\
  ld_alloc_account keys (32 * SUM (MAP CARD ss)) A s t /\
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) ss stk /\ dload_headroom_ok C fn inst s ==>
  t.vs_alloca_next < dimword (:256) /\
  (FLOOKUP t.vs_allocas q = NONE ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  t.vs_alloca_next <= dyn_floor C s /\
  (FLOOKUP t.vs_allocas q = NONE ==> t.vs_alloca_next + 32 <= dyn_floor C s)
Proof
  strip_tac >>
  drule_all ld_configured_insert_reserve >> strip_tac >>
  drule ld_alloc_account_finite >> strip_tac >>
  drule ld_alloc_account_frontier >> strip_tac >>
  `CARD A <= CARD (q INSERT A)` by (Cases_on `q IN A` >> simp[CARD_INSERT]) >>
  `FLOOKUP t.vs_allocas q = NONE ==> q NOTIN A` by
    (strip_tac >> drule ld_alloc_account_domain >>
     disch_then (qspec_then `q` mp_tac o SRULE [EXTENSION]) >>
     Cases_on `q IN FDOM t.vs_allocas` >> fs[FLOOKUP_DEF]) >>
  `t.vs_alloca_next <= s.vs_alloca_next + 32 * ctx_dload_count C /\
   (q NOTIN A ==> t.vs_alloca_next + 32 <= s.vs_alloca_next + 32 * ctx_dload_count C)` by
    (Cases_on `q IN A` >> fs[CARD_INSERT] >> decide_tac) >>
  qpat_x_assum `dload_headroom_ok _ _ _ _` mp_tac >>
  rewrite_tac[dload_headroom_ok_def, dyn_floor_def, GSYM ctx_has_dalloca_def] >>
  Cases_on `ctx_has_dalloca C` >> asm_rewrite_tac[] >> strip_tac >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> decide_tac
QED
