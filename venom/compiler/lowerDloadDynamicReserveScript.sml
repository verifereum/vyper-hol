Theory lowerDloadDynamicReserve
Ancestors
  lowerDloadAllocation lowerDloadStackBound o1LowerDloadJointRestore
  lowerDloadDefs venomExecSemantics venomState finite_map pred_set list arithmetic words

Theorem ld_indexed_sum_bound:
  !xs ys. LIST_REL (\x y. weight x <= cap y) xs ys ==>
    SUM (MAP weight xs) <= SUM (MAP cap ys)
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem ld_reserve_push:
  ld_alloc_account keys (32 * SUM (MAP CARD ss)) A s t /\
  setup_callee fn args s = SOME u /\
  setup_callee gn vals t = SOME v /\ FINITE kc /\
  CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts caller.cf_fn)) /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) ss stk ==>
  ld_alloc_account kc (32 * SUM (MAP CARD (A::ss))) {} u v /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) (A::ss) (caller::stk)
Proof
  strip_tac >> conj_tac
  >- (drule_all ld_alloc_account_enter >> simp[LEFT_ADD_DISTRIB, ADD_COMM]) >>
  simp[]
QED

Theorem ld_reserve_pop:
  ld_alloc_account keys (32 * SUM (MAP CARD ss)) A s t /\
  bind_outputs os xs (adopt_return_fmp rs (merge_callee_state s u)) = SOME s' /\
  bind_outputs ot xt (adopt_return_fmp rt (merge_callee_state t v)) = SOME t' ==>
  ld_alloc_account keys (32 * SUM (MAP CARD ss)) A s' t'
Proof
  strip_tac >>
  qpat_x_assum `bind_outputs os _ _ = _` (mp_then Any SUBST1_TAC ld_bind_outputs_vars_only) >>
  qpat_x_assum `bind_outputs ot _ _ = _` (mp_then Any SUBST1_TAC ld_bind_outputs_vars_only) >>
  irule ld_alloc_account_transport >> goal_assum (drule_at Any) >>
  Cases_on `rs.iret_adopt_fmp` >> Cases_on `rt.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem ld_indexed_reserve_bound:
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 /\
  CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)) /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) ss stk ==>
  CARD A + SUM (MAP CARD ss) <= ctx_dload_count C
Proof
  strip_tac >>
  `SUM (MAP CARD ss) <= SUM (MAP (\f. LENGTH (FILTER
    (\i. i.inst_opcode = DLOAD) (fn_insts f.cf_fn))) stk)` by
    (ho_match_mp_tac ld_indexed_sum_bound >> simp[]) >>
  drule_all ld_stack_dload_count_bound >>
  simp[MAP_COMPOSE, combinTheory.o_DEF] >> decide_tac
QED

Theorem ld_indexed_reserve_nowrap:
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 /\
  CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn)) /\
  LIST_REL (\a f. CARD a <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD)
    (fn_insts f.cf_fn))) ss stk /\
  ld_alloc_account keys (32 * SUM (MAP CARD ss)) A s t /\
  dload_headroom_ok C fn inst s ==>
  t.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule_all ld_indexed_reserve_bound >> strip_tac >>
  drule ld_alloc_account_frontier >>
  gvs[dload_headroom_ok_def] >> decide_tac
QED
