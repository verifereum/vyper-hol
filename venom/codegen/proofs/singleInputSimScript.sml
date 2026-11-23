(* One-operand reordering and assignment preparation. *)
Theory singleInputSim
Ancestors
  emitOperandSim emitInputSim reorderSim mixedPrefixSim strongPrefixSim planAlign planWf
  stackOpSim stackPlanOps stackPlanGen stackPlanTypes stackModel planExec prefixExec
  codegenRel asmSem venomInst dfgDefs planSpillBounds doSwapSim
  finite_map indexedLists list rich_list arithmetic

Theorem simple_prefix_spill_wf:
  !ops initial_fmp lo ps.
    EVERY is_simple_stack_op ops ==> prefix_spill_wf initial_fmp lo ops ps
Proof
  Induct >> simp[prefix_spill_wf_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h` >> gvs[is_simple_stack_op_def, spill_op_wf_def]
QED

Theorem emit_one_input_prefix_spill_wf_owned:
  !opc nl op ps ops ps' initial_fmp lo.
    opc <> INVOKE /\ emit_one_input opc nl op ps = (ops,ps') /\
    (is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
    prefix_spill_wf initial_fmp lo ops ps
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (Cases_on `op` >> fs[is_var_operand_def] >> rename1 `Var v` >>
      Cases_on `FLOOKUP ps.ps_spilled (Var v)` >> gvs[] >>
      rename1 `FLOOKUP _ _ = SOME off` >>
      mp_tac (Q.SPECL [`opc`,`nl`,`v`,`ps`,`off`]
        emit_one_input_var_spilled_plan) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> simp_tac std_ss [LET_THM] >>
      Cases_on `MEM v nl` >> simp[] >> strip_tac >>
      gvs[prefix_spill_wf_def, spill_op_wf_def] >>
      qexists_tac `Var v` >> first_assum ACCEPT_TAC) >>
  irule simple_prefix_spill_wf >>
  mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`] emit_one_input_all_simple) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    rpt gen_tac >> strip_tac >> gvs[is_var_operand_def])) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem emit_single_input_not_spilled:
  emit_input_plan opc [op] nl ps = (ops,target) ==>
  ~is_var_operand op \/ FLOOKUP target.ps_spilled op = NONE
Proof
  rpt strip_tac >>
  drule emit_input_plan_vars_not_spilled >> simp[flookup_thm] >>
  metis_tac[]
QED

Theorem reorder_plan_one_postpop_wf:
  !alloc_base dfg op ps ops ps' dist.
    residual_budget_wf alloc_base [op] ps /\
    stack_get_depth op ps.ps_stack = SOME dist /\
    reorder_plan dfg [op] ps = (ops,ps') ==>
    ps'.ps_stack = stack_pop 1 ps'.ps_stack ++ [op] /\
    stack_peek 0 ps'.ps_stack = op /\
    plan_slots_bounded alloc_base (ps' with ps_stack := stack_pop 1 ps'.ps_stack) /\
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
    ALL_DISTINCT (stack_pop 1 ps'.ps_stack) /\
    DISJOINT (set (stack_pop 1 ps'.ps_stack)) (FDOM ps'.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `MEM op ps.ps_stack` by metis_tac[stack_get_depth_props, reorderPreparationInventoryPropsTheory.stack_peek_mem] >>
  `!x. LIST_ELEM_COUNT x [op] <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> Cases_on `x = op` >>
     gvs[LIST_ELEM_COUNT_THM, GSYM LIST_ELEM_COUNT_MEM]) >>
  `plan_state_residual_wf alloc_base [op] 1 ps' /\
   ps'.ps_stack = stack_pop 1 ps'.ps_stack ++ [op]` by
    (qspecl_then [`alloc_base`, `[op]`, `dfg`, `ps`, `ops`, `ps'`]
       mp_tac reorder_plan_materialised_arranged >> simp[]) >>
  `stack_peek 0 ps'.ps_stack = op` by
    (fs[plan_state_residual_wf_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `ps'.ps_stack = _` kall_tac >>
  mp_tac (Q.SPECL [`alloc_base`,`[op]`,`ps'`] plan_state_residual_wf_pop) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem stack_poke_zero_snoc:
  !stk old new. stack_poke 0 new (SNOC old stk) = SNOC new stk
Proof
  simp[stack_poke_def, LUPDATE_SNOC]
QED
