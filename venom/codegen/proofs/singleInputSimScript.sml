(* One-operand reordering and assignment preparation.
   TOP-LEVEL: reorder_plan_one_shallow_venom_asm_rel. *)
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

Theorem reorder_plan_one:
  !dfg op ps. reorder_plan dfg [op] ps = reorder_one dfg [op] 0 op ps
Proof
  rpt gen_tac >> simp[reorder_plan_def, MAPi_def, MAPi_ACC_def, LET_THM] >>
  Cases_on `reorder_one dfg [op] 0 op ps` >> simp[]
QED

Theorem reorder_plan_one_shallow_ops:
  !dfg op ps ops ps' dist initial_fmp lo.
    stack_get_depth op ps.ps_stack = SOME dist /\ dist <= 16 /\
    reorder_plan dfg [op] ps = (ops,ps') ==>
    EVERY is_simple_stack_op ops /\ prefix_spill_wf initial_fmp lo ops ps
Proof
  rpt gen_tac >> strip_tac >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  pure_rewrite_tac[reorder_plan_one] >>
  Cases_on `dist = 0` >>
  Cases_on `operand_equiv dfg op (stack_peek 0 ps.ps_stack)` >>
  asm_simp_tac (srw_ss()) [reorder_one_def, LET_THM,
    stack_get_unfixed_depth_def, do_swap_def] >> strip_tac >>
  gvs[is_simple_stack_op_def, prefix_spill_wf_def, spill_op_wf_def]
QED

Theorem reorder_plan_one_shallow_venom_asm_rel:
  !dfg op ps ops ps' dist initial_fmp lo o2pc prog vs st.
    stack_get_depth op ps.ps_stack = SOME dist /\ dist <= 16 /\
    reorder_plan dfg [op] ps = (ops,ps') /\
    op <> dead_stack_marker /\
    (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
    (!op1 at. operand_equiv dfg op1 at ==>
      operand_val vs lo op1 = operand_val vs lo at) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `0 < LENGTH ps.ps_stack /\ 1 <= LENGTH ps.ps_stack` by decide_tac >>
  `prefix_wf lo (LENGTH ps.ps_stack) ops` by
    (mp_tac (Q.ISPECL [`dfg:dfg_analysis`,`[op:operand]`,
       `ps:plan_state`,`lo:(string,num) fmap`] reorder_plan_wf_len) >>
     asm_simp_tac (srw_ss()) [LET_THM] >> simp[]) >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (mp_tac (Q.SPECL [`dfg`,`op`,`ps`,`ops`,`ps'`,`dist`,`initial_fmp`,`lo`]
       reorder_plan_one_shallow_ops) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []) >>
  `EVERY is_prefix_op ops` by
    (drule prefix_wf_every_prefix_op >> simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`ops`,`initial_fmp`,`lo`,`o2pc`,`prog`,`ps`,`vs`,`st`]
    mixed_prefix_venom_asm_rel) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `~operand_equiv dfg op dead_stack_marker` by
    (qpat_x_assum `!at. operand_equiv dfg op at ==> _`
       (qspec_then `dead_stack_marker` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`dfg`,`[op]`,`0`,`op`,`ps`,`ops`,`ps'`,`lo`,`vs`,`dist`]
    reorder_one_shallow_sem_align) >>
  (impl_tac >- asm_simp_tac (srw_ss())
    [stack_get_unfixed_depth_def, GSYM reorder_plan_one]) >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  qexists_tac `st'` >> asm_rewrite_tac [] >>
  irule venom_asm_rel_sem_stack_transport >>
  qexists_tac `apply_prefix_ops initial_fmp lo ops ps` >> asm_simp_tac std_ss []
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
  `reorder_one dfg [op] 0 op ps = (ops,ps')` by
    asm_simp_tac std_ss [GSYM reorder_plan_one] >>
  `residual_budget_wf alloc_base [op] ps' /\ 1 <= LENGTH ps'.ps_stack` by
    (mp_tac (Q.SPECL [`dfg`,`[op]`,`0`,`op`,`ps`,`ops`,`ps'`,`alloc_base`]
       reorder_one_residual_budget_wf) >>
     asm_simp_tac (srw_ss()) []) >>
  `stack_peek 0 ps'.ps_stack = op` by
    (mp_tac (Q.SPECL [`dfg`,`[op]`,`0`,`op`,`ps`,`ops`,`ps'`]
       reorder_one_places) >>
     asm_simp_tac (srw_ss()) [stack_get_unfixed_depth_def]) >>
  `plan_state_residual_wf alloc_base [op] 0 ps'` by
    (mp_tac (Q.SPECL [`alloc_base`,`[op]`,`ps'`] residual_budget_wf_to_residual) >>
     asm_simp_tac (srw_ss()) []) >>
  `plan_state_residual_wf alloc_base [op] 1 ps'` by
    (mp_tac (Q.SPECL [`alloc_base`,`[op]`,`0`,`ps'`] plan_state_residual_wf_fix_next) >>
     asm_simp_tac (srw_ss()) []) >>
  `ps'.ps_stack = stack_pop 1 ps'.ps_stack ++ [op]` by
    (mp_tac (Q.ISPECL [`(ps':plan_state).ps_stack`,`[op:operand]`]
       fixed_suffix_decompose) >>
     asm_simp_tac (srw_ss()) []) >>
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
