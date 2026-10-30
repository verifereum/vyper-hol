(* Logical operand placement for the actual reorder loop.
   TOP-LEVEL: reorder_plan_materialised.
   Repeated operands retain the copies outside the already fixed suffix. *)
Theory reorderMaterialised
Ancestors
  reorderSim reorderStages foldlSim stackPlanOps stackPlanTypes stackModel
  indexedLists list rich_list finite_map arithmetic

Theorem reorder_step_materialised_counts:
  !alloc_base dfg pending idx op ps ops post dist.
    residual_budget_wf alloc_base pending ps /\
    idx < LENGTH pending /\ LENGTH pending <= LENGTH ps.ps_stack /\
    LENGTH pending <= 16 /\ MEM op pending /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    stack_get_unfixed_depth op (LENGTH pending - 1 - idx)
      (LENGTH pending) ps.ps_stack = SOME dist /\
    reorder_one dfg pending idx op ps = (ops,post) ==>
    !x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `!x. MEM x pending ==>
    LIST_ELEM_COUNT x post.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    (mp_tac (Q.SPECL [`dfg`,`pending`,`idx`,`op`,`ps`,`ops`,`post`,
       `alloc_base`,`dist`] reorder_one_materialised_counts) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []) >>
  qx_gen_tac `x` >> Cases_on `MEM x pending`
  >- (qpat_assum `!x. MEM x pending ==> _` (qspec_then `x` mp_tac) >>
      asm_simp_tac (srw_ss()) []) >>
  fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem reorder_materialised_step:
  !alloc_base dfg pending idx ps ops post.
    plan_state_residual_wf alloc_base pending idx ps /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    idx < LENGTH pending /\ LENGTH pending <= 16 /\
    reorder_one dfg pending idx (EL idx pending) ps = (ops,post) ==>
    plan_state_residual_wf alloc_base pending (SUC idx) post /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x post.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `residual_budget_wf alloc_base pending ps /\
   LENGTH pending <= LENGTH ps.ps_stack /\ idx <= LENGTH pending` by
    (fs[plan_state_residual_wf_def, residual_budget_wf_def] >> decide_tac) >>
  `MEM (EL idx pending) pending` by
    (simp[MEM_EL] >> qexists_tac `idx` >> simp[]) >>
  `?dist. stack_get_unfixed_depth (EL idx pending)
     (LENGTH pending - 1 - idx) (LENGTH pending) ps.ps_stack = SOME dist` by
    (drule_all materialised_pending_next_on_stack >> simp[]) >>
  `residual_budget_wf alloc_base pending post /\
   LENGTH pending <= LENGTH post.ps_stack` by
    (drule_all reorder_one_residual_budget_wf >> simp[]) >>
  `!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x post.ps_stack` by
    (drule_all reorder_step_materialised_counts >> simp[]) >>
  `plan_state_residual_wf alloc_base pending idx post` by
    (qpat_assum `residual_budget_wf alloc_base pending post`
       (strip_assume_tac o REWRITE_RULE [residual_budget_wf_def]) >>
     asm_simp_tac (srw_ss()) [plan_state_residual_wf_def] >>
     qx_gen_tac `i` >> strip_tac >>
     `stack_peek (LENGTH pending - 1 - i) post.ps_stack =
      stack_peek (LENGTH pending - 1 - i) ps.ps_stack` by
       (drule_all reorder_one_preserves_fixed >> simp[]) >>
     fs[plan_state_residual_wf_def]) >>
  `stack_peek (LENGTH pending - 1 - idx) post.ps_stack = EL idx pending` by
    (mp_tac (Q.SPECL [`dfg`,`pending`,`idx`,`EL idx (pending:operand list)`,
       `ps`,`ops`,`post`] reorder_one_places) >>
     (impl_tac >- asm_simp_tac (srw_ss()) []) >> simp_tac bool_ss []) >>
  asm_rewrite_tac [] >> irule plan_state_residual_wf_fix_next >>
  asm_rewrite_tac []
QED

Theorem reorder_materialised_steps:
  !remaining pending fixed alloc_base dfg ps ops post.
    DROP fixed pending = remaining /\
    plan_state_residual_wf alloc_base pending fixed ps /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    LENGTH pending <= 16 /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
      (MAPi (\i op. (i + fixed,op)) remaining) ps = (ops,post) ==>
    plan_state_residual_wf alloc_base pending (LENGTH pending) post /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x post.ps_stack)
Proof
  Induct_on `remaining`
  >- (simp[plan_steps_def] >> rpt strip_tac >> gvs[] >>
      `fixed = LENGTH pending` by
        (fs[plan_state_residual_wf_def] >> decide_tac) >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `fixed < LENGTH pending` by
    (qpat_assum `DROP fixed pending = _`
       (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >> simp[] >> decide_tac) >>
  `EL fixed pending = h` by
    (mp_tac (Q.ISPECL [`fixed:num`,`pending:operand list`] HD_DROP) >>
     asm_simp_tac (srw_ss()) []) >>
  `DROP (SUC fixed) pending = remaining` by simp[DROP_SUC] >>
  `plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
     ((fixed,h)::MAPi (\i op. (i + SUC fixed,op)) remaining) ps = (ops,post)` by
    (qpat_assum `plan_steps _ _ ps = _`
       (mp_tac o SIMP_RULE (srw_ss()) [MAPi_def, combinTheory.o_DEF, ADD_CLAUSES]) >>
     asm_simp_tac (srw_ss()) [ADD_CLAUSES]) >>
  pop_assum (mp_tac o CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV) o
    MATCH_MP plan_steps_cons_result) >>
  disch_then (qx_choose_then `step_ops` (qx_choose_then `mid`
    (qx_choose_then `rest_ops` strip_assume_tac))) >>
  `plan_state_residual_wf alloc_base pending (SUC fixed) mid /\
   (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x mid.ps_stack)` by
    (mp_tac (Q.SPECL [`alloc_base`,`dfg`,`pending`,`fixed`,`ps`,`step_ops`,`mid`]
       reorder_materialised_step) >>
     (impl_tac >- asm_simp_tac (srw_ss()) []) >> simp_tac bool_ss []) >>
  first_x_assum (qspecl_then [`pending`,`SUC fixed`,`alloc_base`,`dfg`,`mid`,
    `rest_ops`,`post`] mp_tac) >> asm_rewrite_tac []
QED

Theorem reorder_plan_materialised:
  !alloc_base dfg pending ps ops post.
    residual_budget_wf alloc_base pending ps /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    reorder_plan dfg pending ps = (ops,post) ==>
    plan_state_residual_wf alloc_base pending (LENGTH pending) post /\
    post.ps_stack = stack_pop (LENGTH pending) post.ps_stack ++ pending
Proof
  rpt gen_tac >> strip_tac >>
  `plan_state_residual_wf alloc_base pending 0 ps` by
    (drule_all residual_budget_wf_to_residual >> simp[]) >>
  mp_tac (Q.SPECL [`pending`,`pending`,`0`,`alloc_base`,`dfg`,`ps`,`ops`,`post`]
    reorder_materialised_steps) >>
  (impl_tac >- asm_simp_tac (srw_ss()) [GSYM reorder_plan_eq_plan_steps]) >>
  strip_tac >> asm_rewrite_tac [] >>
  irule fixed_suffix_decompose >> fs[plan_state_residual_wf_def]
QED
