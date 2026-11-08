Theory genericInputReady
Ancestors
  inputPlanSim reorderSim stackPlanGen list rich_list sorting arithmetic

Theorem emit_input_plan_residual_budget_nil:
  !base ps opc operands nl iops ps1.
  residual_budget_wf base [] ps /\
  emit_input_plan opc operands nl ps = (iops,ps1) ==>
  residual_budget_wf base operands ps1
Proof
  metis_tac[emit_input_plan_residual_budget_wf, APPEND]
QED

Theorem perm_operand_counts:
  PERM xs ys ==> !x. LIST_ELEM_COUNT x xs = LIST_ELEM_COUNT x ys
Proof
  strip_tac >> gen_tac >> rewrite_tac[LIST_ELEM_COUNT_DEF] >>
  drule PERM_FILTER >> disch_then (qspec_then `(\y. y = x)` mp_tac) >>
  metis_tac[PERM_LENGTH]
QED

Theorem residual_budget_wf_perm:
  !xs ys base ps. PERM xs ys ==>
    (residual_budget_wf base xs ps <=> residual_budget_wf base ys ps)
Proof
  rpt strip_tac >> drule perm_operand_counts >>
  simp[residual_budget_wf_def]
QED

Theorem pending_inventory_wf_perm:
  PERM xs ys ==>
    (pending_inventory_wf xs ps <=> pending_inventory_wf ys ps)
Proof
  strip_tac >> drule perm_operand_counts >>
  simp[pending_inventory_wf_def]
QED

(* The swapped candidate in generate_emit_ops is the same multiset. *)
Theorem last_two_reorder_perm:
  !xs. 2 <= LENGTH xs ==>
    PERM xs (TAKE (LENGTH xs - 2) xs ++
      [EL (LENGTH xs - 1) xs; EL (LENGTH xs - 2) xs])
Proof
  gen_tac >> strip_tac >>
  qspec_then `xs` strip_assume_tac SNOC_CASES >> gvs[] >>
  rename1 `SNOC a ys` >>
  qspec_then `ys` strip_assume_tac SNOC_CASES >> gvs[] >>
  rename1 `SNOC a (SNOC b zs)` >>
  pure_rewrite_tac[SNOC_APPEND, GSYM APPEND_ASSOC, APPEND] >>
  simp[ADD1, TAKE_APPEND1, EL_APPEND_EQN] >>
  simp[PERM_DEF, FILTER_APPEND_DISTRIB] >> gen_tac >>
  Cases_on `a = b` >> gvs[] >>
  Cases_on `x = a` >> Cases_on `x = b` >> gvs[]
QED
