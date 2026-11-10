(*
 * Planner reorder facts used by the lineage inventory: inventory
 * monotonicity and spill-map preservation through reorder_one,
 * reduce_depth_plan and reorder_plan, and the stronger forms of
 * reorderSim's spill-candidate and length-floor lemmas.
 *)

Theory fnPlanLineageReorder
Ancestors
  reorderSim
  foldlSim doSwapSim spillSim instSimHelpers strongPrefixSim planSpillBounds dfgDefs
  stackOpSim mixedPrefixSim planAlign emitInputSim
  stackPlanGen stackPlanOps stackPlanTypes stackModel
  codegenRel asmSem planExec planWf
  indexedLists list rich_list finite_map arithmetic

Theorem do_spill_at_spilled_update:
  !d ps ops ps'.
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    do_spill_at d ps = (ops,ps') ==>
    ?off. ps'.ps_spilled =
      ps.ps_spilled |+ (stack_peek d ps.ps_stack,off)
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_stack <> []` by (strip_tac >> gvs[]) >>
  Cases_on `d = 0`
  >- (gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
      Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >> metis_tac[]) >>
  `stack_peek 0 (stack_swap d ps.ps_stack) =
   stack_peek d ps.ps_stack` by
    (simp[stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE] >>
     IF_CASES_TAC >> gvs[] >> decide_tac) >>
  gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >> metis_tac[]
QED

Theorem select_spill_candidate_var_not_pending:
  !stk pending target_dist target_len cand.
    select_spill_candidate stk pending target_dist target_len = SOME cand ==>
    ~MEM (stack_peek cand stk) pending /\
    is_var_operand (stack_peek cand stk)
Proof
  rpt gen_tac >> strip_tac >>
  fs[select_spill_candidate_def, LET_THM] >>
  imp_res_tac FIND_SOME_MEM >> gvs[]
QED

Theorem reduce_depth_plan_inventory_mono:
  !fuel pending target_op f ps ops ps' base x.
    residual_budget_wf base pending ps /\
    reduce_depth_plan fuel pending target_op f (LENGTH pending) ps =
      (ops,ps') ==>
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps'.ps_stack +
      (if x IN FDOM ps'.ps_spilled then 1 else 0)
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f (LENGTH pending)
              ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < LENGTH pending` >> gvs[] >>
  Cases_on `x' <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x'
              (LENGTH pending)` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  `~MEM (stack_peek cand ps.ps_stack) pending` by
    metis_tac[select_spill_candidate_var_not_pending] >>
  `stack_peek cand ps.ps_stack NOTIN FDOM ps.ps_spilled` by
    (drule_all select_spill_candidate_not_spilled >> simp[]) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[residual_budget_wf_def] >>
  `!y. LIST_ELEM_COUNT y ps1.ps_stack +
       (if y IN FDOM ps1.ps_spilled then 1 else 0) =
       LIST_ELEM_COUNT y ps.ps_stack +
       (if y IN FDOM ps.ps_spilled then 1 else 0)` by
    (qspecl_then [`cand`, `ps`, `spill_ops`, `ps1`] mp_tac
       do_spill_at_inventory_count >>
     ASM_REWRITE_TAC[]) >>
  `residual_budget_wf base' pending ps1` by
    metis_tac[residual_budget_wf_do_spill_at] >>
  Cases_on `reduce_depth_plan fuel pending target_op f
              (LENGTH pending) ps1` >> gvs[] >>
  first_x_assum
    (qspecl_then [`pending`, `target_op`, `f`, `ps1`, `q`, `ps'`,
                  `base'`, `x`] mp_tac) >>
  simp[] >>
  qpat_assum `!y. _` (qspec_then `x` assume_tac) >>
  decide_tac
QED

Theorem reduce_depth_plan_target_length_floor:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') ==>
    MIN (MAX 17 target_len) (LENGTH ps.ps_stack) <= LENGTH ps'.ps_stack
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >> pairarg_tac >> simp[] >>
  rename1 `do_spill_at x' ps = (spill_ops, ps1)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `x' < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack - 1` by (
    qspecl_then [`x'`, `ps`] mp_tac do_spill_at_stack_length >>
    simp[] >> gvs[]) >>
  `target_len <= x'` by metis_tac[select_spill_candidate_below_target] >>
  first_x_assum
    (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`, `ps1`,
                  `rest_ops`, `ps'`] mp_tac) >>
  simp[] >> Cases_on `x <= 16` >> gvs[MIN_DEF, MAX_DEF] >> decide_tac
QED

Theorem reorder_one_inventory_mono:
  !dfg pending idx op ps ops ps' base.
    residual_budget_wf base pending ps /\ idx < LENGTH pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    reorder_one dfg pending idx op ps = (ops,ps') ==>
    !y. LIST_ELEM_COUNT y ps.ps_stack +
      (if y IN FDOM ps.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT y ps'.ps_stack +
      (if y IN FDOM ps'.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `residual_budget_wf base' pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (qspecl_then [`base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps`]
       mp_tac reorder_restore_residual_budget_wf >> simp[] >> gvs[]) >>
  `!y. LIST_ELEM_COUNT y ps.ps_stack +
       (if y IN FDOM ps.ps_spilled then 1 else 0) <=
       LIST_ELEM_COUNT y ps1.ps_stack +
       (if y IN FDOM ps1.ps_spilled then 1 else 0)` by
    (gen_tac >> qspecl_then [`op`, `LENGTH pending - (idx + 1)`,
       `LENGTH pending`, `ps`, `y`] mp_tac reorder_restore_inventory_mono >> gvs[]) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf base' pending ps2 /\
   LENGTH pending <= LENGTH ps2.ps_stack` by
    (Cases_on `x > 16` >> gvs[] >> conj_tac
     >- (drule_all reduce_depth_plan_residual_budget_wf >> simp[]) >>
     drule reduce_depth_plan_target_length_floor >> simp[]) >>
  `!y. LIST_ELEM_COUNT y ps1.ps_stack +
       (if y IN FDOM ps1.ps_spilled then 1 else 0) <=
       LIST_ELEM_COUNT y ps2.ps_stack +
       (if y IN FDOM ps2.ps_spilled then 1 else 0)` by
    (gen_tac >> Cases_on `x > 16` >> gvs[] >>
     drule_all reduce_depth_plan_inventory_mono >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[LESS_EQ_TRANS]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  `dist < LENGTH ps2.ps_stack /\ stack_peek dist ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[LESS_EQ_TRANS]) >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >>
      simp[stack_poke_exchange_multiplicity] >> metis_tac[LESS_EQ_TRANS]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `spill_alloc_layout_wf ps2.ps_alloc ps2.ps_spilled` by
    fs[residual_budget_wf_def] >>
  drule_all do_swap_multiplicity_layout >> strip_tac >>
  `residual_budget_wf base' pending ps3` by
    metis_tac[residual_budget_wf_do_swap] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `spill_alloc_layout_wf ps3.ps_alloc ps3.ps_spilled` by
    fs[residual_budget_wf_def] >>
  `LENGTH pending - (idx + 1) < LENGTH ps3.ps_stack` by decide_tac >>
  qpat_x_assum `do_swap _ ps3 = _` mp_tac >>
  disch_then (mp_then Any mp_tac do_swap_multiplicity_layout) >>
  simp[] >> strip_tac >> metis_tac[LESS_EQ_TRANS]
QED

Theorem reorder_one_target_length:
  !dfg targets idx op ps ops qs.
    LENGTH targets <= LENGTH ps.ps_stack /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    LENGTH targets <= LENGTH qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  rename1 `_ = (restore_ops, ps1)` >>
  `LENGTH targets <= LENGTH ps1.ps_stack` by
    (gvs[AllCaseEqs()] >>
     qspecl_then [`op`, `ps`] mp_tac do_restore_length >> simp[] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps1.ps_stack` >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >> pairarg_tac >> simp[] >>
  rename1 `_ = (reduce_ops, ps2)` >>
  `LENGTH targets <= LENGTH ps2.ps_stack` by
    (gvs[AllCaseEqs()] >> drule reduce_depth_plan_target_length_floor >>
     simp[MIN_DEF, MAX_DEF] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps2.ps_stack` >- (simp[] >> strip_tac >> gvs[]) >>
  `x' < LENGTH ps2.ps_stack` by metis_tac[stack_get_unfixed_depth_bound] >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `x' = LENGTH targets - (idx + 1)`
  >- (simp[] >> strip_tac >> gvs[]) >>
  simp[] >> IF_CASES_TAC
  >- (simp[stack_poke_def] >> strip_tac >> gvs[]) >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qspecl_then [`x'`, `ps2`] mp_tac do_swap_length >>
  qspecl_then [`LENGTH targets - (idx + 1)`, `ps3`] mp_tac do_swap_length >>
  simp[] >> decide_tac
QED

Theorem reorder_fold_target_length[local]:
  !items dfg targets acc ps ops qs.
    LENGTH targets <= LENGTH ps.ps_stack /\
    FOLDL (\(ops,ps) (idx,op).
      (\(step_ops,ps'). (ops ++ step_ops,ps'))
        (reorder_one dfg targets idx op ps)) (acc,ps) items = (ops,qs) ==>
    LENGTH targets <= LENGTH qs.ps_stack
Proof
  Induct >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  PairCases_on `h` >> gvs[] >>
  Cases_on `reorder_one dfg targets h0 h1 ps` >> gvs[] >>
  drule_all reorder_one_target_length >> strip_tac >>
  first_x_assum irule >> qexistsl [`acc ++ q`, `dfg`, `ops`, `r`] >> simp[]
QED

Theorem reorder_plan_target_length:
  !dfg targets ps ops qs.
    LENGTH targets <= LENGTH ps.ps_stack /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    LENGTH targets <= LENGTH qs.ps_stack
Proof
  rpt gen_tac >> simp[reorder_plan_def] >> strip_tac >>
  irule reorder_fold_target_length >>
  qexistsl [`[]`, `dfg`, `MAPi (\i op. (i,op)) targets`, `ops`, `ps`] >>
  simp[]
QED

Theorem reduce_depth_plan_not_spilled:
  !fuel pending op f n ps y.
    MEM y pending /\ y NOTIN FDOM ps.ps_spilled ==>
    y NOTIN FDOM (SND (reduce_depth_plan fuel pending op f n ps)).ps_spilled
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < n` >> gvs[] >>
  Cases_on `x <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x n` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> decide_tac) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    (drule_all select_spill_candidate_bound >> simp[]) >>
  `~MEM (stack_peek cand ps.ps_stack) pending` by
    metis_tac[select_spill_candidate_var_not_pending] >>
  `y NOTIN FDOM ps1.ps_spilled` by
    (drule_all do_spill_at_spilled_update >> strip_tac >>
     gvs[finite_mapTheory.FDOM_FUPDATE] >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  first_x_assum (drule_then (drule_then mp_tac)) >>
  disch_then (qspecl_then [`op`, `f`, `n`] mp_tac) >> simp[]
QED

Theorem reorder_one_pending_not_spilled:
  !dfg pending idx op ps y.
    MEM y pending /\ y NOTIN FDOM ps.ps_spilled ==>
    y NOTIN FDOM (SND (reorder_one dfg pending idx op ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `y NOTIN FDOM ps1.ps_spilled` by
    (Cases_on `stack_get_unfixed_depth op
       (LENGTH pending - (idx + 1)) (LENGTH pending) ps.ps_stack` >>
     gvs[] >> Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
     drule do_restore_preserves_not_spilled >>
     disch_then (qspec_then `op` mp_tac) >> simp[]) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >>
  `y NOTIN FDOM ps2.ps_spilled` by
    (Cases_on `x > 16` >> gvs[] >>
     drule_all reduce_depth_plan_not_spilled >>
     disch_then (qspecl_then [`LENGTH ps1.ps_stack`, `op`,
       `LENGTH pending - (idx + 1)`, `LENGTH pending`] mp_tac) >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[] >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[] >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> simp[] >>
  TRY (Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]) >>
  rpt (pairarg_tac >> simp[]) >>
  qspecl_then [`dist'`, `ps2`] mp_tac do_swap_spilled_unchanged >>
  qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`] mp_tac
    do_swap_spilled_unchanged >> simp[]
QED

Theorem reorder_plan_pending_not_spilled:
  !dfg pending ps y.
    MEM y pending /\ y NOTIN FDOM ps.ps_spilled ==>
    y NOTIN FDOM (SND (reorder_plan dfg pending ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[reorder_plan_def] >>
  `!xs acc. y NOTIN FDOM (SND acc).ps_spilled ==>
    y NOTIN FDOM (SND (FOLDL
      (\(ops,ps) (idx,op).
        let (step_ops,ps') = reorder_one dfg pending idx op ps in
        (ops ++ step_ops,ps')) acc xs)).ps_spilled` suffices_by
    (disch_then irule >> simp[]) >>
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `acc` >> PairCases_on `h` >> simp[LET_THM] >>
  pairarg_tac >> gvs[LET_THM] >> first_x_assum irule >> simp[] >>
  drule_all reorder_one_pending_not_spilled >>
  disch_then (qspecl_then [`dfg`, `h0`, `h1`] mp_tac) >> simp[]
QED

Theorem plan_steps_reorder_inventory_mono[local]:
  !items dfg pending ps ops qs base.
    EVERY (\(idx,op). idx < LENGTH pending) items /\
    residual_budget_wf base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
      items ps = (ops,qs) ==>
    residual_budget_wf base pending qs /\
    LENGTH pending <= LENGTH qs.ps_stack /\
    (!x. LIST_ELEM_COUNT x ps.ps_stack +
       (if x IN FDOM ps.ps_spilled then 1 else 0) <=
       LIST_ELEM_COUNT x qs.ps_stack +
       (if x IN FDOM qs.ps_spilled then 1 else 0))
Proof
  Induct >- simp[plan_steps_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >> gvs[] >>
  drule plan_steps_cons_result >> strip_tac >> gvs[] >>
  drule_all reorder_one_residual_budget_wf >> strip_tac >>
  drule_all reorder_one_inventory_mono >> strip_tac >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspecl_then [`dfg`, `rest_ops`, `qs`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem reorder_plan_inventory_mono:
  !dfg pending ps ops qs base.
    residual_budget_wf base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\ LENGTH pending <= 16 /\
    reorder_plan dfg pending ps = (ops,qs) ==>
    residual_budget_wf base pending qs /\
    LENGTH pending <= LENGTH qs.ps_stack /\
    (!x. LIST_ELEM_COUNT x ps.ps_stack +
       (if x IN FDOM ps.ps_spilled then 1 else 0) <=
       LIST_ELEM_COUNT x qs.ps_stack +
       (if x IN FDOM qs.ps_spilled then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >> irule plan_steps_reorder_inventory_mono >>
  simp[] >> qexistsl_tac [`dfg`, `MAPi (\i op. (i,op)) pending`, `ops`] >>
  simp[GSYM reorder_plan_eq_plan_steps, EVERY_EL,
       indexedListsTheory.EL_MAPi, indexedListsTheory.LENGTH_MAPi]
QED

(* Generic materialisation-to-height boundary, shared by frame and lineage proofs. *)
Theorem list_elem_count_dom_length:
  !xs ys. (!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x ys) ==>
    LENGTH xs <= LENGTH ys
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `MEM h ys` by
    (first_x_assum (qspec_then `h` mp_tac) >>
     Cases_on `MEM h ys` >> simp[LIST_ELEM_COUNT_THM] >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  qpat_x_assum `MEM h ys` mp_tac >>
  rewrite_tac[listTheory.MEM_SPLIT] >> strip_tac >> gvs[] >>
  `!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x (l1 ++ l2)` by
    (gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND] >>
     Cases_on `h = x` >> simp[] >> decide_tac) >>
  first_x_assum drule >> simp[]
QED

Theorem available_input_plan_length:
  !opc inputs nl ps input_ops ps1.
    emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
    LENGTH inputs <= LENGTH ps1.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  irule list_elem_count_dom_length >>
  drule_all emit_input_plan_materialised >> simp[]
QED

Theorem generate_emit_ops_slots:
  !inst ltc ps ops ps'.
    generate_emit_ops inst ltc ps = (ops, ps') ==>
    ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = JNZ` >> gvs[]
  >- (BasicProvers.every_case_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = JMP` >> gvs[]
  >- (BasicProvers.every_case_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = DJMP` >> gvs[] >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[]
  >- (Cases_on `HD inst.inst_operands` >> gvs[] >>
      pairarg_tac >> gvs[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = RET` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSERT` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE` >> gvs[]
  >- (pairarg_tac >> gvs[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = LOG` >> gvs[] >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >>
  Cases_on `inst.inst_opcode = INITIAL_FMP` >> gvs[] >>
  Cases_on `inst.inst_opcode = BUMP` >> gvs[]
QED

Theorem reduce_depth_plan_length_upper:
  !fuel pending op f n ps ops qs.
    reduce_depth_plan fuel pending op f n ps = (ops,qs) ==>
    LENGTH qs.ps_stack <= LENGTH ps.ps_stack
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >> rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `x <= 16` >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x n` >> simp[] >>
  pairarg_tac >> simp[] >>
  rename1 `do_spill_at cand ps = (spill_ops,ps1)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_unfixed_depth_bound] >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `cand < LENGTH ps.ps_stack` by metis_tac[select_spill_candidate_bound] >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack - 1` by
    (qspecl_then [`cand`, `ps`] mp_tac do_spill_at_stack_length >> simp[] >> gvs[]) >>
  first_x_assum drule >> simp[]
QED

Theorem do_swap_length_envelope:
  !d ps. LENGTH (SND (do_swap d ps)).ps_stack <=
    MAX (d + 1) (LENGTH ps.ps_stack)
Proof
  rpt gen_tac >> Cases_on `d = 0` >- simp[do_swap_def] >>
  Cases_on `d <= 16` >- simp[do_swap_def] >>
  simp[do_swap_def, LET_THM] >> rpt (pairarg_tac >> simp[]) >>
  simp[MAX_DEF] >> decide_tac
QED

Theorem reorder_one_length_envelope:
  !dfg targets idx op ps ops qs.
    idx < LENGTH targets /\ MEM op targets /\
    (!x. MEM x targets ==> x NOTIN FDOM ps.ps_spilled) /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    LENGTH qs.ps_stack <= MAX (LENGTH targets) (LENGTH ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP ps.ps_spilled op = NONE` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps.ps_stack` >- simp[] >> simp[] >>
  pairarg_tac >> simp[] >> rename1 `_ = (reduce_ops,ps2)` >>
  `LENGTH ps2.ps_stack <= LENGTH ps.ps_stack` by
    (Cases_on `x > 16` >> gvs[] >>
     drule reduce_depth_plan_length_upper >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[MAX_DEF]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist` >>
  `dist < LENGTH ps2.ps_stack` by metis_tac[stack_get_unfixed_depth_bound] >>
  Cases_on `dist = LENGTH targets - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[MAX_DEF]) >>
  IF_CASES_TAC >> simp[]
  >- (IF_CASES_TAC >> simp[stack_poke_def]
      >- (strip_tac >> gvs[MAX_DEF]) >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      qspecl_then [`dist`, `ps2`] mp_tac do_swap_length >> simp[] >>
      qspecl_then [`LENGTH targets - (idx + 1)`, `ps3`] mp_tac do_swap_length >>
      simp[] >> decide_tac) >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qspecl_then [`dist`, `ps2`] mp_tac do_swap_length >> simp[] >> strip_tac >>
  qspecl_then [`LENGTH targets - (idx + 1)`, `ps3`] mp_tac do_swap_length_envelope >>
  simp[] >> simp[MAX_DEF] >> decide_tac
QED

Theorem reorder_fold_length_bound[local]:
  !items dfg targets acc ps ops qs bound.
    EVERY (\(idx,op). idx < LENGTH targets /\ MEM op targets) items /\
    (!x. MEM x targets ==> x NOTIN FDOM ps.ps_spilled) /\
    LENGTH targets <= bound /\ LENGTH ps.ps_stack <= bound /\
    FOLDL (\(ops,ps) (idx,op).
      (\(step_ops,ps'). (ops ++ step_ops,ps'))
        (reorder_one dfg targets idx op ps)) (acc,ps) items = (ops,qs) ==>
    LENGTH qs.ps_stack <= bound
Proof
  Induct >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> simp[] >> strip_tac >> PairCases_on `h` >> gvs[] >>
  Cases_on `reorder_one dfg targets h0 h1 ps` >> gvs[] >>
  `LENGTH r.ps_stack <= MAX (LENGTH targets) (LENGTH ps.ps_stack)` by
    (drule_all reorder_one_length_envelope >> simp[]) >>
  `!x. MEM x targets ==> x NOTIN FDOM r.ps_spilled` by
    (gen_tac >> disch_tac >>
     `x NOTIN FDOM ps.ps_spilled` by simp[] >>
     drule_all reorder_one_pending_not_spilled >>
     disch_then (qspecl_then [`dfg`, `h0`, `h1`] mp_tac) >> simp[]) >>
  first_x_assum irule >>
  qexistsl [`acc ++ q`, `dfg`, `ops`, `r`, `targets`] >>
  simp[] >> gvs[MAX_DEF]
QED

Theorem reorder_plan_length_envelope:
  !dfg targets ps ops qs.
    (!x. MEM x targets ==> x NOTIN FDOM ps.ps_spilled) /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    LENGTH qs.ps_stack <= MAX (LENGTH targets) (LENGTH ps.ps_stack)
Proof
  rpt gen_tac >> pure_rewrite_tac[reorder_plan_def, LET_THM] >> strip_tac >>
  irule reorder_fold_length_bound >>
  qexistsl [`[]`, `dfg`, `MAPi (\i op. (i,op)) targets`, `ops`, `ps`, `targets`] >>
  simp[listTheory.EVERY_EL, indexedListsTheory.LENGTH_MAPi,
       indexedListsTheory.EL_MAPi, listTheory.EL_MEM]
QED

Theorem reorder_plan_short_residual_empty:
  !dfg targets ps ops qs.
    (!x. MEM x targets ==> x NOTIN FDOM ps.ps_spilled) /\
    LENGTH ps.ps_stack <= LENGTH targets /\
    reorder_plan dfg targets ps = (ops,qs) /\
    stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
    stack_pop (LENGTH targets) qs.ps_stack = []
Proof
  rpt strip_tac >>
  drule_all reorder_plan_length_envelope >>
  `MAX (LENGTH targets) (LENGTH ps.ps_stack) = LENGTH targets` by
    simp[MAX_DEF] >>
  strip_tac >>
  `LENGTH (stack_pop (LENGTH targets) qs.ps_stack) + LENGTH targets =
   LENGTH qs.ps_stack` by metis_tac[listTheory.LENGTH_APPEND] >>
  gvs[MAX_DEF] >>
  `LENGTH (stack_pop (LENGTH targets) qs.ps_stack) = 0` by decide_tac >>
  gvs[]
QED

Theorem reorder_plan_short_reached_targets:
  !dfg targets ps ops qs.
    (!x. MEM x targets ==> x NOTIN FDOM ps.ps_spilled) /\
    LENGTH ps.ps_stack <= LENGTH targets /\
    reorder_plan dfg targets ps = (ops,qs) /\
    stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack ==>
    qs.ps_stack = targets
Proof
  rpt strip_tac >> drule_all reorder_plan_short_residual_empty >>
  strip_tac >> gvs[]
QED
