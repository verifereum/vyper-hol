(*
 * The marker-tolerant residual budgets behind deepResidualSim, and the
 * planner steps of input emission and reorder that preserve them.
 *
 * residual_budget_wf_marked and plan_state_residual_wf_marked are
 * reorderSim's residual_budget_wf and plan_state_residual_wf with the
 * per-operand stack count exempting dead_stack_marker, which a cleanup
 * elision leaves in several slots, and the marker kept out of the spill map.
 *
 * TOP-LEVEL:
 *   residual_budget_wf_marked, plan_state_residual_wf_marked
 *                                           - the marker-tolerant budgets
 *)

Theory deepResidualBudget
Ancestors
  fnPlanPrefix preparedPrefixSim generatedPrefixSim generatedReorderSim
  genericInputReady reorderSim doSwapSim codegenRel asmSem planExec
  stackPlanGen stackPlanOps stackPlanTypes stackModel blockSimHelpers
  list rich_list arithmetic
Libs BasicProvers

Definition residual_budget_wf_marked_def:
  residual_budget_wf_marked base pending (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End

Definition plan_state_residual_wf_marked_def:
  plan_state_residual_wf_marked base pending fixed (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    fixed <= LENGTH pending /\
    (!i. i < fixed ==>
       stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End


Theorem var_operand_not_marker:
  !op. is_var_operand op ==> op <> dead_stack_marker
Proof
  Cases >> simp[is_var_operand_def, dead_stack_marker_def]
QED

Theorem elem_count_replicate:
  !k (x : 'a) y.
    LIST_ELEM_COUNT x (REPLICATE k y) = if x = y then k else 0
Proof
  Induct >> rpt gen_tac
  >- simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `x = y`
  >- gvs[LIST_ELEM_COUNT_THM] >>
  `y <> x` by simp[] >> simp[LIST_ELEM_COUNT_THM]
QED

(* The marked budget is the unmarked one with the stack's markers added to
   the pending list. *)
Theorem residual_budget_wf_marked_pad:
  !base pending ps.
    residual_budget_wf_marked base pending ps ==>
    residual_budget_wf base
      (pending ++ REPLICATE (LIST_ELEM_COUNT dead_stack_marker ps.ps_stack)
                    dead_stack_marker) ps
Proof
  rw[residual_budget_wf_marked_def, residual_budget_wf_def,
     LIST_ELEM_COUNT_THM, elem_count_replicate]
  >- (Cases_on `op = dead_stack_marker` >> simp[]) >>
  `op <> dead_stack_marker` by (strip_tac >> gvs[]) >>
  simp[]
QED

Theorem residual_budget_wf_unpad:
  !base pending pending' ps.
    residual_budget_wf base pending' ps /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op pending' = LIST_ELEM_COUNT op pending) /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled ==>
    residual_budget_wf_marked base pending ps
Proof
  rw[residual_budget_wf_marked_def, residual_budget_wf_def] >>
  `op <> dead_stack_marker` by (strip_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem residual_budget_wf_marked_perm:
  !xs ys base ps. PERM xs ys ==>
    (residual_budget_wf_marked base xs ps <=>
     residual_budget_wf_marked base ys ps)
Proof
  rpt strip_tac >> drule perm_operand_counts >>
  simp[residual_budget_wf_marked_def]
QED

Theorem do_dup_spilled_eq:
  !dist ps ops ps'.
    do_dup dist ps = (ops, ps') ==> ps'.ps_spilled = ps.ps_spilled
Proof
  rw[do_dup_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem emit_one_input_not_spilled:
  !opc nl op ps ops ps' x.
    emit_one_input opc nl op ps = (ops, ps') /\
    x NOTIN FDOM ps.ps_spilled ==>
    x NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[emit_one_input_def, is_var_operand_def, do_restore_def, LET_THM] >>
  rpt (FULL_CASE_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_dup_spilled_eq >> gvs[finite_mapTheory.FDOM_DOMSUB]
QED

Theorem emit_input_plan_not_spilled:
  !operands opc nl ps ops ps' x.
    emit_input_plan opc operands nl ps = (ops, ps') /\
    x NOTIN FDOM ps.ps_spilled ==>
    x NOTIN FDOM ps'.ps_spilled
Proof
  Induct >> simp[emit_input_plan_cons] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all emit_one_input_not_spilled >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem emit_one_input_residual_budget_wf_marked:
  !base pending opc nl op ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    emit_one_input opc nl op ps = (ops, ps') ==>
    residual_budget_wf_marked base (pending ++ [op]) ps'
Proof
  rpt strip_tac >>
  drule residual_budget_wf_marked_pad >> strip_tac >>
  drule_all emit_one_input_residual_budget_wf >> strip_tac >>
  qpat_x_assum `residual_budget_wf_marked _ _ _`
    (strip_assume_tac o REWRITE_RULE [residual_budget_wf_marked_def]) >>
  drule_all emit_one_input_not_spilled >> strip_tac >>
  qspecl_then [`base'`, `pending ++ [op]`,
    `(pending ++ REPLICATE (LIST_ELEM_COUNT dead_stack_marker
        ps.ps_stack) dead_stack_marker) ++ [op]`, `ps'`]
    irule residual_budget_wf_unpad >>
  simp[LIST_ELEM_COUNT_THM, elem_count_replicate] >>
  qexists_tac `ps` >> fs[]
QED

Theorem emit_input_plan_residual_budget_wf_marked:
  !operands base pending opc nl ps iops ps1.
    residual_budget_wf_marked base pending ps /\
    emit_input_plan opc operands nl ps = (iops,ps1) ==>
    residual_budget_wf_marked base (pending ++ operands) ps1
Proof
  rpt strip_tac >>
  drule residual_budget_wf_marked_pad >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> strip_tac >>
  qpat_x_assum `residual_budget_wf_marked _ _ _`
    (strip_assume_tac o REWRITE_RULE [residual_budget_wf_marked_def]) >>
  drule_all emit_input_plan_not_spilled >> strip_tac >>
  qspecl_then [`base'`, `pending ++ operands`,
    `(pending ++ REPLICATE (LIST_ELEM_COUNT dead_stack_marker
        ps.ps_stack) dead_stack_marker) ++ operands`, `ps1`]
    irule residual_budget_wf_unpad >>
  simp[LIST_ELEM_COUNT_THM, elem_count_replicate] >>
  qexists_tac `ps` >> fs[]
QED
