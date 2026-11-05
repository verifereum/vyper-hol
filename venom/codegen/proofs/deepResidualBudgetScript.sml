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
 *   emit_input_plan_residual_budget_wf_marked
 *                                           - input emission keeps the budget
 *   reorder_plan_residual_budget_wf_marked  - reordering keeps the budget,
 *                                             the inventory and the length
 *                                             floor, with no bound on the
 *                                             number of targets
 *)

Theory deepResidualBudget
Ancestors
  fnPlanPrefix preparedPrefixSim generatedPrefixSim generatedReorderSim
  genericInputReady reorderSim doSwapSim codegenRel asmSem planExec
  stackPlanGen stackPlanOps stackPlanTypes stackModel blockSimHelpers planWf planSpillBounds foldlSim
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

(* ===== Reorder steps over the marked budget =====
   reorder_one reads LENGTH target_ops, so padding the pending list with
   markers would change the plan; these follow reorderSim's unmarked proofs
   directly, without its LENGTH pending <= 16 bound. *)

Theorem elem_count_sing[local]:
  !x (y : 'a). LIST_ELEM_COUNT x [y] = if x = y then 1 else 0
Proof
  rw[LIST_ELEM_COUNT_DEF] >> gvs[]
QED

Theorem select_spill_candidate_props:
  !stk forbidden dist target_len cand.
    select_spill_candidate stk forbidden dist target_len = SOME cand ==>
    target_len <= cand /\ ~MEM (stack_peek cand stk) forbidden /\
    is_var_operand (stack_peek cand stk)
Proof
  rpt gen_tac >> simp[select_spill_candidate_def, LET_THM] >>
  strip_tac >> imp_res_tac FIND_SOME_MEM >> gvs[]
QED

Theorem do_spill_at_length[local]:
  !d ps.
    d < LENGTH ps.ps_stack ==>
    LENGTH (SND (do_spill_at d ps)).ps_stack = LENGTH ps.ps_stack - 1
Proof
  rpt gen_tac >> strip_tac >>
  simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `d = 0` >> simp[stack_pop_def] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[stack_pop_def]
QED

Theorem do_spill_at_spilled_update:
  !d ps ops ps'.
    d < LENGTH ps.ps_stack /\ do_spill_at d ps = (ops, ps') ==>
    ?off. ps'.ps_spilled = ps.ps_spilled |+ (stack_peek d ps.ps_stack, off)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `d = 0`
  >- (gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
      Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >> metis_tac[]) >>
  `stack_peek 0 (stack_swap d ps.ps_stack) = stack_peek d ps.ps_stack` by
    (simp[stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE] >>
     IF_CASES_TAC >> gvs[] >> decide_tac) >>
  gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >> metis_tac[]
QED

(* select_spill_candidate only picks offsets at or above target_len, so a
   depth reduction never cuts the stack below target_len. *)
Theorem reduce_depth_plan_target_len_floor:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') /\
    target_len <= LENGTH ps.ps_stack ==>
    target_len <= LENGTH ps'.ps_stack
Proof
  Induct >- simp[reduce_depth_plan_def] >>
  rpt gen_tac >> simp[Once reduce_depth_plan_def, LET_THM] >>
  Cases_on `f + 1 < target_len` >> simp[] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `x <= 16` >> simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >> TRY (strip_tac >> gvs[] >> NO_TAC) >>
  pairarg_tac >> simp[] >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `cand < LENGTH ps.ps_stack` by metis_tac[select_spill_candidate_bound] >>
  drule select_spill_candidate_props >> strip_tac >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack - 1` by
    (qspecl_then [`cand`, `ps`] mp_tac do_spill_at_length >> simp[]) >>
  `target_len <= LENGTH ps1.ps_stack` by decide_tac >>
  metis_tac[]
QED

Theorem residual_budget_wf_marked_do_swap:
  !base pending dist ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  fs[residual_budget_wf_marked_def] >>
  imp_res_tac do_swap_slots_bounded >>
  imp_res_tac do_swap_multiplicity_layout >> gvs[]
QED

Theorem residual_budget_wf_marked_stack_poke_exchange:
  !base pending ps d1 d2.
    residual_budget_wf_marked base pending ps /\
    d1 < LENGTH ps.ps_stack /\ d2 < LENGTH ps.ps_stack ==>
    residual_budget_wf_marked base pending
      (ps with ps_stack :=
        stack_poke d2 (stack_peek d1 ps.ps_stack)
          (stack_poke d1 (stack_peek d2 ps.ps_stack) ps.ps_stack))
Proof
  rpt strip_tac >>
  fs[residual_budget_wf_marked_def, stack_poke_exchange_multiplicity]
QED

Theorem residual_budget_wf_marked_restore:
  !base pending op ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    do_restore op ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `residual_budget_wf_marked sb pending ps` >>
  `plan_slots_bounded sb ps'` by
    metis_tac[do_restore_slots_bounded, residual_budget_wf_marked_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- gvs[do_restore_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `op IN FDOM ps.ps_spilled` by fs[finite_mapTheory.flookup_thm] >>
  fs[residual_budget_wf_marked_def] >>
  `op <> dead_stack_marker` by (strip_tac >> gvs[]) >>
  gvs[do_restore_def, stack_push_def, SNOC_APPEND, LIST_ELEM_COUNT_THM,
      elem_count_sing, finite_mapTheory.FDOM_DOMSUB] >>
  rpt conj_tac
  >- metis_tac[spill_alloc_layout_wf_after_free]
  >- (rpt strip_tac >> rw[] >> res_tac >> decide_tac)
  >> rpt strip_tac >> rw[] >> res_tac >> decide_tac
QED

Theorem residual_budget_wf_marked_do_spill_at:
  !base pending d ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    ~MEM (stack_peek d ps.ps_stack) pending /\
    stack_peek d ps.ps_stack <> dead_stack_marker /\
    do_spill_at d ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `v = stack_peek d ps.ps_stack` >>
  `!x. LIST_ELEM_COUNT x ps'.ps_stack + LIST_ELEM_COUNT x [v] =
       LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[do_spill_at_stack_count] >>
  `?off. ps'.ps_spilled = ps.ps_spilled |+ (v, off)` by
    metis_tac[do_spill_at_spilled_update] >>
  `LIST_ELEM_COUNT v pending = 0` by fs[GSYM LIST_ELEM_COUNT_MEM] >>
  rename1 `residual_budget_wf_marked sb pending ps` >>
  fs[residual_budget_wf_marked_def] >>
  `plan_slots_bounded sb ps'` by metis_tac[do_spill_at_slots_bounded] >>
  `spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled` by
    metis_tac[do_spill_at_layout_wf] >>
  `dead_stack_marker <> v` by metis_tac[] >>
  `!x. LIST_ELEM_COUNT x ps'.ps_stack <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> qpat_assum `!x. _ + _ = _` (qspec_then `x` mp_tac) >>
     decide_tac) >>
  `LIST_ELEM_COUNT v ps'.ps_stack + 1 = LIST_ELEM_COUNT v ps.ps_stack` by
    (`LIST_ELEM_COUNT v [v] = 1` by simp[elem_count_sing] >>
     qpat_assum `!x. _ + _ = _` (qspec_then `v` mp_tac) >>
     decide_tac) >>
  `LIST_ELEM_COUNT v ps.ps_stack <= 1` by
    (`LIST_ELEM_COUNT v ps.ps_stack <= SUC (LIST_ELEM_COUNT v pending)` by
       metis_tac[] >> decide_tac) >>
  gvs[finite_mapTheory.FDOM_FUPDATE] >> rpt strip_tac
  >- (res_tac >>
      qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack <= _`
        (qspec_then `op` assume_tac) >> decide_tac)
  >- simp[]
  >> res_tac >>
     qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack <= _`
       (qspec_then `op` assume_tac) >> decide_tac
QED

Theorem select_spill_candidate_not_spilled_marked:
  !base pending ps dist target_len d.
    residual_budget_wf_marked base pending ps /\
    1 <= LENGTH ps.ps_stack /\
    select_spill_candidate ps.ps_stack pending dist target_len = SOME d ==>
    stack_peek d ps.ps_stack NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all select_spill_candidate_bound >> strip_tac >>
  drule select_spill_candidate_props >> strip_tac >>
  strip_tac >> fs[residual_budget_wf_marked_def] >>
  qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
    (qspec_then `stack_peek d ps.ps_stack` (drule_then assume_tac)) >>
  `MEM (stack_peek d ps.ps_stack) ps.ps_stack` by
    (rewrite_tac[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
  fs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem do_spill_at_inventory_count_marked[local]:
  !d ps ops ps'.
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    stack_peek d ps.ps_stack NOTIN FDOM ps.ps_spilled /\
    do_spill_at d ps = (ops, ps') ==>
    !x.
      LIST_ELEM_COUNT x ps'.ps_stack +
        (if x IN FDOM ps'.ps_spilled then 1 else 0) =
      LIST_ELEM_COUNT x ps.ps_stack +
        (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >>
  `LIST_ELEM_COUNT x ps'.ps_stack +
     LIST_ELEM_COUNT x [stack_peek d ps.ps_stack] =
   LIST_ELEM_COUNT x ps.ps_stack` by metis_tac[do_spill_at_stack_count] >>
  drule_all do_spill_at_spilled_update >> strip_tac >>
  Cases_on `x = stack_peek d ps.ps_stack` >>
  gvs[finite_mapTheory.FDOM_FUPDATE, elem_count_sing]
QED

Theorem reduce_depth_plan_residual_budget_wf_marked:
  !fuel base pending target_op f ps ops ps'.
    residual_budget_wf_marked base pending ps /\
    reduce_depth_plan fuel pending target_op f (LENGTH pending) ps =
      (ops, ps') ==>
    residual_budget_wf_marked base pending ps'
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f (LENGTH pending)
              ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < LENGTH pending` >> gvs[] >>
  Cases_on `x <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x
              (LENGTH pending)` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  drule select_spill_candidate_props >> strip_tac >>
  `stack_peek cand ps.ps_stack <> dead_stack_marker` by
    metis_tac[var_operand_not_marker] >>
  `residual_budget_wf_marked base' pending ps1` by
    metis_tac[residual_budget_wf_marked_do_spill_at] >>
  Cases_on `reduce_depth_plan fuel pending target_op f (LENGTH pending) ps1` >>
  gvs[] >> metis_tac[]
QED

Theorem reduce_depth_plan_pending_inventory_mono_marked:
  !fuel pending target_op f ps ops ps' base x.
    residual_budget_wf_marked base pending ps /\
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
  drule select_spill_candidate_props >> strip_tac >>
  `stack_peek cand ps.ps_stack <> dead_stack_marker` by
    metis_tac[var_operand_not_marker] >>
  `stack_peek cand ps.ps_stack NOTIN FDOM ps.ps_spilled` by
    metis_tac[select_spill_candidate_not_spilled_marked] >>
  `!y. LIST_ELEM_COUNT y ps1.ps_stack +
       (if y IN FDOM ps1.ps_spilled then 1 else 0) =
       LIST_ELEM_COUNT y ps.ps_stack +
       (if y IN FDOM ps.ps_spilled then 1 else 0)` by
    (qspecl_then [`cand`, `ps`, `spill_ops`, `ps1`] mp_tac
       do_spill_at_inventory_count_marked >> simp[]) >>
  `residual_budget_wf_marked base' pending ps1` by
    metis_tac[residual_budget_wf_marked_do_spill_at] >>
  Cases_on `reduce_depth_plan fuel pending target_op f
              (LENGTH pending) ps1` >> gvs[] >>
  first_x_assum
    (qspecl_then [`pending`, `target_op`, `f`, `ps1`, `q`, `ps'`,
                  `base'`, `x`] mp_tac) >>
  simp[] >>
  qpat_assum `!y. _` (qspec_then `x` assume_tac) >>
  decide_tac
QED

Theorem reorder_restore_residual_budget_wf_marked:
  !base pending op f ps.
    residual_budget_wf_marked base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack ==>
    let (_,ps') =
      case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
        SOME _ => ([] : stack_op list, ps)
      | NONE =>
          (case FLOOKUP ps.ps_spilled op of
             SOME _ => do_restore op ps
           | NONE => ([], ps))
    in residual_budget_wf_marked base pending ps' /\
       LENGTH pending <= LENGTH ps'.ps_stack
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >>
  simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  Cases_on `do_restore op ps` >> gvs[] >>
  conj_tac
  >- (qspecl_then [`base'`, `pending`, `op`, `ps`, `q`, `r`] mp_tac
        residual_budget_wf_marked_restore >> simp[])
  >> qspecl_then [`op`, `ps`] mp_tac do_restore_length >> simp[]
QED

Theorem do_restore_inventory_count_marked[local]:
  !(ps : plan_state) op off x.
    FLOOKUP ps.ps_spilled op = SOME off ==>
    LIST_ELEM_COUNT x (SND (do_restore op ps)).ps_stack +
      (if x IN FDOM (SND (do_restore op ps)).ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >>
  simp[do_restore_def, stack_push_def, SNOC_APPEND, LIST_ELEM_COUNT_THM,
       elem_count_sing, finite_mapTheory.FDOM_DOMSUB] >>
  Cases_on `x = op` >> gvs[finite_mapTheory.flookup_thm]
QED

Theorem reorder_restore_inventory_mono_marked[local]:
  !op f target_len (ps : plan_state) x.
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x
      (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
              SOME _ => ([] : stack_op list, ps)
            | NONE =>
                (case FLOOKUP ps.ps_spilled op of
                   SOME _ => do_restore op ps
                 | NONE => ([], ps)))).ps_stack +
      (if x IN FDOM
        (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
                SOME _ => ([] : stack_op list, ps)
              | NONE =>
                  (case FLOOKUP ps.ps_spilled op of
                     SOME _ => do_restore op ps
                   | NONE => ([], ps)))).ps_spilled then 1 else 0)
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f target_len ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  qspecl_then [`ps`, `op`, `off`, `x`] mp_tac do_restore_inventory_count_marked >>
  simp[]
QED

Theorem reorder_one_residual_budget_wf_marked:
  !dfg pending idx op ps ops ps' base.
    residual_budget_wf_marked base pending ps /\
    idx < LENGTH pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_one dfg pending idx op ps = (ops, ps') ==>
    residual_budget_wf_marked base pending ps' /\
    LENGTH pending <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (qspecl_then [`base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps`]
       mp_tac reorder_restore_residual_budget_wf_marked >> simp[] >> gvs[]) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps2` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps1`, `reduce_ops`, `ps2`]
       mp_tac reduce_depth_plan_residual_budget_wf_marked >> simp[]) >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `LENGTH pending`, `ps1`,
       `reduce_ops`, `ps2`] mp_tac reduce_depth_plan_target_len_floor >>
     fs[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `stack_peek dist' ps2.ps_stack = op`
    (fn th => SUBST_ALL_TAC (SYM th)) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist' ps2.ps_stack)
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >> conj_tac
      >- (irule residual_budget_wf_marked_stack_poke_exchange >> simp[])
      >> simp[stack_poke_def]) >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops, ps3)` >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 =
           (swap2_ops, ps4)` >>
  `residual_budget_wf_marked base' pending ps3` by
    metis_tac[residual_budget_wf_marked_do_swap] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `residual_budget_wf_marked base' pending ps4` by
    (qspecl_then [`base'`, `pending`,
       `LENGTH pending - (idx + 1)`, `ps3`, `swap2_ops`, `ps4`]
       mp_tac residual_budget_wf_marked_do_swap >> simp[]) >>
  `LENGTH ps4.ps_stack = LENGTH ps3.ps_stack` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`]
       mp_tac do_swap_length >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem reorder_one_pending_inventory_wf_marked:
  !dfg pending idx op ps ops ps' base.
    pending_inventory_wf pending ps /\
    residual_budget_wf_marked base pending ps /\ idx < LENGTH pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_one dfg pending idx op ps = (ops,ps') ==>
    pending_inventory_wf pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (qspecl_then [`base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps`]
       mp_tac reorder_restore_residual_budget_wf_marked >> simp[] >> gvs[]) >>
  `!x. MEM x pending ==>
      LIST_ELEM_COUNT x ps.ps_stack +
        (if x IN FDOM ps.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x ps1.ps_stack +
        (if x IN FDOM ps1.ps_spilled then 1 else 0)` by
    (gen_tac >> strip_tac >>
     qspecl_then [`op`, `LENGTH pending - (idx + 1)`,
       `LENGTH pending`, `ps`, `x`]
       mp_tac reorder_restore_inventory_mono_marked >> gvs[]) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> rewrite_tac[pending_inventory_wf_def] >>
      gen_tac >> Cases_on `MEM op' pending`
      >- (qpat_assum `!x. MEM x pending ==> _`
            (qspec_then `op'` (drule_then assume_tac)) >>
          qpat_assum `pending_inventory_wf pending ps`
            (assume_tac o Q.SPEC `op'` o
             REWRITE_RULE [pending_inventory_wf_def]) >>
          irule LESS_EQ_TRANS >>
          qexists_tac `LIST_ELEM_COUNT op' ps.ps_stack +
            (if op' IN FDOM ps.ps_spilled then 1 else 0)` >> simp[])
      >> fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf_marked base' pending ps2` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps1`, `reduce_ops`, `ps2`]
       mp_tac reduce_depth_plan_residual_budget_wf_marked >> simp[]) >>
  `!y. MEM y pending ==>
      LIST_ELEM_COUNT y ps1.ps_stack +
        (if y IN FDOM ps1.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT y ps2.ps_stack +
        (if y IN FDOM ps2.ps_spilled then 1 else 0)` by
    (gen_tac >> strip_tac >> Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps1`, `reduce_ops`, `ps2`,
       `base'`, `y`] mp_tac reduce_depth_plan_pending_inventory_mono_marked >>
     simp[]) >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `LENGTH pending`, `ps1`,
       `reduce_ops`, `ps2`] mp_tac reduce_depth_plan_target_len_floor >>
     fs[]) >>
  `pending_inventory_wf pending ps2` by
    (rewrite_tac[pending_inventory_wf_def] >> gen_tac >>
     Cases_on `MEM op' pending`
     >- (qpat_assum `!y. MEM y pending ==> _`
           (qspec_then `op'` (drule_then assume_tac)) >>
         qpat_assum `!x. MEM x pending ==> _`
           (qspec_then `op'` (drule_then assume_tac)) >>
         qpat_assum `pending_inventory_wf pending ps`
           (assume_tac o Q.SPEC `op'` o
            REWRITE_RULE [pending_inventory_wf_def]) >>
         irule LESS_EQ_TRANS >>
         qexists_tac `LIST_ELEM_COUNT op' ps1.ps_stack +
           (if op' IN FDOM ps1.ps_spilled then 1 else 0)` >>
         conj_tac
         >- (irule LESS_EQ_TRANS >>
             qexists_tac `LIST_ELEM_COUNT op' ps.ps_stack +
               (if op' IN FDOM ps.ps_spilled then 1 else 0)` >> simp[])
         >> simp[])
     >> fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `stack_peek dist' ps2.ps_stack = op`
    (fn th => SUBST_ALL_TAC (SYM th)) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> decide_tac) >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist' ps2.ps_stack)
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[pending_inventory_wf_def] >> gen_tac >>
      qpat_assum `!op. LIST_ELEM_COUNT op pending <= _`
        (qspec_then `op'` assume_tac) >>
      simp[stack_poke_exchange_multiplicity]) >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 = (swap2_ops,ps4)` >>
  `ps3.ps_spilled = ps2.ps_spilled /\
   (!y. LIST_ELEM_COUNT y ps3.ps_stack = LIST_ELEM_COUNT y ps2.ps_stack)` by
    (qspecl_then [`dist'`, `ps2`, `swap1_ops`, `ps3`] mp_tac
       do_swap_multiplicity_layout >> fs[residual_budget_wf_marked_def]) >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `ps4.ps_spilled = ps3.ps_spilled /\
   (!y. LIST_ELEM_COUNT y ps4.ps_stack = LIST_ELEM_COUNT y ps3.ps_stack)` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`,
       `swap2_ops`, `ps4`] mp_tac do_swap_multiplicity_layout >>
     `spill_alloc_layout_wf ps3.ps_alloc ps3.ps_spilled` by
       (qspecl_then [`base'`, `pending`, `dist'`, `ps2`,
          `swap1_ops`, `ps3`] mp_tac residual_budget_wf_marked_do_swap >>
        impl_tac >- simp[] >>
        disch_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
          REWRITE_RULE [residual_budget_wf_marked_def])) >>
     simp[]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `pending_inventory_wf pending ps2` mp_tac >>
  simp[pending_inventory_wf_def]
QED

Theorem plan_steps_reorder_residual_budget_wf_marked:
  !items ps ops ps'.
    EVERY (\(idx,op). idx < LENGTH pending) items /\
    residual_budget_wf_marked sb pending ps /\
    pending_inventory_wf pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps =
      (ops,ps') ==>
    residual_budget_wf_marked sb pending ps' /\
    pending_inventory_wf pending ps' /\
    LENGTH pending <= LENGTH ps'.ps_stack
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[plan_steps_def]) >>
  rpt gen_tac >> Cases_on `h` >> rename1 `(idx,op)::items` >> strip_tac >>
  qpat_x_assum `plan_steps _ (_::_) _ = _` mp_tac >>
  simp[Once plan_steps_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `reorder_one dfg pending idx op ps = (step_ops,ps1)` >>
  `residual_budget_wf_marked sb pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_one_residual_budget_wf_marked] >>
  `pending_inventory_wf pending ps1` by
    metis_tac[reorder_one_pending_inventory_wf_marked] >>
  first_x_assum drule_all >> simp[]
QED

(* The budget half of deepResidualSim's reorder_plan_venom_asm_rel_numeric_marked,
   with the stack-length floor it needs. *)
Theorem reorder_plan_residual_budget_wf_marked:
  !dfg target_ops ps ops ps' base.
    residual_budget_wf_marked base target_ops ps /\
    pending_inventory_wf target_ops ps /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    reorder_plan dfg target_ops ps = (ops,ps') ==>
    residual_budget_wf_marked base target_ops ps' /\
    pending_inventory_wf target_ops ps' /\
    LENGTH target_ops <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH target_ops)
     (MAPi (\i op. (i,op)) target_ops)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorder_plan_eq_plan_steps]) >>
  drule_all plan_steps_reorder_residual_budget_wf_marked >> simp[]
QED
