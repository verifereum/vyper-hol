Theory fnPlanLineageWide
Ancestors fnPlanLineageInventory fnPlanLineageSetup
Libs stackPlanOpsTheory stackModelTheory fnPlanLineageReorderTheory listTheory
     stackPlanGenTheory venomInstTheory asmIRTheory venomEffectsTheory

(* Materialisation shields arbitrary residual prefixes even for wide joins.
   The preservation lemmas here do not assume a short target window. *)
Theorem reorder_one_wide_counts:
  !dfg targets idx op ps ops qs d.
    idx < LENGTH targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
    MEM op targets /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    !x. MEM x targets ==>
      LIST_ELEM_COUNT x qs.ps_stack = LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> rename1 `_ = (reduce_ops,mid)` >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     drule reduce_depth_plan_target_length_floor >>
     simp[arithmeticTheory.MIN_DEF, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!x. MEM x targets ==>
    LIST_ELEM_COUNT x mid.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     metis_tac[reorderSimTheory.reduce_depth_plan_pending_stack_count_unconditional]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) mid.ps_stack`
  >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  `dist < LENGTH mid.ps_stack /\ stack_peek dist mid.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH targets - (idx + 1) < LENGTH mid.ps_stack` by decide_tac >>
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  qspecl_then [`dfg`, `op`, `dist`, `LENGTH targets - (idx + 1)`, `mid`, `x`]
    mp_tac reorderSimTheory.reorder_place_phase_multiplicity >> simp[] >>
  Cases_on `dist = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist mid.ps_stack)
    (stack_peek (LENGTH targets - (idx + 1)) mid.ps_stack)` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem do_swap_wide_peek_other:
  !d k ps. d < LENGTH ps.ps_stack /\ k < LENGTH ps.ps_stack /\
    k <> 0 /\ k <> d ==>
    stack_peek k (SND (do_swap d ps)).ps_stack = stack_peek k ps.ps_stack
Proof
  rpt strip_tac >> simp[doSwapSimTheory.do_swap_stack_result] >>
  Cases_on `d = 0` >>
  simp[stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE] >>
  `LENGTH ps.ps_stack - 1 - k <> PRE (LENGTH ps.ps_stack)` by decide_tac >>
  `LENGTH ps.ps_stack - 1 - k <> LENGTH ps.ps_stack - (d + 1)` by decide_tac >>
  simp[]
QED

Theorem do_swap_wide_peek_ends:
  !d ps. d < LENGTH ps.ps_stack ==>
    stack_peek d (SND (do_swap d ps)).ps_stack = stack_peek 0 ps.ps_stack /\
    stack_peek 0 (SND (do_swap d ps)).ps_stack = stack_peek d ps.ps_stack
Proof
  rpt strip_tac >> simp[doSwapSimTheory.do_swap_stack_result,
    stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE]
QED

Theorem reorder_place_wide_fixed:
  !dfg op dist final_dist k ps.
    dist < LENGTH ps.ps_stack /\ final_dist < LENGTH ps.ps_stack /\
    k < LENGTH ps.ps_stack /\ k <> 0 /\ k <> dist /\ k <> final_dist ==>
    stack_peek k
      (if dist = final_dist then ps
       else if operand_equiv dfg op (stack_peek final_dist ps.ps_stack) then
         ps with ps_stack := stack_poke final_dist op
           (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)
       else SND (do_swap final_dist (SND (do_swap dist ps)))).ps_stack =
    stack_peek k ps.ps_stack
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist = final_dist` >> simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek final_dist ps.ps_stack)` >> simp[]
  >- simp[stack_peek_def, stack_poke_def, EL_LUPDATE] >>
  Cases_on `do_swap dist ps` >> gvs[] >>
  rename1 `do_swap dist ps = (s1,ps1)` >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
    (qspecl_then [`dist`, `ps`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  Cases_on `do_swap final_dist ps1` >> gvs[] >>
  `stack_peek k ps1.ps_stack = stack_peek k ps.ps_stack` by
    metis_tac[do_swap_wide_peek_other, pairTheory.SND] >>
  metis_tac[do_swap_wide_peek_other, pairTheory.SND]
QED

Theorem reorder_place_wide_places:
  !dfg op dist final_dist ps.
    dist < LENGTH ps.ps_stack /\ final_dist < LENGTH ps.ps_stack /\
    stack_peek dist ps.ps_stack = op ==>
    stack_peek final_dist
      (if dist = final_dist then ps
       else if operand_equiv dfg op (stack_peek final_dist ps.ps_stack) then
         ps with ps_stack := stack_poke final_dist op
           (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)
       else SND (do_swap final_dist (SND (do_swap dist ps)))).ps_stack = op
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist = final_dist` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist ps.ps_stack)
    (stack_peek final_dist ps.ps_stack)` >> simp[]
  >- simp[stack_peek_def, stack_poke_def, EL_LUPDATE] >>
  Cases_on `do_swap dist ps` >> gvs[] >>
  rename1 `do_swap dist ps = (s1,ps1)` >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
    (qspecl_then [`dist`, `ps`] mp_tac planWfTheory.do_swap_length >> simp[]) >>
  Cases_on `do_swap final_dist ps1` >> gvs[] >>
  `stack_peek 0 ps1.ps_stack = stack_peek dist ps.ps_stack` by
    metis_tac[do_swap_wide_peek_ends, pairTheory.SND] >>
  metis_tac[do_swap_wide_peek_ends, pairTheory.SND]
QED

Theorem reorder_one_wide_preserves_fixed:
  !dfg targets idx op ps ops qs i d.
    idx < LENGTH targets /\ i < idx /\
    LENGTH targets <= LENGTH ps.ps_stack /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    stack_peek (LENGTH targets - 1 - i) qs.ps_stack =
    stack_peek (LENGTH targets - 1 - i) ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  `LENGTH targets - 1 - i = LENGTH targets - (i + 1)` by decide_tac >>
  `reduce_depth_plan (LENGTH ps.ps_stack) targets op
      (LENGTH targets - (idx + 1)) (LENGTH targets) ps = ([],ps)` by
    (Cases_on `LENGTH ps.ps_stack` >> simp[reduce_depth_plan_def] >> decide_tac) >>
  `d < LENGTH ps.ps_stack /\
    ~(LENGTH targets - (idx + 1) < d /\ d < LENGTH targets)` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  Cases_on `d > 16` >> simp[] >>
  qspecl_then [`dfg`, `op`, `d`, `LENGTH targets - (idx + 1)`,
    `LENGTH targets - (i + 1)`, `ps`] mp_tac reorder_place_wide_fixed >>
  (impl_tac >- decide_tac) >>
  Cases_on `d = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps.ps_stack)` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Theorem reorder_one_wide_places:
  !dfg targets idx op ps ops qs d.
    idx < LENGTH targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
    MEM op targets /\
    stack_get_unfixed_depth op (LENGTH targets - 1 - idx)
      (LENGTH targets) ps.ps_stack = SOME d /\
    reorder_one dfg targets idx op ps = (ops,qs) ==>
    stack_peek (LENGTH targets - 1 - idx) qs.ps_stack = op
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH targets - 1 - idx = LENGTH targets - (idx + 1)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> rename1 `_ = (reduce_ops,mid)` >>
  `LENGTH targets <= LENGTH mid.ps_stack` by
    (Cases_on `d > 16` >> gvs[] >>
     drule reduce_depth_plan_target_length_floor >>
     simp[arithmeticTheory.MIN_DEF, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `?dist. stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
      (LENGTH targets) mid.ps_stack = SOME dist` by
    (Cases_on `d > 16` >> gvs[] >>
     drule_all planWfTheory.reduce_depth_plan_dist_ge >>
     disch_then (qspec_then `LENGTH ps.ps_stack` mp_tac) >>
     simp[LET_THM] >> metis_tac[]) >>
  `dist < LENGTH mid.ps_stack /\ stack_peek dist mid.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH targets - (idx + 1) < LENGTH mid.ps_stack` by decide_tac >>
  simp[] >> strip_tac >>
  qspecl_then [`dfg`, `op`, `dist`, `LENGTH targets - (idx + 1)`, `mid`]
    mp_tac reorder_place_wide_places >> simp[] >>
  Cases_on `dist = LENGTH targets - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist mid.ps_stack)
    (stack_peek (LENGTH targets - (idx + 1)) mid.ps_stack)` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem reorder_one_wide_step:
  !dfg targets idx ps ops qs.
    idx < LENGTH targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < idx ==>
      stack_peek (LENGTH targets - 1 - i) ps.ps_stack = EL i targets) /\
    reorder_one dfg targets idx (EL idx targets) ps = (ops,qs) ==>
    LENGTH targets <= LENGTH qs.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x qs.ps_stack = LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < SUC idx ==>
      stack_peek (LENGTH targets - 1 - i) qs.ps_stack = EL i targets)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> Cases_on `MEM x targets`
     >- simp[] >> gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
  `?d. stack_get_unfixed_depth (EL idx targets)
      (LENGTH targets - 1 - idx) (LENGTH targets) ps.ps_stack = SOME d` by
    metis_tac[reorderSimTheory.materialised_pending_next_on_stack_window] >>
  `MEM (EL idx targets) targets` by simp[EL_MEM] >>
  conj_tac >- metis_tac[reorder_one_target_length] >>
  conj_tac >- metis_tac[reorder_one_wide_counts] >>
  gen_tac >> strip_tac >> Cases_on `i = idx`
  >- (qpat_x_assum `i = idx` SUBST_ALL_TAC >>
      metis_tac[reorder_one_wide_places]) >>
  `i < idx` by decide_tac >>
  metis_tac[reorder_one_wide_preserves_fixed]
QED

Theorem reorder_wide_fold_bottom_frame[local]:
  !m k dfg targets ps prefix acc ops qs.
    k + m <= LENGTH targets /\ LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < k ==> stack_peek (LENGTH targets - 1 - i) ps.ps_stack = EL i targets) /\
    FOLDL (\(code,st) (idx,op).
      (\(step,out). (code ++ step,out)) (reorder_one dfg targets idx op st))
      (acc,ps) (GENLIST (\j. (k+j,EL (k+j) targets)) m) = (ops,qs) ==>
    FOLDL (\(code,st) (idx,op).
      (\(step,out). (code ++ step,out)) (reorder_one dfg targets idx op st))
      (acc,ps with ps_stack := prefix ++ ps.ps_stack)
      (GENLIST (\j. (k+j,EL (k+j) targets)) m) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct_on `m` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k < LENGTH targets` by decide_tac >>
  `!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> Cases_on `MEM x targets` >> simp[] >>
     gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
  drule_all reorderSimTheory.materialised_pending_next_on_stack_window >> strip_tac >>
  Cases_on `reorder_one dfg targets k (EL k targets) ps` >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops,mid)` >>
  `MEM (EL k targets) targets` by simp[EL_MEM] >>
  `LENGTH targets - 1 - k = LENGTH targets - (k + 1)` by decide_tac >>
  `LENGTH targets <= LENGTH mid.ps_stack /\
   (!x. MEM x targets ==>
     LIST_ELEM_COUNT x mid.ps_stack = LIST_ELEM_COUNT x ps.ps_stack) /\
   (!i. i < SUC k ==>
     stack_peek (LENGTH targets - 1 - i) mid.ps_stack = EL i targets)` by
    (drule_all reorder_one_wide_step >> simp[]) >>
  `reorder_one dfg targets k (EL k targets)
     (ps with ps_stack := prefix ++ ps.ps_stack) =
     (step_ops,mid with ps_stack := prefix ++ mid.ps_stack)` by
    (irule fnPlanLineageInventoryTheory.reorder_one_shielded_bottom_frame >> fs[]) >>
  `!x. MEM x targets ==>
    LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x mid.ps_stack` by metis_tac[] >>
  `GENLIST (\j. (k+j,EL (k+j) targets)) (SUC m) =
     (k,EL k targets) :: GENLIST (\j. (SUC k+j,EL (SUC k+j) targets)) m` by
    (simp[rich_listTheory.GENLIST_CONS, arithmeticTheory.ADD_CLAUSES, combinTheory.o_DEF] >>
     AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `FOLDL _ _ _ = (ops,qs)` mp_tac >>
  simp[] >> strip_tac >>
  qpat_x_assum `!k dfg targets ps prefix acc ops qs. _`
    (qspec_then `SUC k` mp_tac) >>
  simp[] >> disch_then irule >> fs[]
QED

Theorem reorder_plan_wide_materialised_bottom_frame:
  !dfg targets ps prefix ops qs.
    LENGTH targets <= LENGTH ps.ps_stack /\
    (!x. MEM x targets ==>
      LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg targets ps = (ops,qs) ==>
    reorder_plan dfg targets (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `MAPi (\i op. (i,op)) targets =
   GENLIST (\j. (0+j,EL (0+j) targets)) (LENGTH targets)` by
    simp[LIST_EQ_REWRITE, indexedListsTheory.EL_MAPi, EL_GENLIST] >>
  gvs[reorder_plan_def] >>
  qspecl_then [`LENGTH targets`, `0`] mp_tac reorder_wide_fold_bottom_frame >>
  simp[] >> disch_then irule >> simp[]
QED

Theorem restore_spilled_plan_distinct_materialised:
  !targets ps ops mid.
    ALL_DISTINCT targets /\
    (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    restore_spilled_plan targets ps = (ops,mid) ==>
    (!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x mid.ps_stack) /\
    LENGTH targets <= LENGTH mid.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  drule fnPlanLineageInventoryTheory.restore_spilled_plan_inventory_count >> strip_tac >>
  `!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x mid.ps_stack` by
    (gen_tac >> Cases_on `MEM x targets`
     >- (drule fnPlanLineageInventoryTheory.all_distinct_elem_count_le_one >>
         disch_then (qspec_then `x` assume_tac) >>
         `x NOTIN FDOM mid.ps_spilled` by simp[] >>
         `MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled` by simp[] >>
         qpat_x_assum `!x. LIST_ELEM_COUNT x mid.ps_stack + _ = _`
           (qspec_then `x` mp_tac) >>
         Cases_on `x IN FDOM ps.ps_spilled` >>
         fs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
     fs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
  simp[] >> irule list_elem_count_dom_length >> simp[]
QED

Theorem restore_reorder_wide_bottom_frame:
  !targets ps restore_ops mid dfg reorder_ops out prefix.
    ALL_DISTINCT targets /\
    (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    restore_spilled_plan targets ps = (restore_ops,mid) /\
    reorder_plan dfg targets mid = (reorder_ops,out) ==>
    restore_spilled_plan targets (ps with ps_stack := prefix ++ ps.ps_stack) =
      (restore_ops,mid with ps_stack := prefix ++ mid.ps_stack) /\
    reorder_plan dfg targets (mid with ps_stack := prefix ++ mid.ps_stack) =
      (reorder_ops,out with ps_stack := prefix ++ out.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all restore_spilled_plan_distinct_materialised >> strip_tac >>
  conj_tac
  >- (irule fnPlanLineageInventoryTheory.restore_spilled_plan_bottom_frame >> simp[]) >>
  irule reorder_plan_wide_materialised_bottom_frame >> simp[]
QED

Theorem terminal_jmp_regular_bottom_frame:
  !liveness dfg cfg fn inst next_live halt next_term lbl ps prefix ops out dest.
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
    inst.inst_outputs = [] /\
    (!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
      ALL_DISTINCT targets /\
      (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled)) /\
    generate_regular_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl ps =
      (ops,out) ==>
    generate_regular_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,out with ps_stack := prefix ++ out.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `!dfg ps. reorder_plan dfg [] ps = ([],ps)` by simp[reorder_plan_def] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, stackPlanTypesTheory.is_label_operand_def,
       emit_input_plan_def, is_commutative_def,
       stack_pop_def, generate_emit_ops_def, venom_to_evm_name_def] >>
  Cases_on `join_target_ops liveness fn lbl inst` >> simp[]
  >- (strip_tac >> gvs[fnPlanLineageSetupTheory.release_dead_spills_stack_update,
                       release_dead_spills_stack]) >>
  rename1 `join_target_ops liveness fn lbl inst = SOME targets` >>
  namedCases_on `restore_spilled_plan targets ps` ["rops mid"] >>
  namedCases_on `reorder_plan dfg targets mid` ["sops tail"] >>
  `ALL_DISTINCT targets /\
   (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled)` by metis_tac[] >>
  drule_all restore_reorder_wide_bottom_frame >>
  disch_then (qspec_then `prefix` strip_assume_tac) >>
  simp[] >> strip_tac >>
  gvs[fnPlanLineageSetupTheory.release_dead_spills_stack_update, release_dead_spills_stack]
QED

Theorem join_reached_bottom_extension:
  !liveness fn lbl inst out prefix.
    (!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
      LENGTH targets <= LENGTH out.ps_stack) ==>
    (join_reached liveness fn lbl inst
       (out with ps_stack := prefix ++ out.ps_stack) <=>
     join_reached liveness fn lbl inst out)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `join_target_ops liveness fn lbl inst` >>
  simp[join_reached_def] >>
  `LENGTH x <= LENGTH out.ps_stack` by metis_tac[] >>
  simp[stack_pop_bottom_extension, APPEND_ASSOC]
QED

Theorem terminal_jmp_regular_target_height:
  !liveness dfg cfg fn inst next_live halt next_term lbl ps ops out dest.
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
    inst.inst_outputs = [] /\
    (!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
      ALL_DISTINCT targets /\
      (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled)) /\
    generate_regular_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl ps =
      (ops,out) ==>
    (!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
      LENGTH targets <= LENGTH out.ps_stack)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `!dfg ps. reorder_plan dfg [] ps = ([],ps)` by simp[reorder_plan_def] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, stackPlanTypesTheory.is_label_operand_def,
       emit_input_plan_def, is_commutative_def,
       stack_pop_def, generate_emit_ops_def, venom_to_evm_name_def] >>
  namedCases_on `restore_spilled_plan targets ps` ["rops mid"] >>
  namedCases_on `reorder_plan dfg targets mid` ["sops tail"] >>
  `ALL_DISTINCT targets /\
   (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled)` by metis_tac[] >>
  drule_all restore_spilled_plan_distinct_materialised >> strip_tac >>
  drule_all reorder_plan_target_length >> strip_tac >>
  simp[] >> strip_tac >> gvs[release_dead_spills_stack]
QED

Theorem terminal_jmp_inst_bottom_frame:
  !liveness dfg cfg fn inst next_live halt next_term lbl ps prefix ops out dest.
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
    inst.inst_outputs = [] /\
    (!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
      ALL_DISTINCT targets /\
      (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled)) /\
    generate_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl ps =
      SOME (ops,out) ==>
    generate_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      SOME (ops,out with ps_stack := prefix ++ out.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
     is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
     is_raw_fmp_opcode_def, is_param_opcode_def, AllCaseEqs()] >>
  `!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
     LENGTH targets <= LENGTH out.ps_stack` by
    metis_tac[terminal_jmp_regular_target_height] >>
  `generate_regular_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl
     (ps with ps_stack := prefix ++ ps.ps_stack) =
     (ops,out with ps_stack := prefix ++ out.ps_stack)` by
    (irule terminal_jmp_regular_bottom_frame >> simp[] >> metis_tac[]) >>
  `join_reached liveness fn lbl inst (out with ps_stack := prefix ++ out.ps_stack) <=>
     join_reached liveness fn lbl inst out` by
    (irule join_reached_bottom_extension >> metis_tac[]) >>
  simp[]
QED

Theorem terminal_jmp_inst_bottom_reflection:
  !liveness dfg cfg fn inst next_live halt next_term lbl ps prefix ops extended_out dest.
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
    inst.inst_outputs = [] /\
    (!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
      ALL_DISTINCT targets /\
      (!x. MEM x targets ==> MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled)) /\
    generate_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl
      (ps with ps_stack := prefix ++ ps.ps_stack) = SOME (ops,extended_out) ==>
    ?out. generate_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl ps =
      SOME (ops,out) /\ extended_out = out with ps_stack := prefix ++ out.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  namedCases_on `generate_regular_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl ps`
    ["core_ops out"] >>
  `!targets. join_target_ops liveness fn lbl inst = SOME targets ==>
     LENGTH targets <= LENGTH out.ps_stack` by
    metis_tac[terminal_jmp_regular_target_height] >>
  `generate_regular_inst_plan liveness dfg cfg fn inst next_live halt next_term lbl
     (ps with ps_stack := prefix ++ ps.ps_stack) =
     (core_ops,out with ps_stack := prefix ++ out.ps_stack)` by
    (irule terminal_jmp_regular_bottom_frame >> simp[] >> metis_tac[]) >>
  `join_reached liveness fn lbl inst (out with ps_stack := prefix ++ out.ps_stack) <=>
     join_reached liveness fn lbl inst out` by
    (irule join_reached_bottom_extension >> metis_tac[]) >>
  qexists_tac `out` >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
     is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
     is_raw_fmp_opcode_def, is_param_opcode_def, AllCaseEqs()]
QED
