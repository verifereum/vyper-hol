(* Structural administrative boundaries for the regular instruction planner. *)
Theory staticAbortPlanBoundary
Ancestors
  planWf planAlign fnBlockPlanStaticBalance stackPlanGen stackPlanOps
  stackModel prefixExec cleanOpsSim doSwapSim list rich_list arithmetic sorting

Theorem popmany_fold_wf_len[local]:
  !items acc ps ops qs lo n.
    FOLDL pop_foldl_body (acc,ps) items = (ops,qs) /\
    prefix_wf lo n acc /\
    prefix_end_len lo n acc = LENGTH ps.ps_stack ==>
    prefix_wf lo n ops /\ prefix_end_len lo n ops = LENGTH qs.ps_stack
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_depth h ps.ps_stack`
  >- (fs[pop_foldl_body_def] >> first_x_assum irule >>
      rpt (first_assum $ irule_at Any)) >>
  rename1 `stack_get_depth h ps.ps_stack = SOME d` >>
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  Cases_on `do_swap d ps` >> rename1 `do_swap d ps = (sw,mid)` >>
  `prefix_wf lo (LENGTH ps.ps_stack) sw /\
   prefix_end_len lo (LENGTH ps.ps_stack) sw = LENGTH mid.ps_stack` by
    (drule do_swap_wf_len >> simp[]) >>
  `LENGTH mid.ps_stack = LENGTH ps.ps_stack` by
    metis_tac[do_swap_stack_perm, sortingTheory.PERM_LENGTH, pairTheory.SND] >>
  `pop_foldl_body (acc,ps) h =
    (acc ++ sw ++ [SOPop 1], mid with ps_stack := stack_pop 1 mid.ps_stack)` by
    (qpat_x_assum `!acc ps ops qs lo n. _` kall_tac >>
     qpat_x_assum `FOLDL _ _ _ = _` kall_tac >>
     Cases_on `d = 0`
     >- (gvs[] >> qpat_x_assum `do_swap 0 ps = _` mp_tac >>
         simp[do_swap_def] >> strip_tac >>
         qpat_x_assum `ps = mid` SUBST_ALL_TAC >>
         qpat_x_assum `sw = []` SUBST_ALL_TAC >>
         simp[pop_foldl_body_def]) >>
     simp[pop_foldl_body_def]) >>
  fs[] >> first_x_assum (qspecl_then
    [`acc ++ sw ++ [SOPop 1]`, `mid with ps_stack := stack_pop 1 mid.ps_stack`]
    MATCH_MP_TAC) >> simp[] >>
  `prefix_wf lo n (acc ++ sw) /\
   prefix_end_len lo n (acc ++ sw) = LENGTH mid.ps_stack` by
    metis_tac[prefix_wf_len_append] >>
  `prefix_wf lo (LENGTH mid.ps_stack) [SOPop 1] /\
   prefix_end_len lo (LENGTH mid.ps_stack) [SOPop 1] = LENGTH ps.ps_stack - 1` by
    simp[prefix_wf_def, prefix_end_len_def, stack_op_wf_def] >>
  metis_tac[prefix_wf_len_append]
QED

Theorem popmany_plan_wf_len:
  !items ps lo.
    prefix_wf lo (LENGTH ps.ps_stack) (FST (popmany_plan items ps)) /\
    prefix_end_len lo (LENGTH ps.ps_stack) (FST (popmany_plan items ps)) =
      LENGTH (SND (popmany_plan items ps)).ps_stack
Proof
  rpt gen_tac >> Cases_on `items = []`
  >- simp[popmany_plan_def, prefix_wf_def, prefix_end_len_def] >>
  Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items))`
  >- (
      `LENGTH items < LENGTH ps.ps_stack` by metis_tac[contiguous_top_stack_bound] >>
      `LENGTH items <= 16` by fs[is_contiguous_top_def] >>
      Cases_on `items` >- fs[] >>
      fs[] >> simp[popmany_plan_def] >>
      simp[do_swap_def, prefix_wf_def, prefix_end_len_def, stack_op_wf_def,
           stack_pop_def, stack_swap_def]) >>
  `popmany_plan items ps = popmany_individual items ps` by
    (Cases_on `items` >> gvs[popmany_plan_def, EVERY_MEM, EXISTS_MEM] >>
     IF_CASES_TAC >> gvs[] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  simp[popmany_individual_eq_foldl] >>
  irule popmany_fold_wf_len >>
  qexistsl [`[]`, `QSORT (\a b. case stack_get_depth a ps.ps_stack of
    NONE => T | SOME da => case stack_get_depth b ps.ps_stack of
      NONE => T | SOME db => da <= db) items`, `ps`] >>
  simp[prefix_wf_def, prefix_end_len_def]
QED

Theorem optimistic_swap_plan_wf_len:
  !dfg inst nl nt ps lo.
    prefix_wf lo (LENGTH ps.ps_stack)
      (FST (optimistic_swap_plan dfg inst nl nt ps)) /\
    prefix_end_len lo (LENGTH ps.ps_stack)
      (FST (optimistic_swap_plan dfg inst nl nt ps)) =
      LENGTH (SND (optimistic_swap_plan dfg inst nl nt ps)).ps_stack
Proof
  rpt gen_tac >> rename1 `optimistic_swap_plan dfg inst nl term ps` >>
  simp[optimistic_swap_plan_def] >>
  Cases_on `term` >- simp[prefix_wf_def, prefix_end_len_def] >>
  Cases_on `inst.inst_outputs = []` >- simp[prefix_wf_def, prefix_end_len_def] >>
  Cases_on `nl = []` >- simp[prefix_wf_def, prefix_end_len_def] >>
  Cases_on `operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST nl))`
  >- simp[prefix_wf_def, prefix_end_len_def] >>
  simp[] >> Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack`
  >- simp[prefix_wf_def, prefix_end_len_def] >>
  simp[] >> Cases_on `do_swap x ps` >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  drule do_swap_wf_len >> simp[]
QED

Theorem emit_input_plan_no_labels_opcode[local]:
  !operands opc other nl ps.
    (!l. ~MEM (Label l) operands) ==>
    emit_input_plan opc operands nl ps = emit_input_plan other operands nl ps
Proof
  Induct >- simp[] >> rpt strip_tac >>
  `!live qs. emit_one_input opc live h qs = emit_one_input other live h qs` by
    (Cases_on `h` >> fs[emit_one_input_def] >> metis_tac[]) >>
  simp[emit_input_plan_def] >>
  Cases_on `emit_one_input other (operand_vars operands ++ nl) h ps` >> simp[] >>
  first_x_assum (qspecl_then [`opc`, `other`, `nl`, `r`] mp_tac) >>
  impl_tac >- metis_tac[MEM] >> simp[]
QED

Theorem regular_input_plan_wf_len:
  !inst nl ps lo.
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) ==>
    prefix_wf lo (LENGTH ps.ps_stack)
      (FST (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)) /\
    prefix_end_len lo (LENGTH ps.ps_stack)
      (FST (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)) =
      LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack
Proof
  rpt gen_tac >> disch_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (`!l. ~MEM (Label l) (compute_operands inst)` by
        fs[compute_operands_def, asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
      `emit_input_plan inst.inst_opcode (compute_operands inst) nl ps =
       emit_input_plan ADD (compute_operands inst) nl ps` by
        metis_tac[emit_input_plan_no_labels_opcode] >>
      simp[emit_input_plan_wf_len]) >>
  simp[emit_input_plan_wf_len]
QED
