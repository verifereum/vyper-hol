(* Structural administrative boundaries for the regular instruction planner. *)
Theory staticAbortPlanBoundary
Ancestors
  planWf planAlign fnBlockPlanStaticBalance fnPlanPrefix stackPlanGen stackPlanOps
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

Theorem selected_reorder_wf_len[local]:
  LENGTH operands <= LENGTH ps.ps_stack /\ LENGTH operands <= 16 /\
  reorder_plan dfg operands ps = (oa,sa) /\
  swapped = TAKE (LENGTH operands - 2) operands ++
    [EL (LENGTH operands - 1) operands; EL (LENGTH operands - 2) operands] /\
  reorder_plan dfg swapped ps = (ob,sb) /\
  (if comm /\ 2 <= LENGTH operands then
     (if reorder_cost oa < reorder_cost ob then (oa,sa) else (ob,sb))
   else reorder_plan dfg operands ps) = (ops,qs) ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_end_len lo (LENGTH ps.ps_stack) ops = LENGTH qs.ps_stack /\
  LENGTH operands <= LENGTH qs.ps_stack
Proof
  strip_tac >>
  Cases_on `comm /\ 2 <= LENGTH operands`
  >- (`LENGTH (TAKE (LENGTH operands - 2) operands ++
          [EL (LENGTH operands - 1) operands; EL (LENGTH operands - 2) operands]) =
        LENGTH operands` by simp[] >>
      qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >>
      IF_CASES_TAC >> strip_tac >> gvs[] >>
      imp_res_tac reorder_plan_length_floor >>
      qspecl_then [`dfg`, `operands`, `ps`, `lo`] mp_tac reorder_plan_wf_len >>
      qspecl_then [`dfg`, `TAKE (LENGTH operands - 2) operands ++
        [EL (LENGTH operands - 1) operands; EL (LENGTH operands - 2) operands]`,
        `ps`, `lo`] mp_tac reorder_plan_wf_len >> fs[]) >>
  gvs[] >> imp_res_tac reorder_plan_length_floor >>
  qspecl_then [`dfg`, `operands`, `ps`, `lo`] mp_tac reorder_plan_wf_len >> simp[]
QED

Theorem regular_plan_admin_decomposition:
  generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs) /\
  inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) ==>
  ?pre emit post ps6 ps7 m h.
    ops = pre ++ emit ++ post /\
    prefix_wf lo (LENGTH ps.ps_stack) pre /\
    prefix_end_len lo (LENGTH ps.ps_stack) pre = m /\
    LENGTH (compute_operands inst) <= m /\
    h + LENGTH (compute_operands inst) = m + LENGTH inst.inst_outputs /\
    LENGTH ps6.ps_stack = h /\
    generate_emit_ops inst (case inst.inst_opcode of LOG =>
      (case HD inst.inst_operands of Lit v => w2n v | _ => 0) | _ => 0) ps6 = (emit,ps7) /\
    LENGTH ps7.ps_stack = h /\
    prefix_wf lo h post /\ prefix_end_len lo h post = LENGTH qs.ps_stack
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics core` >>
  `prefix_wf lo (LENGTH ps.ps_stack) input_ops /\
   prefix_end_len lo (LENGTH ps.ps_stack) input_ops = LENGTH ps1.ps_stack` by
    (drule regular_input_plan_wf_len >>
     disch_then (qspecl_then [`nl`, `ps`] mp_tac) >> simp[]) >>
  `LENGTH (compute_operands inst) <= LENGTH ps1.ps_stack` by fs[] >>
  `prefix_wf lo (LENGTH ps1.ps_stack) reorder_ops /\
   prefix_end_len lo (LENGTH ps1.ps_stack) reorder_ops = LENGTH ps4.ps_stack /\
   LENGTH (compute_operands inst) <= LENGTH ps4.ps_stack` by
    (Cases_on `reorder_plan dfg (compute_operands inst) ps1` >>
     Cases_on `reorder_plan dfg
       (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
        [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
         EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]) ps1` >>
     irule selected_reorder_wf_len >> simp[] >>
     qexistsl [`is_commutative inst.inst_opcode`, `dfg`] >>
     fs[arithmeticTheory.GREATER_EQ, LET_THM]) >>
  `prefix_wf lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops) /\
   prefix_end_len lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops) = LENGTH ps4.ps_stack` by
    metis_tac[prefix_wf_len_append] >>
  `LENGTH core.ps_stack + LENGTH (compute_operands inst) =
    LENGTH ps4.ps_stack + LENGTH inst.inst_outputs` by
    (simp[Abbr `core`, push_outputs_length, stack_pop_def]) >>
  pairarg_tac >> simp[] >>
  `LENGTH ps7.ps_stack = LENGTH core.ps_stack` by
    metis_tac[generate_emit_ops_stack, pairTheory.SND] >>
  Cases_on `inst.inst_outputs = []` >> simp[]
  >- (strip_tac >> gvs[] >>
      qexistsl [`input_ops ++ reorder_ops`, `emit_ops`, `[]`, `core`, `ps7`] >>
      simp[APPEND_ASSOC, prefix_wf_def, prefix_end_len_def, release_dead_spills_stack] >>
      decide_tac) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  `prefix_wf lo (LENGTH ps7.ps_stack) pop_ops /\
   prefix_end_len lo (LENGTH ps7.ps_stack) pop_ops = LENGTH ps8.ps_stack` by
    (qpat_x_assum `(if _ then _ else _) = (pop_ops,ps8)` mp_tac >>
     IF_CASES_TAC >> simp[]
     >- (strip_tac >> qspecl_then
           [`MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)`, `ps7`, `lo`]
           mp_tac popmany_plan_wf_len >> simp[]) >>
     strip_tac >> gvs[prefix_wf_def, prefix_end_len_def]) >>
  `prefix_wf lo (LENGTH ps8.ps_stack) opt_ops /\
   prefix_end_len lo (LENGTH ps8.ps_stack) opt_ops = LENGTH ps9.ps_stack` by
    (qpat_x_assum `(if _ then _ else _) = (opt_ops,ps9)` mp_tac >>
     IF_CASES_TAC >> simp[prefix_wf_def, prefix_end_len_def] >>
     strip_tac >> qspecl_then [`dfg`, `inst`, `nl`, `term`, `ps8`, `lo`]
       mp_tac optimistic_swap_plan_wf_len >> simp[]) >>
  qexistsl [`input_ops ++ reorder_ops`, `emit_ops`, `pop_ops ++ opt_ops`, `core`, `ps7`] >>
  simp[APPEND_ASSOC, release_dead_spills_stack] >>
  `LENGTH qs.ps_stack = LENGTH ps9.ps_stack` by
    metis_tac[release_dead_spills_stack] >>
  metis_tac[prefix_wf_len_append]
QED
