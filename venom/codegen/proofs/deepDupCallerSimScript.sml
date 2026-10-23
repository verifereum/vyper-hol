(* Caller boundaries for the two-input deep-DUP case. *)
Theory deepDupCallerSim
Ancestors deepDupFrameSim stackPlanGen doSwapSim stackPlanTypes stackModel
          stackPlanOps planWf finite_map list rich_list
Libs BasicProvers

Theorem caller_stack_get_depth_push[local]:
  !op stk. stack_get_depth op (stack_push op stk) = SOME 0
Proof
  simp[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def]
QED

Theorem emit_one_input_stack_growth:
  !opc nl op ps ops ps'.
    emit_one_input opc nl op ps = (ops,ps') ==>
    LENGTH ps'.ps_stack <= LENGTH ps.ps_stack + 2 /\
    (LENGTH ps.ps_stack + 1 < LENGTH ps'.ps_stack ==>
       ps'.ps_stack = ps.ps_stack ++ [op;op]) /\
    (?extra. ps'.ps_stack = ps.ps_stack ++ extra /\ LENGTH extra <= 2)
Proof
  rpt gen_tac >>
  Cases_on `op` >>
  simp[emit_one_input_def, is_var_operand_def, LET_THM]
  >- (strip_tac >> gvs[stack_push_def])
  >- (Cases_on `FLOOKUP ps.ps_spilled (Var s)` >>
      simp[do_restore_def, LET_THM]
      >- (Cases_on `MEM s nl` >> simp[]
          >- (Cases_on `stack_get_depth (Var s) ps.ps_stack` >> simp[] >>
              Cases_on `do_dup x ps` >> simp[] >> strip_tac >> gvs[] >>
              `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
              drule do_dup_stack_exact >> simp[] >> strip_tac >> gvs[]) >>
          strip_tac >> gvs[])
      >> simp[caller_stack_get_depth_push] >>
      Cases_on `MEM s nl` >>
      simp[do_dup_def, stack_dup_def, stack_push_def, stack_peek_def,
           EL_APPEND_EQN] >> strip_tac >> gvs[EL_APPEND_EQN])
  >> Cases_on `opc = INVOKE` >> simp[] >>
     strip_tac >> gvs[stack_push_def]
QED

Theorem caller_stack_find_prefix_bound[local]:
  !ys p xs d. stack_find p xs = SOME d ==>
    ?e. stack_find p (ys ++ xs) = SOME e /\ e <= LENGTH ys + d
Proof
  Induct >> simp[stack_find_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `p h` >> simp[] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  qexists `e + 1` >> simp[]
QED

Theorem caller_stack_get_depth_append_bound:
  !op xs ys d. stack_get_depth op xs = SOME d ==>
    ?e. stack_get_depth op (xs ++ ys) = SOME e /\ e <= LENGTH ys + d
Proof
  simp[stack_get_depth_def, REVERSE_APPEND] >> rpt strip_tac >>
  drule caller_stack_find_prefix_bound >>
  disch_then (qspec_then `REVERSE ys` mp_tac) >> simp[]
QED

Theorem emit_one_input_second_depth_bound:
  !opc nl op ps ops ps' other d.
    emit_one_input opc nl op ps = (ops,ps') /\
    stack_get_depth other ps.ps_stack = SOME d /\ d <= 15 ==>
    ?e. stack_get_depth other ps'.ps_stack = SOME e /\ e <= 17 /\
        (e = 17 ==> ps'.ps_stack = ps.ps_stack ++ [op;op])
Proof
  rpt strip_tac >> drule emit_one_input_stack_growth >> strip_tac >>
  drule caller_stack_get_depth_append_bound >>
  disch_then (qspec_then `extra` mp_tac) >> strip_tac >>
  qexists `e` >> conj_tac >- metis_tac[] >>
  conj_tac >- decide_tac >> strip_tac >>
  first_x_assum irule >> gvs[]
QED

Theorem do_dup17_duplicate_top_not_wf:
  !ps xs x ops ps' f lo tail.
    ps.ps_stack = xs ++ [x;x] /\ 17 < LENGTH ps.ps_stack /\
    do_dup 17 ps = (ops,ps') ==>
    ~prefix_spill_wf f lo (ops ++ tail) ps
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`17`, `ps`] do_dup_big_decompose) >>
  simp[] >> strip_tac >>
  `top_n 2 ps.ps_stack = [x;x]` by
    simp[top_n_def, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  gvs[LET_THM] >>
  qmatch_asmsub_abbrev_tac `spill_alloc_n [] ps.ps_alloc items` >>
  `LENGTH (FST (spill_alloc_n [] ps.ps_alloc items)) = 2` by
    simp[spill_alloc_n_offsets_length, Abbr `items`] >>
  Cases_on `FST (spill_alloc_n [] ps.ps_alloc items)` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[Abbr `items`] >>
  metis_tac[duplicate_key_spill_restore_not_wf, APPEND]
QED

Theorem do_dup_two_growth_venom_asm_rel:
  !dist ps ops target lo o2pc prog vs before.
    do_dup dist ps = (ops,target) /\ dist < LENGTH ps.ps_stack /\
    dist <= 17 /\
    (dist = 17 ==> ?xs x. ps.ps_stack = xs ++ [x;x]) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    prefix_spill_wf initial_fmp lo ops ps /\
    venom_asm_rel lo ps vs before /\
    asm_block_at prog before.as_pc (execute_plan initial_fmp ops) ==>
    ?after.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) before = AsmOK after /\
      venom_asm_rel lo target vs after /\
      after.as_pc = before.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt strip_tac >> Cases_on `dist = 17`
  >- (gvs[] >>
      `17 < LENGTH ps.ps_stack` by simp[] >>
      drule_all do_dup17_duplicate_top_not_wf >>
      disch_then (qspecl_then [`initial_fmp`, `lo`, `[]`] mp_tac) >> simp[]) >>
  Cases_on `dist = 16`
  >- (gvs[] >> metis_tac[do_dup16_venom_asm_rel_frame, arithmeticTheory.ADD_COMM]) >>
  `dist <= 15` by decide_tac >>
  `15 < dist ==> ALL_DISTINCT (top_n (dist - 15) ps.ps_stack) /\
     DISJOINT (set (top_n (dist - 15) ps.ps_stack)) (FDOM ps.ps_spilled)` by simp[] >>
  metis_tac[do_dup_venom_asm_rel_layout, arithmeticTheory.ADD_COMM]
QED

Theorem emit_one_input_restored_depth_zero:
  !opc nl op ps ops target.
    emit_one_input opc nl op ps = (ops,target) /\
    is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op) ==>
    stack_get_depth op target.ps_stack = SOME 0
Proof
  rpt gen_tac >> Cases_on `op` >> simp[is_var_operand_def] >>
  Cases_on `FLOOKUP ps.ps_spilled (Var s)` >> simp[] >> strip_tac >>
  gvs[emit_one_input_def, is_var_operand_def, do_restore_def, LET_THM,
      caller_stack_get_depth_push] >>
  Cases_on `MEM s nl` >>
  gvs[do_dup_def, stack_dup_def, stack_peek_def, stack_push_def,
      EL_APPEND_EQN] >>
  simp[stack_get_depth_def, REVERSE_SNOC, stack_find_def, EL_LENGTH_SNOC]
QED
