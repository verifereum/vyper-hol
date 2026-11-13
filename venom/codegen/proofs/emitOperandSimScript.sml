(* Physical simulation of operand preparation, including deep duplication.
   TOP-LEVEL: do_restore_venom_asm_rel, emit_one_input_venom_asm_rel. *)
Theory emitOperandSim
Ancestors
  emitInputSim doDupCorrect doDupModel doSwapSim spillSim allocMono planAlign planWf
  stackOpSim
  stackPlanGen stackPlanOps stackPlanTypes stackModel planExec
  prefixExec prefixSim mixedPrefixSim strongPrefixSim
  codegenRel asmSem indexedLists list rich_list finite_map arithmetic

Theorem do_restore_venom_asm_rel:
  !op ps ops ps' initial_fmp lo o2pc prog vs st.
    do_restore op ps = (ops,ps') /\
    prefix_spill_wf initial_fmp lo ops ps /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do_restore _ _ = _` mp_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >> strip_tac >> gvs[]
  >- (qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `off < dimword(:256)` by fs[prefix_spill_wf_def, spill_op_wf_def] >>
  mp_tac (Q.SPECL [`lo`,`o2pc`,`prog`,`off`,`op`,`ps`,`vs`,`st`]
    restore_op_venom_asm_rel) >>
  (impl_tac >- fs[execute_plan_def, exec_stack_op_def]) >> strip_tac >>
  qexists_tac `st'` >>
  asm_simp_tac (srw_ss()) [execute_plan_def, exec_stack_op_def, ADD_COMM] >>
  irule venom_asm_rel_ps_transfer >>
  qexists_tac `ps with <|ps_stack := stack_push op ps.ps_stack;
    ps_spilled := ps.ps_spilled \\ op|>` >>
  asm_simp_tac (srw_ss()) [free_spill_slot_def]
QED

Theorem emit_one_input_var_unspilled_sim[local]:
  !opc nl v ps ops ps' initial_fmp lo o2pc prog vs st.
    FLOOKUP ps.ps_spilled (Var v) = NONE /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_one_input opc nl (Var v) ps = (ops,ps') /\
    prefix_spill_wf initial_fmp lo ops ps /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [emit_one_input_def, is_var_operand_def] >>
  Cases_on `MEM v nl` >> simp[]
  >- (Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[]
      >- (strip_tac >> gvs[] >> qexists_tac `st` >>
          simp[execute_plan_def, asm_steps_def]) >>
      rename1 `stack_get_depth _ _ = SOME dist` >>
      Cases_on `do_dup dist ps` >> simp[] >> strip_tac >> gvs[] >>
      mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`ps'`,`initial_fmp`,`lo`,
        `o2pc`,`prog`,`vs`,`st`] do_dup_venom_asm_rel_prefix) >>
      (impl_tac >- (asm_rewrite_tac [] >>
        drule stack_get_depth_bound >> simp[])) >>
      simp_tac std_ss [ADD_COMM]) >>
  strip_tac >> gvs[] >> qexists_tac `st` >>
  simp[execute_plan_def, asm_steps_def]
QED

Theorem emit_one_input_var_spilled_plan:
  !opc nl v ps off.
    FLOOKUP ps.ps_spilled (Var v) = SOME off ==>
    let restored = ps with <|ps_stack := stack_push (Var v) ps.ps_stack;
      ps_spilled := ps.ps_spilled \\ Var v;
      ps_alloc := free_spill_slot off ps.ps_alloc|>
    in emit_one_input opc nl (Var v) ps =
      if MEM v nl then
        ([SORestore off; SODup 1],
         restored with ps_stack := stack_dup 0 restored.ps_stack)
      else ([SORestore off], restored)
Proof
  rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) [emit_one_input_def, is_var_operand_def,
    do_restore_def, stack_get_depth_push, do_dup_def] >>
  Cases_on `MEM v nl` >> simp[stack_get_depth_push, do_dup_def]
QED

Theorem emit_one_input_var_spilled_sim[local]:
  !opc nl v ps off ops ps' initial_fmp lo o2pc prog vs st.
    FLOOKUP ps.ps_spilled (Var v) = SOME off /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_one_input opc nl (Var v) ps = (ops,ps') /\
    prefix_spill_wf initial_fmp lo ops ps /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `spill_lookup off ps.ps_spilled = Var v` by
    (pure_rewrite_tac[spill_lookup_def] >> irule spill_hilbert_unique >>
     asm_rewrite_tac [] >>
     drule spill_alloc_layout_wf_spilled_separated >> simp[]) >>
  mp_tac (Q.SPECL [`opc`,`nl`,`v`,`ps`,`off`]
    emit_one_input_var_spilled_plan) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  `prefix_wf lo (LENGTH ps.ps_stack) ops /\ EVERY is_prefix_op ops` by
    (Cases_on `MEM v nl` >> gvs[prefix_wf_def, stack_op_wf_def,
      is_prefix_op_def]) >>
  mp_tac (Q.SPECL [`ops`,`initial_fmp`,`lo`,`o2pc`,`prog`,`ps`,`vs`,`st`]
    mixed_prefix_venom_asm_rel) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `st'` >> asm_rewrite_tac [] >>
  irule venom_asm_rel_ps_transfer >>
  qexists_tac `apply_prefix_ops initial_fmp lo ops ps` >>
  asm_rewrite_tac [] >> Cases_on `MEM v nl` >>
  gvs[apply_prefix_ops_def, apply_prefix_op_def,
    apply_simple_op_def, free_spill_slot_def, stack_dup_def, stack_peek_def,
    stack_push_def, EL_LENGTH_SNOC]
QED

Theorem emit_one_input_venom_asm_rel:
  !opc nl op ps ops ps' initial_fmp lo o2pc prog vs st.
    opc <> INVOKE /\
    (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_one_input opc nl op ps = (ops,ps') /\
    prefix_spill_wf initial_fmp lo ops ps /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op`
  >- (rename1 `Lit w` >>
      mp_tac (Q.SPECL [`opc`,`nl`,`Lit w`,`ps`,`ops`,`ps'`,`lo`,
        `o2pc`,`prog`,`vs`,`st`] emit_one_input_sim) >>
      (impl_tac >- asm_simp_tac (srw_ss()) [is_var_operand_def]) >>
      simp_tac bool_ss [])
  >- (rename1 `Var v` >> Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (mp_tac (Q.SPECL [`opc`,`nl`,`v`,`ps`,`ops`,`ps'`,`initial_fmp`,
            `lo`,`o2pc`,`prog`,`vs`,`st`] emit_one_input_var_unspilled_sim) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          simp_tac bool_ss []) >>
      rename1 `FLOOKUP _ _ = SOME off` >>
      mp_tac (Q.SPECL [`opc`,`nl`,`v`,`ps`,`off`,`ops`,`ps'`,`initial_fmp`,
        `lo`,`o2pc`,`prog`,`vs`,`st`] emit_one_input_var_spilled_sim) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp_tac bool_ss []) >>
  rename1 `Label lbl` >>
  mp_tac (Q.SPECL [`opc`,`nl`,`Label lbl`,`ps`,`ops`,`ps'`,`lo`,
    `o2pc`,`prog`,`vs`,`st`] emit_one_input_sim) >>
  (impl_tac >- asm_simp_tac (srw_ss()) [is_var_operand_def]) >>
  simp_tac bool_ss []
QED

Theorem emit_one_input_layout_wf:
  !opc nl op ps ops ps'.
    emit_one_input opc nl op ps = (ops,ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op`
  >- gvs[emit_one_input_def, is_var_operand_def]
  >- (rename1 `Var v` >> Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (Cases_on `MEM v nl`
          >- (Cases_on `stack_get_depth (Var v) ps.ps_stack`
              >- gvs[emit_one_input_def, is_var_operand_def] >>
              rename1 `stack_get_depth _ _ = SOME dist` >>
              Cases_on `do_dup dist ps` >>
              gvs[emit_one_input_def, is_var_operand_def] >>
              mp_tac (Q.SPECL [`dist`,`ps`] do_dup_layout_wf) >>
              (impl_tac >- (asm_rewrite_tac [] >>
                drule stack_get_depth_bound >> simp[])) >>
              asm_simp_tac (srw_ss()) []) >>
          gvs[emit_one_input_def, is_var_operand_def]) >>
      rename1 `FLOOKUP _ _ = SOME off` >>
      `spill_alloc_layout_wf (free_spill_slot off ps.ps_alloc)
        (ps.ps_spilled \\ Var v)` by
        (irule spill_alloc_layout_wf_after_free >> asm_rewrite_tac []) >>
      mp_tac (Q.SPECL [`opc`,`nl`,`v`,`ps`,`off`]
        emit_one_input_var_spilled_plan) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      simp_tac std_ss [LET_THM] >>
      Cases_on `MEM v nl` >> simp[] >> strip_tac >> gvs[]) >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  simp[emit_one_input_def, is_var_operand_def] >>
  Cases_on `opc = INVOKE` >> simp[] >> strip_tac >> gvs[]
QED

Theorem emit_input_plan_two_venom_asm_rel:
  !opc h h' nl ps ops1 mid ops2 ps' initial_fmp lo o2pc prog vs st.
    opc <> INVOKE /\
    (!l. MEM (Label l) [h;h'] ==> IS_SOME (FLOOKUP lo l)) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_one_input opc (operand_vars [h'] ++ nl) h ps = (ops1,mid) /\
    emit_one_input opc nl h' mid = (ops2,ps') /\
    prefix_spill_wf initial_fmp lo ops1 ps /\
    prefix_spill_wf initial_fmp lo ops2 mid /\ venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
    ?st'. asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  rpt gen_tac >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp ops1) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp ops1))
     (execute_plan initial_fmp ops2)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`opc`,`operand_vars [h'] ++ nl`,`h`,`ps`,`ops1`,`mid`,
    `initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`] emit_one_input_venom_asm_rel) >>
  (impl_tac >- (asm_rewrite_tac [] >> rpt strip_tac >>
    qpat_x_assum `!l. MEM (Label l) [h;h'] ==> _`
      (qspec_then `l` mp_tac) >> simp[])) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  `spill_alloc_layout_wf mid.ps_alloc mid.ps_spilled` by
    (mp_tac (Q.SPECL [`opc`,`operand_vars [h'] ++ nl`,`h`,`ps`,`ops1`,`mid`]
       emit_one_input_layout_wf) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`opc`,`nl`,`h'`,`mid`,`ops2`,`ps'`,`initial_fmp`,
    `lo`,`o2pc`,`prog`,`vs`,`st1`] emit_one_input_venom_asm_rel) >>
  (impl_tac >- (asm_simp_tac std_ss [] >> rpt strip_tac >>
    qpat_x_assum `!l. MEM (Label l) [h;h'] ==> _`
      (qspec_then `l` mp_tac) >> simp[])) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >>
  qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) []
QED

Theorem emit_one_input_same_or_push:
  !opc nl op ps ops ps'.
    emit_one_input opc nl op ps = (ops,ps') ==>
    (ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled) \/
    ?stk. ps'.ps_stack = SNOC op stk
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op`
  >- (gvs[emit_one_input_def, is_var_operand_def, stack_push_def])
  >- (rename1 `Var v` >> Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (Cases_on `MEM v nl`
          >- (Cases_on `stack_get_depth (Var v) ps.ps_stack`
              >- gvs[emit_one_input_def, is_var_operand_def] >>
              rename1 `stack_get_depth _ _ = SOME dist` >>
              drule stack_get_depth_props >> strip_tac >>
              Cases_on `do_dup dist ps` >>
              gvs[emit_one_input_def, is_var_operand_def] >>
              disj2_tac >> qexists_tac `ps.ps_stack` >>
              qpat_assum `do_dup dist ps = _` (fn eq =>
                mp_tac (REWRITE_RULE [eq,pairTheory.SND]
                  (Q.SPECL [`dist`,`ps`] do_dup_stack))) >>
              asm_simp_tac (srw_ss()) [stack_dup_def]) >>
          gvs[emit_one_input_def, is_var_operand_def]) >>
      rename1 `FLOOKUP _ _ = SOME off` >>
      mp_tac (Q.SPECL [`opc`,`nl`,`v`,`ps`,`off`]
        emit_one_input_var_spilled_plan) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      simp_tac std_ss [LET_THM] >>
      Cases_on `MEM v nl` >> simp[] >> strip_tac >>
      gvs[stack_dup_def, stack_peek_def, stack_push_def, EL_LENGTH_SNOC]) >>
  gvs[emit_one_input_def, is_var_operand_def, stack_push_def] >>
  Cases_on `opc = INVOKE` >> gvs[]
QED

Theorem emit_one_input_before_deep_dup:
  !opc nl h v ps ops mid dist.
    ((?d. stack_get_depth (Var v) ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled (Var v))) /\
    emit_one_input opc nl h ps = (ops,mid) /\
    FLOOKUP mid.ps_spilled (Var v) = NONE /\
    stack_get_depth (Var v) mid.ps_stack = SOME dist /\ 15 < dist ==>
    ?stk. mid.ps_stack = SNOC h stk /\ h <> Var v
Proof
  rpt gen_tac >> strip_tac >> drule emit_one_input_same_or_push >> strip_tac
  >- (fs[] >> gvs[] >> decide_tac) >>
  qexists_tac `stk` >> asm_rewrite_tac [] >> strip_tac >>
  gvs[GSYM stack_push_def, stack_get_depth_push]
QED

(* Prepared distinct operands already in their final order need no reorder. *)
Theorem reorder_plan_two_prepared:
  !dfg h h' ps stk.
    ps.ps_stack = stk ++ [h;h'] /\ h <> h' ==>
    reorder_plan dfg [h;h'] ps = ([],ps)
Proof
  rpt gen_tac >> strip_tac >>
  `stack_get_unfixed_depth h 1 2 ps.ps_stack = SOME 1` by
    asm_simp_tac (srw_ss()) [stack_get_unfixed_depth_def,
      stack_get_depth_def, REVERSE_APPEND, stack_find_def] >>
  `stack_get_unfixed_depth h' 0 2 ps.ps_stack = SOME 0` by
    (irule stack_get_unfixed_depth_zero >>
     asm_simp_tac (srw_ss())
       [stack_get_depth_def, REVERSE_APPEND, stack_find_def]) >>
  qpat_x_assum `ps.ps_stack = _` kall_tac >>
  asm_simp_tac (srw_ss()) [reorder_plan_def, reorder_one_def,
    MAPi_def, MAPi_ACC_def, LET_THM]
QED

Theorem emit_deep_second_input_reorder:
  !dfg opc first_nl nl h v ps ops1 mid ops2 ps' dist.
    ((?d. stack_get_depth (Var v) ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled (Var v))) /\
    emit_one_input opc first_nl h ps = (ops1,mid) /\
    FLOOKUP mid.ps_spilled (Var v) = NONE /\ MEM v nl /\
    stack_get_depth (Var v) mid.ps_stack = SOME dist /\ 15 < dist /\
    emit_one_input opc nl (Var v) mid = (ops2,ps') ==>
    reorder_plan dfg [h;Var v] ps' = ([],ps')
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`opc`,`first_nl`,`h`,`v`,`ps`,`ops1`,`mid`,`dist`]
    emit_one_input_before_deep_dup) >>
  (impl_tac >- asm_simp_tac (srw_ss()) []) >>
  disch_then (qx_choose_then `stk` strip_assume_tac) >>
  `stack_peek dist mid.ps_stack = Var v` by
    (drule stack_get_depth_props >> simp[]) >>
  `do_dup dist mid = (ops2,ps')` by
    (qpat_x_assum `emit_one_input opc nl (Var v) mid = _` mp_tac >>
     asm_simp_tac (srw_ss()) [emit_one_input_def, is_var_operand_def] >>
     Cases_on `do_dup dist mid` >> simp[]) >>
  `ps'.ps_stack = stk ++ [h;Var v]` by
    (qpat_assum `do_dup dist mid = _` (fn eq =>
       mp_tac (REWRITE_RULE [eq,pairTheory.SND]
         (Q.SPECL [`dist`,`mid`] do_dup_stack))) >>
     asm_simp_tac (srw_ss()) [stack_dup_def, SNOC_APPEND]) >>
  mp_tac (Q.SPECL [`dfg`,`h`,`Var v`,`ps'`,`stk`] reorder_plan_two_prepared) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED
