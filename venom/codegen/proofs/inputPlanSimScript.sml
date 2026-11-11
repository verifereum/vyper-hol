(* Operand preparation against the compiler-checked assembly program.
   TOP-LEVEL: emit_operand_sim, emit_input_plan_sim.
   Deep duplication may spill repeated operands;
   physical spill slots, rather than the temporary operand map, track them. *)
Theory inputPlanSim
Ancestors
  emitOperandSim emitInputSim singleInputSim doDupCorrect spillWordBounds
  stackPlanGen stackPlanOps stackPlanTypes stackModel codegenRel asmSem planExec
  planAlign planWf mixedPrefixSim prefixExec list rich_list finite_map arithmetic
  dfgDefs stackOpSim reorderSim

Theorem emit_operand_owned_sim[local]:
  !opc nl op ps ops post initial_fmp lo o2pc prog vs st.
    opc <> INVOKE /\
    (is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_one_input opc nl op ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`,`ops`,`post`,`initial_fmp`,`lo`]
       emit_one_input_prefix_spill_wf_owned) >>
     (impl_tac >- (asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
       mp_tac (Q.SPECL [`initial_fmp`,`ops`,`prog`,`st.as_pc`,`off`]
         plan_restore_offset_word_bound) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
       simp_tac bool_ss [])) >> simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,
    `o2pc`,`prog`,`vs`,`st`] emit_one_input_venom_asm_rel) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

Theorem emit_operand_unspilled_sim[local]:
  !opc nl v ps ops post initial_fmp lo o2pc prog vs st.
    FLOOKUP ps.ps_spilled (Var v) = NONE /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_one_input opc nl (Var v) ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
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
      mp_tac (Q.SPECL [`dist`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,
        `o2pc`,`prog`,`vs`,`st`] do_dup_venom_asm_rel) >>
      (impl_tac >- (asm_rewrite_tac [] >> conj_tac
        >- (drule stack_get_depth_bound >> simp[]) >>
        rpt gen_tac >> strip_tac >>
        mp_tac (Q.SPECL [`initial_fmp`,`ops`,`prog`,`st.as_pc`,`off`]
          plan_spill_offset_word_bound) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        simp_tac bool_ss [])) >> simp_tac std_ss [ADD_COMM]) >>
  strip_tac >> gvs[] >> qexists_tac `st` >>
  simp[execute_plan_def, asm_steps_def]
QED

Theorem emit_operand_sim:
  !opc nl op ps ops post initial_fmp lo o2pc prog vs st.
    opc <> INVOKE /\
    (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_one_input opc nl op ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_var_operand op /\ FLOOKUP ps.ps_spilled op = NONE`
  >- (Cases_on `op` >> gvs[is_var_operand_def] >> rename1 `Var v` >>
      mp_tac (Q.SPECL [`opc`,`nl`,`v`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,
        `o2pc`,`prog`,`vs`,`st`] emit_operand_unspilled_sim) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp_tac std_ss [ADD_COMM]) >>
  `is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)` by
    (Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[]) >>
  mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`,`ops`,`post`,`initial_fmp`,`lo`,
    `o2pc`,`prog`,`vs`,`st`] emit_operand_owned_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []
QED

Theorem emit_input_plan_sim:
  !operands opc nl ps ops post initial_fmp lo o2pc prog vs st.
    opc <> INVOKE /\
    (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    emit_input_plan opc operands nl ps = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct
  >- (simp[emit_input_plan_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (first_ops,mid)` >>
  Cases_on `emit_input_plan opc operands nl mid` >>
  rename1 `emit_input_plan opc operands nl mid = (rest_ops,last)` >>
  `ops = first_ops ++ rest_ops /\ post = last` by
    (qpat_x_assum `emit_input_plan opc (h::operands) nl ps = _` mp_tac >>
     simp[Once emit_input_plan_def, LET_THM]) >> gvs[] >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp first_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp first_ops))
     (execute_plan initial_fmp rest_ops)` by
    fs[execute_plan_append, asm_block_at_append] >>
  mp_tac (Q.SPECL [`opc`,`operand_vars operands ++ nl`,`h`,`ps`,`first_ops`,
    `mid`,`initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`] emit_operand_sim) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> rpt strip_tac >>
    qpat_assum `!l. MEM (Label l) (h::operands) ==> _`
      (qspec_then `l` mp_tac) >> simp[])) >>
  disch_then (qx_choose_then `st1` strip_assume_tac) >>
  `spill_alloc_layout_wf mid.ps_alloc mid.ps_spilled` by
    (drule_all emit_one_input_layout_wf >> simp[]) >>
  first_x_assum (qspecl_then [`opc`,`nl`,`mid`,`rest_ops`,`last`,`initial_fmp`,
    `lo`,`o2pc`,`prog`,`vs`,`st1`] mp_tac) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> rpt strip_tac >>
    qpat_assum `!l. MEM (Label l) (h::operands) ==> _`
      (qspec_then `l` mp_tac) >> simp[])) >>
  disch_then (qx_choose_then `st2` strip_assume_tac) >>
  qexists_tac `st2` >>
  asm_simp_tac std_ss [execute_plan_append, LENGTH_APPEND, asm_steps_add,
    ADD_ASSOC] >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem emit_input_plan_residual_budget_wf:
  !operands pending alloc_base opc nl ps ops post.
    residual_budget_wf alloc_base pending ps /\
    emit_input_plan opc operands nl ps = (ops,post) ==>
    residual_budget_wf alloc_base (pending ++ operands) post
Proof
  Induct >- simp[emit_input_plan_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc operands nl mid` >>
  rename1 `emit_input_plan opc operands nl mid = (rest_ops,last)` >>
  `ops = step_ops ++ rest_ops /\ post = last` by
    (qpat_x_assum `emit_input_plan opc (h::operands) nl ps = _` mp_tac >>
     simp[Once emit_input_plan_def, LET_THM]) >> gvs[] >>
  `residual_budget_wf alloc_base (pending ++ [h]) mid` by
    (mp_tac (Q.SPECL [`alloc_base`,`pending`,`opc`,
       `operand_vars operands ++ nl`,`h`,`ps`,`step_ops`,`mid`]
       emit_one_input_residual_budget_wf) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  first_x_assum (qspecl_then [`pending ++ [h]`,`alloc_base`,`opc`,`nl`,`mid`,
    `rest_ops`,`last`] mp_tac) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac []
QED
