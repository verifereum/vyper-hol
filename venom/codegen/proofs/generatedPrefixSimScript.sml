Theory generatedPrefixSim
Ancestors
  scratchPrefixSim emitInputSim reorderSim allocMono planWf
  planSpillBounds genericInputReady
  stackPlanGen stackPlanOps stackPlanTypes stackModel
  codegenRel asmSem planExec spillSim doSwapSim stackOpSim blockSimHelpers
  list rich_list finite_map arithmetic asmIR sorting regularMemorySim

Theorem do_restore_venom_asm_rel_numeric:
  do_restore op ps = (ops,ps') /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- gvs[do_restore_def, execute_plan_def, asm_steps_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  gvs[do_restore_def, execute_plan_def, exec_stack_op_def] >>
  drule_all restore_op_venom_asm_rel >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists `st'` >> simp[] >>
  irule venom_asm_rel_ps_transfer >>
  qexists `ps with <|ps_stack := stack_push op ps.ps_stack;
    ps_spilled := ps.ps_spilled \\ op|>` >>
  simp[free_spill_slot_def]
QED

Theorem emit_one_input_unspilled_numeric:
  opc <> INVOKE /\
  ~(is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
  emit_one_input opc nl op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> Cases_on `op`
  >- (drule_at (Pat `emit_one_input _ _ _ _ = _`) emit_one_input_sim >>
      simp[is_var_operand_def] >> disch_then drule_all >> simp[]) 
  >- (rename1 `Var v` >> fs[is_var_operand_def] >>
      qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
      simp[emit_one_input_def, is_var_operand_def] >>
      Cases_on `MEM v nl`
      >- (Cases_on `stack_get_depth (Var v) ps.ps_stack`
          >- (simp[] >> strip_tac >>
              gvs[execute_plan_def, asm_steps_def]) >>
          rename1 `stack_get_depth _ _ = SOME dist` >>
          Cases_on `do_dup dist ps` >> simp[] >> strip_tac >> gvs[] >>
          `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
          drule_all do_dup_venom_asm_rel_numeric >>
          disch_then (qspec_then `o2pc` strip_assume_tac) >>
          qexists `st'` >> asm_rewrite_tac[] >>
          MATCH_ACCEPT_TAC ADD_COMM) >>
      simp[] >> strip_tac >> gvs[execute_plan_def, asm_steps_def]) >>
  drule_at (Pat `emit_one_input _ _ _ _ = _`) emit_one_input_sim >>
      simp[is_var_operand_def] >> disch_then drule_all >> simp[]
QED

Theorem emit_one_input_restore_decompose:
  is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op) /\
  do_restore op ps = (rops,ps1) ==>
  emit_one_input opc nl op ps =
    let (sops,ps2) = emit_one_input opc nl op ps1 in (rops ++ sops,ps2)
Proof
  strip_tac >> Cases_on `op` >> gvs[is_var_operand_def] >>
  Cases_on `FLOOKUP ps.ps_spilled (Var s)` >>
  gvs[do_restore_def, emit_one_input_def, is_var_operand_def, LET_THM,
    stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def] >>
  Cases_on `MEM s nl` >> simp[do_dup_def]
QED

Theorem do_restore_layout_wf:
  do_restore op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  strip_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[do_restore_def] >> metis_tac[spill_alloc_layout_wf_after_free]
QED

Theorem do_restore_not_spilled:
  do_restore op ps = (ops,ps') ==> FLOOKUP ps'.ps_spilled op = NONE
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[do_restore_def] >>
  strip_tac >> gvs[]
QED

Theorem emit_one_input_venom_asm_rel_numeric:
  opc <> INVOKE /\
  (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
  emit_one_input opc nl op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (qpat_x_assum `is_var_operand op /\ _` strip_assume_tac >>
      Cases_on `do_restore op ps` >>
      rename1 `do_restore op ps = (rops,ps1)` >>
      Cases_on `emit_one_input opc nl op ps1` >>
      rename1 `emit_one_input opc nl op ps1 = (sops,ps2)` >>
      `ops = rops ++ sops /\ ps' = ps2` by
        (drule_all emit_one_input_restore_decompose >>
         disch_then (qspecl_then [`opc`, `nl`] mp_tac) >> simp[]) >>
      gvs[EVERY_APPEND] >>
      `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled` by
        metis_tac[do_restore_layout_wf] >>
      `FLOOKUP ps1.ps_spilled op = NONE` by metis_tac[do_restore_not_spilled] >>
      qpat_x_assum `asm_block_at _ _ _` mp_tac >>
      simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
      drule_all do_restore_venom_asm_rel_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      rename1 `asm_steps _ _ _ _ st = AsmOK mid` >>
      `asm_block_at prog mid.as_pc (execute_plan initial_fmp sops)` by
        metis_tac[ADD_COMM] >>
      `~(is_var_operand op /\ IS_SOME (FLOOKUP ps1.ps_spilled op))` by simp[] >>
      drule_all emit_one_input_unspilled_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      rename1 `venom_asm_rel lo ps' vs final` >>
      qexists `final` >>
      (conj_tac >- (simp[execute_plan_append] >>
        irule asm_steps_compose_ok >> qexists `mid` >>
        conj_tac >> first_assum ACCEPT_TAC)) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp[execute_plan_append] >> decide_tac) >>
  drule_all emit_one_input_unspilled_numeric >> simp[]
QED

Theorem emit_one_input_unspilled_layout_wf:
  ~(is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_one_input opc nl op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  strip_tac >> Cases_on `op` >> fs[is_var_operand_def]
  >- gvs[emit_one_input_def, is_var_operand_def]
  >- (rename1 `Var v` >>
      qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
      simp[emit_one_input_def, is_var_operand_def] >>
      Cases_on `MEM v nl` >> simp[]
      >- (Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[]
          >- (strip_tac >> gvs[]) >>
          rename1 `stack_get_depth _ _ = SOME dist` >>
          Cases_on `do_dup dist ps` >> simp[] >> strip_tac >> gvs[] >>
          drule do_dup_layout_wf >>
          disch_then (qspec_then `dist` mp_tac) >>
          simp[] >> metis_tac[stack_get_depth_bound]) >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  simp[emit_one_input_def, is_var_operand_def] >>
  Cases_on `opc = INVOKE` >> simp[] >> strip_tac >> gvs[]
QED

Theorem emit_one_input_layout_wf:
  emit_one_input opc nl op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  strip_tac >>
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (qpat_x_assum `is_var_operand op /\ _` strip_assume_tac >>
      Cases_on `do_restore op ps` >>
      rename1 `do_restore op ps = (rops,ps1)` >>
      Cases_on `emit_one_input opc nl op ps1` >>
      rename1 `emit_one_input opc nl op ps1 = (sops,ps2)` >>
      drule_all emit_one_input_restore_decompose >>
      disch_then (qspecl_then [`opc`, `nl`] mp_tac) >> simp[] >> strip_tac >>
      `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled` by
        metis_tac[do_restore_layout_wf] >>
      `FLOOKUP ps1.ps_spilled op = NONE` by metis_tac[do_restore_not_spilled] >>
      irule emit_one_input_unspilled_layout_wf >>
      qexistsl [`nl`, `op`, `opc`, `sops`, `ps1`] >> simp[]) >>
  metis_tac[emit_one_input_unspilled_layout_wf]
QED

Theorem emit_input_plan_venom_asm_rel_numeric:
  !operands ps ops ps' st.
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  emit_input_plan opc operands nl ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct_on `operands`
  >- simp[emit_input_plan_def, execute_plan_def, asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (sops,ps1)` >>
  Cases_on `emit_input_plan opc operands nl ps1` >>
  rename1 `emit_input_plan _ _ _ _ = (rops,ps2)` >>
  `ops = sops ++ rops /\ ps' = ps2` by
    (qpat_x_assum `emit_input_plan _ (_::_) _ _ = _` mp_tac >>
     simp[emit_input_plan_def]) >>
  gvs[EVERY_APPEND] >>
  `!l. h = Label l ==> IS_SOME (FLOOKUP lo l)` by metis_tac[MEM] >>
  `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled` by
    metis_tac[emit_one_input_layout_wf] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all emit_one_input_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps _ _ _ _ st = AsmOK mid` >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp rops)` by
    metis_tac[ADD_COMM] >>
  first_x_assum (qspecl_then [`ps1`, `rops`, `ps'`, `mid`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[MEM])) >> strip_tac >>
  rename1 `venom_asm_rel lo ps' vs final` >>
  qexists `final` >>
  (conj_tac >- (once_rewrite_tac[ADD_COMM] >>
    irule asm_steps_compose_ok >> qexists `mid` >>
    conj_tac >> first_assum ACCEPT_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >> decide_tac
QED

Theorem emit_one_input_unspilled_slots_bounded:
  ~(is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_one_input opc nl op ps = (ops,ps') /\ plan_slots_bounded spill_base ps ==>
  plan_slots_bounded spill_base ps'
Proof
  strip_tac >> Cases_on `op` >> fs[is_var_operand_def]
  >- gvs[emit_one_input_def, is_var_operand_def]
  >- (rename1 `Var v` >>
      qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
      simp[emit_one_input_def, is_var_operand_def] >>
      Cases_on `MEM v nl` >> simp[]
      >- (Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[]
          >- (strip_tac >> gvs[]) >>
          rename1 `stack_get_depth _ _ = SOME dist` >>
          Cases_on `do_dup dist ps` >> simp[] >> strip_tac >> gvs[] >>
          `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
          drule_all do_dup_slots_bounded >> simp[]) >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  simp[emit_one_input_def, is_var_operand_def] >>
  Cases_on `opc = INVOKE` >> simp[] >> strip_tac >> gvs[]
QED

Theorem emit_one_input_slots_bounded:
  emit_one_input opc nl op ps = (ops,ps') /\ plan_slots_bounded spill_base ps ==>
  plan_slots_bounded spill_base ps'
Proof
  strip_tac >>
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (qpat_x_assum `is_var_operand op /\ _` strip_assume_tac >>
      Cases_on `do_restore op ps` >>
      rename1 `do_restore op ps = (rops,ps1)` >>
      Cases_on `emit_one_input opc nl op ps1` >>
      rename1 `emit_one_input opc nl op ps1 = (sops,ps2)` >>
      drule_all emit_one_input_restore_decompose >>
      disch_then (qspecl_then [`opc`, `nl`] mp_tac) >> simp[] >> strip_tac >>
      `plan_slots_bounded spill_base ps1` by metis_tac[do_restore_slots_bounded] >>
      `FLOOKUP ps1.ps_spilled op = NONE` by metis_tac[do_restore_not_spilled] >>
      irule emit_one_input_unspilled_slots_bounded >>
      qexistsl [`nl`, `op`, `opc`, `sops`, `ps1`] >> simp[]) >>
  metis_tac[emit_one_input_unspilled_slots_bounded]
QED

Theorem emit_input_plan_layout_wf:
  !operands ps ops ps'.
  emit_input_plan opc operands nl ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[emit_one_input_layout_wf]
QED

Theorem emit_input_plan_slots_bounded:
  !operands ps ops ps'.
  emit_input_plan opc operands nl ps = (ops,ps') /\ plan_slots_bounded spill_base ps ==>
  plan_slots_bounded spill_base ps'
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[emit_one_input_slots_bounded]
QED

Theorem emit_one_input_available:
  emit_one_input opc nl op ps = (ops,ps') /\
  (MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) ==>
  MEM x ps'.ps_stack \/ x IN FDOM ps'.ps_spilled
Proof
  strip_tac >>
  qspecl_then [`opc`, `nl`, `op`, `ps`, `x`] mp_tac
    emit_one_input_inventory_mono_aux >>
  simp[] >>
  spose_not_then strip_assume_tac >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `x IN FDOM ps.ps_spilled` >> gvs[]
QED

Theorem do_dup_preserves_not_mem:
  !dist ps ops ps' y.
    do_dup dist ps = (ops,ps') /\
    dist < LENGTH ps.ps_stack /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do_dup _ _ = _` mp_tac >>
  simp[do_dup_def, LET_THM] >>
  Cases_on `dist <= 15` >> simp[]
  >- (strip_tac >> gvs[stack_dup_def, listTheory.MEM_SNOC] >>
      `MEM (stack_peek dist ps.ps_stack) ps.ps_stack` by
        simp[stack_peek_def, EL_MEM] >>
      metis_tac[])
  >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     gvs[stack_dup_def, listTheory.MEM_SNOC] >>
     `MEM (stack_peek dist ps.ps_stack) ps.ps_stack` by
       simp[stack_peek_def, EL_MEM] >> metis_tac[]
QED

Theorem do_restore_preserves_not_mem:
  !op ps ops ps' y.
    do_restore op ps = (ops,ps') /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do_restore _ _ = _` mp_tac >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, stack_push_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[finite_mapTheory.flookup_thm]
QED


Theorem emit_one_input_preserves_not_mem:
  !opc nl op ps ops ps' y.
    emit_one_input opc nl op ps = (ops,ps') /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  Cases_on `op` >>
  simp[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def]
  >- (strip_tac >> gvs[])
  >- (Cases_on `FLOOKUP ps.ps_spilled (Var s)` >> simp[]
      >- (Cases_on `MEM s nl` >> simp[] >>
          Cases_on `stack_get_depth (Var s) ps.ps_stack` >> simp[] >>
          rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
          imp_res_tac stack_get_depth_props >>
          metis_tac[do_dup_preserves_not_mem])
      >> rename1 `FLOOKUP ps.ps_spilled (Var s) = SOME off` >>
         Cases_on `do_restore (Var s) ps` >>
         rename1 `do_restore (Var s) ps = (restore_ops,psr)` >>
         `~MEM (Var y) psr.ps_stack /\
          Var y NOTIN FDOM psr.ps_spilled` by
           metis_tac[do_restore_preserves_not_mem] >>
         simp[] >> Cases_on `MEM s nl` >> simp[] >>
         Cases_on `stack_get_depth (Var s) psr.ps_stack` >> simp[] >>
         rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
         imp_res_tac stack_get_depth_props >>
         metis_tac[do_dup_preserves_not_mem])
  >> Cases_on `opc = INVOKE` >> strip_tac >> gvs[]
QED

Theorem emit_input_plan_preserves_not_mem:
  !opc operands nl ps ops ps' y.
    emit_input_plan opc operands nl ps = (ops,ps') /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  gen_tac >> Induct >> simp[emit_input_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum irule >>
  metis_tac[emit_one_input_preserves_not_mem]
QED

Theorem emit_input_plan_available:
  !operands ps ops ps'.
  emit_input_plan opc operands nl ps = (ops,ps') /\
  (MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) ==>
  MEM x ps'.ps_stack \/ x IN FDOM ps'.ps_spilled
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[emit_one_input_available]
QED

Theorem emit_input_plan_output_exclusion:
  emit_input_plan opc operands nl ps = (ops,ps') /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs) ==>
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps'.ps_stack /\
  (!op. op IN FDOM ps'.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs)
Proof
  strip_tac >>
  `!y. MEM y outputs ==>
       ~MEM (Var y) ps.ps_stack /\ Var y NOTIN FDOM ps.ps_spilled` by
    (fs[EVERY_MEM] >> gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `!op. MEM op _ ==> _` (qspec_then `Var y` mp_tac) >>
         simp[] >> metis_tac[]) >>
     qpat_x_assum `!op. op IN FDOM _ ==> _` (qspec_then `Var y` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!y. MEM y outputs ==>
       ~MEM (Var y) ps'.ps_stack /\ Var y NOTIN FDOM ps'.ps_spilled` by
    metis_tac[emit_input_plan_preserves_not_mem] >>
  simp[EVERY_MEM] >> conj_tac >> rpt strip_tac >>
  Cases_on `op` >> gvs[] >> metis_tac[]
QED

Theorem emit_input_plan_prepared_sim:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spill_base ps /\
  residual_budget_wf spill_base [] ps /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
  plan_slots_bounded spill_base ps' /\
  residual_budget_wf spill_base operands ps' /\
  pending_inventory_wf operands ps' /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  conj_tac >- metis_tac[emit_input_plan_layout_wf] >>
  conj_tac >- metis_tac[emit_input_plan_slots_bounded] >>
  conj_tac >- metis_tac[emit_input_plan_residual_budget_nil] >>
  conj_tac >- metis_tac[emit_input_plan_pending_inventory] >>
  irule emit_input_plan_venom_asm_rel_numeric >> simp[] >>
  metis_tac[]
QED

Theorem stack_swap_preserves_not_mem[local]:
  !d stk x.
    d < LENGTH stk /\ ~MEM x stk ==>
    ~MEM x (stack_swap d stk)
Proof
  rpt strip_tac >>
  `0 < LENGTH stk` by decide_tac >>
  `LENGTH stk - 1 < LENGTH stk` by decide_tac >>
  `LENGTH stk - 1 - d < LENGTH stk` by decide_tac >>
  `MEM (EL (LENGTH stk - 1) stk) stk` by simp[EL_MEM] >>
  `MEM (EL (LENGTH stk - 1 - d) stk) stk` by simp[EL_MEM] >>
  gvs[stack_swap_def, LET_THM] >>
  imp_res_tac listTheory.MEM_LUPDATE_E >> gvs[] >>
  imp_res_tac listTheory.MEM_LUPDATE_E >> gvs[]
QED

Theorem do_spill_tos_preserves_not_mem[local]:
  !ps ops ps' y.
    do_spill_tos ps = (ops,ps') /\
    0 < LENGTH ps.ps_stack /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do_spill_tos _ = _` mp_tac >>
  simp[do_spill_tos_def, LET_THM, stack_pop_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac
  >- metis_tac[rich_listTheory.MEM_TAKE]
  >> simp[finite_mapTheory.FDOM_FUPDATE, stack_peek_def] >>
     `MEM (EL (LENGTH ps.ps_stack - 1) ps.ps_stack) ps.ps_stack` by
       simp[EL_MEM] >>
     metis_tac[]
QED

Theorem do_spill_at_preserves_not_mem[local]:
  !d ps ops ps' y.
    do_spill_at d ps = (ops,ps') /\
    d < LENGTH ps.ps_stack /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Cases_on `d = 0`
  >- (gvs[do_spill_at_def] >>
      metis_tac[do_spill_tos_preserves_not_mem])
  >> qpat_x_assum `do_spill_at _ _ = _` mp_tac >>
     simp[do_spill_at_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     `~MEM (Var y) (stack_swap d ps.ps_stack)` by
       metis_tac[stack_swap_preserves_not_mem] >>
     `0 < LENGTH (stack_swap d ps.ps_stack)` by
       simp[stack_swap_def] >>
     qspecl_then
       [`ps with ps_stack := stack_swap d ps.ps_stack`, `spill_ops`, `ps'`, `y`]
       mp_tac do_spill_tos_preserves_not_mem >> simp[]
QED

Theorem reduce_depth_plan_preserves_not_mem[local]:
  !fuel target_ops target_op f target_len ps ops ps' y.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops,ps') /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  Induct_on `fuel`
  >- simp[reduce_depth_plan_def]
  >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `reduce_depth_plan _ _ _ _ _ _ = _` mp_tac >>
     simp[Once reduce_depth_plan_def] >>
     Cases_on `f + 1 < target_len` >> simp[]
     >- (strip_tac >> gvs[])
     >> Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >> simp[]
     >- (strip_tac >> gvs[])
     >> Cases_on `x <= 16` >> simp[]
     >- (strip_tac >> gvs[])
     >> Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >> simp[]
     >- (strip_tac >> gvs[])
     >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac stack_get_unfixed_depth_bound >>
     `1 <= LENGTH ps.ps_stack` by decide_tac >>
     imp_res_tac select_spill_candidate_bound >>
     `~MEM (Var y) ps''.ps_stack /\
      Var y NOTIN FDOM ps''.ps_spilled` by
       (qspecl_then [`x'`, `ps`, `spill_ops`, `ps''`, `y`] mp_tac
          do_spill_at_preserves_not_mem >> simp[]) >>
     metis_tac[]
QED

Theorem do_swap_preserves_not_mem[local]:
  !d ps ops ps' y.
    do_swap d ps = (ops,ps') /\
    d < LENGTH ps.ps_stack /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `(SND (do_swap d ps)).ps_spilled = ps.ps_spilled` by
    (Cases_on `d <= 15`
     >- (Cases_on `d = 0` >> gvs[do_swap_def])
     >> Cases_on `d <= 16`
     >- gvs[do_swap_def]
     >> gvs[do_swap_def, LET_THM] >> rpt (pairarg_tac >> gvs[])) >>
  `~MEM (Var y) (SND (do_swap d ps)).ps_stack` by
    (qspecl_then [`d`, `ps`, `Var y`] mp_tac do_swap_multiplicity >>
     simp[] >> strip_tac >>
     gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
  gvs[]
QED

Theorem stack_poke_preserves_not_mem[local]:
  !d a stk x.
    ~MEM x stk /\ x <> a ==>
    ~MEM x (stack_poke d a stk)
Proof
  rpt strip_tac >>
  gvs[stack_poke_def] >>
  imp_res_tac listTheory.MEM_LUPDATE_E >> gvs[]
QED


Theorem reorder_one_preserves_not_mem_reachable[local]:
  !dfg pending idx op ps ops ps' y.
    reorder_one dfg pending idx op ps = (ops,ps') /\
    idx < LENGTH pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    LENGTH pending <= 17 /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    LENGTH pending <= LENGTH ps'.ps_stack /\
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `~MEM (Var y) ps1.ps_stack /\
   Var y NOTIN FDOM ps1.ps_spilled` by
    (Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops
       ps.ps_stack` >> gvs[]
     >- (Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[]
         >- (qspecl_then [`op`, `ps`, `restore_ops`, `ps1`, `y`] mp_tac
               do_restore_preserves_not_mem >> simp[])
         >> metis_tac[])
     >> metis_tac[]) >>
  `LENGTH pending <= LENGTH ps1.ps_stack` by
    (Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops
       ps.ps_stack` >> gvs[]
     >- (Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
         qspecl_then [`op`, `ps`] mp_tac do_restore_length >> simp[])) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  rename1 `_ = (reduce_ops,ps2)` >>
  `~MEM (Var y) ps2.ps_stack /\
   Var y NOTIN FDOM ps2.ps_spilled` by
    (Cases_on `x > 16` >> gvs[] >>
     metis_tac[reduce_depth_plan_preserves_not_mem]) >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    (Cases_on `x > 16` >> gvs[]
     >- (qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
           `LENGTH pending - (idx + 1)`, `LENGTH pending`, `ps1`,
           `reduce_ops`, `ps2`] mp_tac reduce_depth_plan_length_floor >>
         simp[] >> decide_tac)) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `MEM op ps2.ps_stack` by
    (qpat_assum `stack_peek dist' ps2.ps_stack = op`
       (fn th => rewrite_tac[GSYM th]) >>
     rewrite_tac[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >>
      `MEM (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)
           ps2.ps_stack` by simp[stack_peek_def, EL_MEM] >>
      conj_tac >- simp[stack_poke_def, LENGTH_LUPDATE] >>
      `~MEM (Var y)
         (stack_poke dist'
            (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)
            ps2.ps_stack)` by metis_tac[stack_poke_preserves_not_mem] >>
      metis_tac[stack_poke_preserves_not_mem]) >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 = (swap2_ops,ps4)` >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `~MEM (Var y) ps3.ps_stack /\ Var y NOTIN FDOM ps3.ps_spilled` by
    metis_tac[do_swap_preserves_not_mem] >>
  `~MEM (Var y) ps4.ps_stack /\ Var y NOTIN FDOM ps4.ps_spilled` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`,
       `swap2_ops`, `ps4`, `y`] mp_tac do_swap_preserves_not_mem >> simp[]) >>
  `LENGTH ps4.ps_stack = LENGTH ps3.ps_stack` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`] mp_tac
       do_swap_length >> simp[]) >>
  strip_tac >> gvs[]
QED




Theorem reorder_fold_preserves_not_mem_reachable[local]:
  !work dfg pending acc_ops ps ops ps' y.
    EVERY (\io. FST io < LENGTH pending) work /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    LENGTH pending <= 17 /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled /\
    FOLDL (\(ops,ps) (idx,op).
      let (step_ops,ps') = reorder_one dfg pending idx op ps in
      (ops ++ step_ops,ps')) (acc_ops,ps) work = (ops,ps') ==>
    LENGTH pending <= LENGTH ps'.ps_stack /\
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  Induct
  >- simp[]
  >> rpt gen_tac >> PairCases_on `h` >> simp[LET_THM] >>
     pairarg_tac >> simp[] >> strip_tac >>
     `LENGTH pending <= LENGTH ps''.ps_stack /\
      ~MEM (Var y) ps''.ps_stack /\
      Var y NOTIN FDOM ps''.ps_spilled` by
       metis_tac[reorder_one_preserves_not_mem_reachable] >>
     first_x_assum (qspecl_then
       [`dfg`, `pending`, `acc_ops ++ step_ops`, `ps''`, `ops`, `ps'`, `y`]
       mp_tac) >> simp[]
QED

Theorem reorder_plan_preserves_not_mem_reachable:
  !dfg pending ps ops ps' y.
    reorder_plan dfg pending ps = (ops,ps') /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    LENGTH pending <= 17 /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    LENGTH pending <= LENGTH ps'.ps_stack /\
    ~MEM (Var y) ps'.ps_stack /\
    Var y NOTIN FDOM ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `FOLDL (\(ops,ps) (idx,op).
      let (step_ops,ps') = reorder_one dfg pending idx op ps in
      (ops ++ step_ops,ps')) ([],ps)
      (MAPi (\i op. (i,op)) pending) = (ops,ps')` by
    (qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
     simp[reorder_plan_def]) >>
  `EVERY (\io. FST io < LENGTH pending)
     (MAPi (\i op. (i,op)) pending)` by
    (simp[EVERY_MEM, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[]) >>
  qspecl_then
    [`MAPi (\i op. (i,op)) pending`, `dfg`, `pending`, `[]`, `ps`,
     `ops`, `ps'`, `y`] mp_tac reorder_fold_preserves_not_mem_reachable >>
  simp[]
QED

Theorem reorder_plan_output_exclusion:
  reorder_plan dfg selected ps = (ops,ps') /\
  LENGTH selected <= LENGTH ps.ps_stack /\ LENGTH selected <= 17 /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs) ==>
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps'.ps_stack /\
  (!op. op IN FDOM ps'.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs)
Proof
  strip_tac >>
  `!y. MEM y outputs ==>
       ~MEM (Var y) ps.ps_stack /\ Var y NOTIN FDOM ps.ps_spilled` by
    (fs[EVERY_MEM] >> gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `!op. MEM op _ ==> _` (qspec_then `Var y` mp_tac) >>
         simp[] >> metis_tac[]) >>
     qpat_x_assum `!op. op IN FDOM _ ==> _` (qspec_then `Var y` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!y. MEM y outputs ==>
       ~MEM (Var y) ps'.ps_stack /\ Var y NOTIN FDOM ps'.ps_spilled` by
    metis_tac[reorder_plan_preserves_not_mem_reachable] >>
  simp[EVERY_MEM] >> conj_tac >> rpt strip_tac >>
  Cases_on `op` >> gvs[] >> metis_tac[]
QED

Theorem materialised_emit_resources:
  plan_state_residual_wf spillbase selected (LENGTH selected) ps /\
  LENGTH selected = n /\ LENGTH outputs <= 1 /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs) /\
  emitted = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop n ps.ps_stack) outputs ==>
  plan_slots_bounded spillbase emitted /\
  spill_alloc_layout_wf emitted.ps_alloc emitted.ps_spilled /\
  ALL_DISTINCT emitted.ps_stack /\
  DISJOINT (set emitted.ps_stack) (FDOM emitted.ps_spilled)
Proof
  strip_tac >> drule plan_state_residual_wf_pop >> strip_tac >>
  Cases_on `outputs` >- gvs[] >>
  rename1 `LENGTH (out::rest) <= 1` >>
  `rest = []` by (Cases_on `rest` >> gvs[]) >> gvs[] >>
  `~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
    (fs[EVERY_MEM] >> conj_tac
     >- (qpat_x_assum `!op. MEM op _ ==> _`
           (qspec_then `Var out` mp_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!op. op IN FDOM _ ==> _`
       (qspec_then `Var out` mp_tac) >> simp[] >> metis_tac[]) >>
  gvs[stack_push_def, ALL_DISTINCT_SNOC, plan_slots_bounded_def] >>
  conj_tac >- metis_tac[rich_listTheory.MEM_TAKE, stack_pop_def] >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem materialised_emit_singleton_depth:
  emitted = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop n ps.ps_stack) [out] ==>
  stack_get_depth (Var out) emitted.ps_stack = SOME 0
Proof
  simp[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def]
QED

(* Relocated from genBlockSim for predecessor consumers. *)
Theorem generate_emit_ops_some_name:
  !inst ltc ps name.
    venom_to_evm_name inst.inst_opcode = SOME name ==>
    generate_emit_ops inst ltc ps = ([SOEmit name], ps)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INITIAL_FMP` >> gvs[venom_to_evm_name_def] >>
  Cases_on `inst.inst_opcode = BUMP` >> gvs[venom_to_evm_name_def] >>
  simp[generate_emit_ops_def, LET_THM]
QED

(* Expose the chosen dry-run result, retaining its operand order. *)
Theorem regular_plan_selected_prefix:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  generate_regular_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    (ops, final) ==>
  ?iops prepared selected rops arranged emitted popops popped optops tail.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps =
      (iops, prepared) /\
    reorder_plan dfg selected prepared = (rops, arranged) /\
    (selected = compute_operands inst \/
      (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
       selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
        [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
         EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
    emitted = FOLDL (\st out. st with ps_stack := stack_push (Var out) st.ps_stack)
      (arranged with ps_stack := stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack)
      inst.inst_outputs /\
    (if inst.inst_outputs = [] \/ halting then (popops,popped) = ([],emitted)
     else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs))
       emitted = (popops,popped)) /\
    (if inst.inst_outputs = [] \/ FILTER (\out. MEM out nl) inst.inst_outputs = []
     then (optops,tail) = ([],popped)
     else optimistic_swap_plan dfg inst nl term popped = (optops,tail)) /\
    final = release_dead_spills nl tail /\
    ops = iops ++ rops ++ [SOEmit name] ++ popops ++ optops
Proof
  strip_tac >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> INITIAL_FMP /\
   inst.inst_opcode <> BUMP` by
    (rpt conj_tac >> strip_tac >> gvs[venom_to_evm_name_def]) >>
  `!ltc ps_arg. generate_emit_ops inst ltc ps_arg =
    ([SOEmit name], ps_arg)` by simp[generate_emit_ops_some_name] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `?selected. reorder_plan dfg selected ps1 = (reorder_ops,ps4) /\
    (selected = compute_operands inst \/
      (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
       selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
        [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
         EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]))` by
    (Cases_on `is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst)`
     >- (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >>
         pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
         IF_CASES_TAC >> strip_tac >> gvs[] >> metis_tac[]) >>
     qexists `compute_operands inst` >> gvs[arithmeticTheory.GREATER_EQ]) >>
  pop_assum strip_assume_tac >>
  Cases_on `inst.inst_outputs = []`
  >- (simp[] >> strip_tac >>
      qexists `selected` >> qexists `reorder_ops` >> qexists `ps4` >> simp[]) >>
  simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >>
  qexists `selected` >> qexists `reorder_ops` >> qexists `ps4` >> simp[] >>
  qexists `pop_ops` >> qexists `ps8` >> qexists `opt_ops` >> qexists `ps9` >>
  Cases_on `halting` >> gvs[] >>
  Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >> gvs[]
QED

Theorem regular_plan_selected_perm:
  (selected = operands \/
    (is_commutative opc /\ 2 <= LENGTH operands /\
     selected = TAKE (LENGTH operands - 2) operands ++
       [EL (LENGTH operands - 1) operands; EL (LENGTH operands - 2) operands])) ==>
  PERM operands selected
Proof
  strip_tac >- simp[PERM_REFL] >> gvs[] >>
  irule last_two_reorder_perm >> simp[]
QED

(* PERM_EVERY and PERM_MEM_EQ transport all pointwise operand premises,
   including semantic agreement and marker exclusion, without unfolding
   the commutative candidate in consumers. *)
Theorem selected_input_arranged:
  residual_budget_wf spillbase [] ps /\
  (!op. MEM op operands /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  reorder_plan dfg selected prepared = (rops,arranged) ==>
  plan_state_residual_wf spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected
Proof
  strip_tac >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all emit_input_plan_residual_budget_nil >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule residual_budget_wf_perm >>
  disch_then (qspecl_then [`spillbase`, `prepared`] mp_tac) >> strip_tac >>
  irule reorder_plan_materialised_arranged >>
  conj_tac >- metis_tac[PERM_LENGTH] >>
  qexistsl_tac [`dfg`, `rops`, `prepared`] >>
  fs[] >> metis_tac[PERM_LENGTH]
QED

Theorem regular_prefix_segment_address_bounds:
  ops = iops ++ rops ++ [SOEmit name] ++ post /\
  prefix_spill_wf f lo (FRONT ops) ps ==>
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) iops /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) rops
Proof
  strip_tac >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (irule prefix_spill_wf_front_emit_address_bounds >>
     qexistsl_tac [`f`, `lo`, `name`, `post`, `ps`] >>
     gvs[APPEND_ASSOC]) >> fs[]
QED

Theorem emit_output_fold_stack:
  !outputs ps.
    FOLDL (\st out. st with ps_stack := stack_push (Var out) st.ps_stack) ps outputs =
    ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk) ps.ps_stack outputs
Proof
  Induct >> simp[]
QED

Theorem emit_output_fold_alloc:
  !outputs ps. (FOLDL (\st out.
    st with ps_stack := stack_push (Var out) st.ps_stack) ps outputs).ps_alloc =
    ps.ps_alloc
Proof
  Induct >> simp[]
QED

Theorem regular_postfix_alloc_frame:
  (if outputs = [] \/ halting then (popops,popped) = ([],emitted)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outputs))
      emitted = (popops,popped)) /\
  (if outputs = [] \/ FILTER (\out. MEM out nl) outputs = []
   then (optops,tail) = ([],popped)
   else optimistic_swap_plan dfg inst nl term popped = (optops,tail)) /\
  final = release_dead_spills nl tail ==>
  emitted.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  emitted.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  strip_tac >>
  `emitted.ps_alloc.sa_spill_base = popped.ps_alloc.sa_spill_base /\
   emitted.ps_alloc.sa_next_offset <= popped.ps_alloc.sa_next_offset` by
    (Cases_on `outputs = [] \/ halting` >> gvs[] >>
     metis_tac[popmany_plan_spill_base, popmany_plan_next_offset]) >>
  `popped.ps_alloc.sa_spill_base = tail.ps_alloc.sa_spill_base /\
   popped.ps_alloc.sa_next_offset <= tail.ps_alloc.sa_next_offset` by
    (Cases_on `outputs = [] \/ FILTER (\out. MEM out nl) outputs = []` >> gvs[] >>
     metis_tac[optimistic_swap_plan_spill_base, optimistic_swap_plan_next_offset]) >>
  gvs[release_dead_spills_spill_base, release_dead_spills_next_offset]
QED

Theorem regular_emit_memory_transport:
  emitted.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  emitted.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
  EVERY (\(off,len). len = 0 \/ off + len <= final.ps_alloc.sa_spill_base \/
    final.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
  inst_memory_safe final.ps_alloc inst vs vs' ==>
  EVERY (\(off,len). len = 0 \/ off + len <= emitted.ps_alloc.sa_spill_base \/
    emitted.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
  inst_memory_safe emitted.ps_alloc inst vs vs'
Proof
  strip_tac >> conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >> simp[] >>
      first_x_assum drule >> simp[] >> decide_tac) >>
  irule inst_memory_safe_mono >> qexists `final.ps_alloc` >> simp[]
QED

Theorem regular_prepared_alloc_frame:
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  emitted = FOLDL (\st out. st with ps_stack := stack_push (Var out) st.ps_stack)
    (arranged with ps_stack := stack_pop n arranged.ps_stack) outputs ==>
  ps.ps_alloc.sa_spill_base = prepared.ps_alloc.sa_spill_base /\
  prepared.ps_alloc.sa_spill_base = emitted.ps_alloc.sa_spill_base /\
  ps.ps_alloc.sa_next_offset <= prepared.ps_alloc.sa_next_offset /\
  prepared.ps_alloc.sa_next_offset <= emitted.ps_alloc.sa_next_offset
Proof
  strip_tac >> simp[emit_output_fold_alloc] >>
  metis_tac[emit_input_plan_spill_base, emit_input_plan_next_offset,
    reorder_plan_spill_base, reorder_plan_next_offset]
QED

