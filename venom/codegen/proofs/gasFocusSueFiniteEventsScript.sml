Theory gasFocusSueFiniteEvents
Ancestors o1ContractSue[qualified]
  singleUseExpansionSupplySim gasEvents o1PassLift
  singleUseExpansionSupplyProofs singleUseExpansionDefs irSupply
  stateFrame stateEquiv venomExecProps venomExecProofs
  venomExecSemantics venomWf venomInst venomState
  analysisSimDefs instIdxIndep execEquivParamProofs passSharedSubst
  venomFnScheduleRunner ctxLookupAgreeHelpers cfgWf contextCodegenRelProps
  venomWfProps

Theorem sue_assign_prefix_gas_events[local]:
  !assigns k bb tail t u.
  EVERY (\a. a.inst_opcode = ASSIGN) assigns /\
  DROP k bb.bb_instructions = assigns ++ tail /\
  run_insts fuel ctx assigns t = OK u ==>
  gas_events_block fuel ctx owner bb (t with vs_inst_idx := k) =
  gas_events_block fuel ctx owner bb (u with vs_inst_idx := k + LENGTH assigns)
Proof
  Induct >> rpt gen_tac
  >- simp[run_insts_def] >>
  strip_tac >> fs[] >>
  `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = h /\
   DROP (SUC k) bb.bb_instructions = assigns ++ tail` by
    (`k < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP k _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
        simp[listTheory.LENGTH_DROP]) >>
     fs[rich_listTheory.DROP_CONS_EL]) >>
  `step_inst fuel ctx h (t with vs_inst_idx := k) =
   exec_result_map (\u. u with vs_inst_idx := k) (step_inst fuel ctx h t)` by
    (simp[Once step_inst_def] >> simp[Once step_inst_def] >>
     irule step_inst_inst_idx_indep >> simp[is_terminator_def]) >>
  Cases_on `step_inst fuel ctx h t` >> gvs[run_insts_def] >>
  simp[Once gas_events_block_def, get_instruction_def, gas_events_step_def,
       is_terminator_def, exec_result_map_def] >>
  first_x_assum (qspec_then `SUC k` mp_tac) >>
  pure_rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
  disch_then irule >> simp[]
QED

Theorem sue_rewritten_gas_events_step[local]:
  inst_wf inst /\ execution_frame s = execution_frame t /\
  LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
    inst.inst_operands ops /\
  (!i. i < LENGTH inst.inst_operands ==>
    !lbl. EL i inst.inst_operands = Label lbl ==> EL i ops = Label lbl) ==>
  gas_events_step fuel ctx owner (inst with inst_operands := ops) t =
  gas_events_step fuel ctx owner inst s
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[inst_wf_def] >>
      `newop = Label lbl` by
        (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[decode_invoke_def] >>
      drule o1ContractSueTheory.sue_eval_operands_related >> strip_tac >>
      `!callee args. setup_callee callee args t = setup_callee callee args s` by
        (rpt gen_tac >> irule setup_callee_execution_frame >> simp[]) >>
      simp[gas_events_step_def, decode_invoke_def]) >>
  simp[gas_events_step_def]
QED

Theorem sue_preserved_gas_events_step[local]:
  sue_state_rel P s t /\ inst_wf inst /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN P) ==>
  gas_events_step fuel ctx owner inst t = gas_events_step fuel ctx owner inst s
Proof
  strip_tac >>
  `gas_events_step fuel ctx owner (inst with inst_operands := inst.inst_operands) t =
   gas_events_step fuel ctx owner inst s` suffices_by simp[] >>
  irule sue_rewritten_gas_events_step >> fs[sue_state_rel_def] >>
  simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule sue_state_rel_eval_operand >> qexists_tac `P` >>
  simp[sue_state_rel_def] >> metis_tac[listTheory.MEM_EL]
QED

Theorem sue_segment_indexed_gas_events[local]:
  ir_supply_inst_ok supply /\ P SUBSET set supply.irs_used_vars /\
  sue_segments_supply dfg supply bb.bb_instructions = (segs,supply') /\
  i < LENGTH bb.bb_instructions /\ bb' = bb with bb_instructions := FLAT segs /\
  inst = EL i bb.bb_instructions /\ inst_wf inst /\ ~is_alloca_op inst.inst_opcode /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN P) /\
  (~sue_should_skip inst.inst_opcode ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars) /\
  sue_state_rel P s t /\ t.vs_inst_idx = sue_segment_offset segs i ==>
  ?k u inst'.
    gas_events_block fuel ctx owner bb' t = gas_events_block fuel ctx owner bb' u /\
    gas_events_step fuel ctx owner inst' u = gas_events_step fuel ctx owner inst s /\
    u.vs_inst_idx = k /\ k < LENGTH bb'.bb_instructions /\
    EL k bb'.bb_instructions = inst' /\ inst'.inst_opcode = inst.inst_opcode /\
    SUC k = sue_segment_offset segs (SUC i) /\
    sue_result_rel P (step_inst fuel ctx inst s) (step_inst fuel ctx inst' u)
Proof
  strip_tac >> drule_all sue_segments_supply_index_ready >> strip_tac >>
  `i < LENGTH segs` by metis_tac[sue_segments_supply_length] >>
  drule sue_segment_offset_drop >> strip_tac >>
  drule sue_segment_offset_suc >> strip_tac >>
  Cases_on `sue_should_skip inst.inst_opcode`
  >- suspend "skip" >>
  Cases_on `sue_expand_ops_supply dfg inst si inst.inst_operands 0` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst si inst.inst_operands 0 = (assigns,ops,sj')` >>
  `EL i segs = assigns ++ [inst with inst_operands := ops]` by
    gvs[sue_expand_inst_supply_def] >>
  `!a v. MEM a assigns /\ a.inst_operands = [Var v] ==> v IN FDOM s.vs_vars` by
    (drule sue_expand_ops_supply_copy_sources >>
     simp[listTheory.EVERY_MEM] >> metis_tac[listTheory.CONS_11]) >>
  drule_all sue_expand_ops_supply_step_sim >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  suspend "expanded"
QED

Resume sue_segment_indexed_gas_events[skip]:
  `EL i segs = [inst]` by metis_tac[sue_expand_inst_supply_skip, pairTheory.PAIR_EQ] >>
  `sue_segment_offset segs i < LENGTH (FLAT segs) /\
   EL (sue_segment_offset segs i) (FLAT segs) = inst` by
    (fs[] >>
     `sue_segment_offset segs i < LENGTH (FLAT segs)` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
        simp[listTheory.LENGTH_DROP]) >>
     fs[rich_listTheory.DROP_CONS_EL]) >>
  qexistsl [`sue_segment_offset segs i`, `t`, `inst`] >> simp[] >>
  conj_tac >- (irule sue_preserved_gas_events_step >> simp[] >> metis_tac[]) >>
  irule sue_step_inst_preserves >> simp[] >> metis_tac[]
QED

Resume sue_segment_indexed_gas_events[expanded]:
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    (drule_all sue_expand_ops_supply_prefix >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `DROP (sue_segment_offset segs i) bb'.bb_instructions =
    assigns ++ (inst with inst_operands := ops)::FLAT (DROP (SUC i) segs)` by
    (simp[] >> pure_asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  `t with vs_inst_idx := sue_segment_offset segs i = t` by
    (qpat_x_assum `t.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all sue_assign_prefix_gas_events >>
  disch_then (qspec_then `owner` assume_tac) >>
  `sue_segment_offset segs i + LENGTH assigns < LENGTH bb'.bb_instructions /\
    EL (sue_segment_offset segs i + LENGTH assigns) bb'.bb_instructions =
      inst with inst_operands := ops` by
    (drule singleUseExpansionSupplySimTheory.sue_drop_prefix_index >> simp[]) >>
  qexistsl [`sue_segment_offset segs i + LENGTH assigns`,
    `u with vs_inst_idx := sue_segment_offset segs i + LENGTH assigns`,
    `inst with inst_operands := ops`] >>
  simp[] >> suspend "end"
QED

Resume sue_segment_indexed_gas_events[end]:
  conj_tac
  >- (qpat_x_assum `gas_events_block _ _ _ _ _ = _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  reverse conj_tac
  >- (qpat_x_assum `sue_result_rel _ _ _` mp_tac >>
      once_rewrite_tac[GSYM (Q.INST [`n` |-> `0`, `m` |-> `0`] sue_result_rel_idx)] >>
      pure_rewrite_tac[sue_step_inst_idx_norm] >> simp[]) >>
  drule_all sue_expand_ops_supply_eval >> strip_tac >>
  drule sue_expand_ops_supply_structure >> strip_tac >>
  irule sue_rewritten_gas_events_step >>
  gvs[sue_state_rel_def, execution_frame_def, eval_op_inst_idx]
QED

Finalise sue_segment_indexed_gas_events

Theorem sue_block_supply_gas_events:
  !i s t.
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_inst_ok supply /\ set (fn_ir_vars fn) SUBSET set supply.irs_used_vars /\
  sue_segments_supply (dfg_build_function fn) supply bb.bb_instructions = (segs,supply') /\
  bb' = bb with bb_instructions := FLAT segs /\
  phi_prefix_length bb.bb_instructions <= i /\ i <= LENGTH bb.bb_instructions /\
  s.vs_inst_idx = i /\ t.vs_inst_idx = sue_segment_offset segs i /\
  sue_boundary_defined fn bb i s /\ sue_state_rel (set (fn_ir_vars fn)) s t ==>
  gas_events_block fuel ctx owner bb' t = gas_events_block fuel ctx owner bb s
Proof
  measureInduct_on `LENGTH bb.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH bb.bb_instructions`
  >- (`LENGTH segs = LENGTH bb.bb_instructions` by metis_tac[sue_segments_supply_length] >>
      `sue_segment_offset segs i = LENGTH (FLAT segs)` by metis_tac[sue_segment_offset_end] >>
      gvs[] >> simp[Once gas_events_block_def, get_instruction_def] >>
      simp[Once gas_events_block_def, get_instruction_def]) >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `inst_wf (EL i bb.bb_instructions)` by metis_tac[listTheory.EVERY_EL] >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
       v IN set (fn_ir_vars fn)` by metis_tac[sue_original_operand_covered, listTheory.MEM_EL] >>
  `(EL i bb.bb_instructions).inst_opcode <> PHI` by metis_tac[sue_phi_suffix_nonphi] >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==> v IN FDOM s.vs_vars` by
    metis_tac[sue_boundary_operand_defined] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (`!bbs. MEM bb bbs ==> MEM (EL i bb.bb_instructions) (fn_insts_blocks bbs)` by
       (Induct >> simp[fn_insts_blocks_def] >> metis_tac[listTheory.MEM_EL]) >>
     simp[fn_insts_def]) >>
  `(EL i bb.bb_instructions).inst_opcode <> ALLOCA` by
    (qpat_x_assum `EVERY (\inst. inst.inst_opcode <> ALLOCA) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> disch_then drule >> simp[]) >>
  `~is_alloca_op (EL i bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `(EL i bb.bb_instructions).inst_opcode <> ALLOCA` mp_tac >>
     Cases_on `(EL i bb.bb_instructions).inst_opcode` >> simp[is_alloca_op_def]) >>
  `?k u inst'.
    gas_events_block fuel ctx owner bb' t = gas_events_block fuel ctx owner bb' u /\
    gas_events_step fuel ctx owner inst' u =
      gas_events_step fuel ctx owner (EL i bb.bb_instructions) s /\
    u.vs_inst_idx = k /\ k < LENGTH bb'.bb_instructions /\
    EL k bb'.bb_instructions = inst' /\
    inst'.inst_opcode = (EL i bb.bb_instructions).inst_opcode /\
    SUC k = sue_segment_offset segs (SUC i) /\
    sue_result_rel (set (fn_ir_vars fn))
      (step_inst fuel ctx (EL i bb.bb_instructions) s) (step_inst fuel ctx inst' u)` by
    (irule sue_segment_indexed_gas_events >> simp[] >> metis_tac[]) >>
  suspend "step"
QED

Resume sue_block_supply_gas_events[step]:
  qpat_x_assum `gas_events_block _ _ _ bb' t = _` SUBST1_TAC >>
  `get_instruction bb s.vs_inst_idx = SOME (EL i bb.bb_instructions)` by
    simp[get_instruction_def] >>
  `get_instruction bb' u.vs_inst_idx = SOME inst'` by gvs[get_instruction_def] >>
  once_rewrite_tac[gas_events_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx (EL i bb.bb_instructions) s` >>
  Cases_on `step_inst fuel ctx inst' u` >>
  fs[sue_result_rel_def, lift_result_def] >>
  rename1 `sue_state_rel (set (fn_ir_vars fn)) v v'` >>
  Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> simp[] >>
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `sue_boundary_defined fn bb (SUC i) (v with vs_inst_idx := SUC i)` by
    (irule sue_boundary_defined_step >> simp[] >> metis_tac[]) >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`v with vs_inst_idx := SUC i`,
    `v' with vs_inst_idx := sue_segment_offset segs (SUC i)`] mp_tac) >>
  simp[]
QED

Finalise sue_block_supply_gas_events

Theorem sue_function_supply_gas_events:
  !fuel st tt.
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  fn_reachable fn st.vs_current_bb /\ strict_dom_vars_defined fn st /\
  sue_state_rel (set (fn_ir_vars fn)) st tt ==>
  gas_events_blocks fuel ctx fn' tt = gas_events_blocks fuel ctx fn st
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (pure_once_rewrite_tac[gas_events_blocks_def] >> simp[]) >>
  `tt.vs_current_bb = st.vs_current_bb` by fs[sue_state_rel_def] >>
  Cases_on `lookup_block st.vs_current_bb fn.fn_blocks`
  >- (`lookup_block st.vs_current_bb fn'.fn_blocks = NONE` by
        (Cases_on `lookup_block st.vs_current_bb fn'.fn_blocks` >> simp[] >>
         drule_all sue_function_lookup_ready_back >> simp[]) >>
      pure_once_rewrite_tac[gas_events_blocks_def] >> simp[]) >>
  rename1 `lookup_block st.vs_current_bb fn.fn_blocks = SOME bb` >>
  drule_all sue_function_lookup_ready >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = st.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
      !v. MEM (Var v) inst.inst_operands ==> v IN set (fn_ir_vars fn)) bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> metis_tac[sue_original_operand_covered]) >>
  `sue_result_rel (set (fn_ir_vars fn))
     (eval_phis st bb.bb_instructions) (eval_phis tt (FLAT segs))` by
    (irule sue_expanded_phi_entry >> simp[] >> metis_tac[]) >>
  `phi_prefix_length (FLAT segs) = phi_prefix_length bb.bb_instructions` by
    (drule sue_segments_supply_flat >> strip_tac >>
     drule_all sue_expand_insts_supply_phis >> simp[]) >>
  `sue_segment_offset segs (phi_prefix_length bb.bb_instructions) =
    phi_prefix_length bb.bb_instructions` by metis_tac[sue_segments_phi_offset] >>
  pure_once_rewrite_tac[gas_events_blocks_def] >> simp[] >>
  Cases_on `eval_phis st bb.bb_instructions` >>
  Cases_on `eval_phis tt (FLAT segs)` >>
  gvs[sue_result_rel_def, lift_result_def] >>
  suspend "block"
QED

Resume sue_function_supply_gas_events[block]:
  `sue_boundary_defined fn bb (phi_prefix_length bb.bb_instructions)
    (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[sue_boundary_defined_phis] >>
  `v.vs_current_bb = st.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `fn'.fn_name = fn.fn_name` by metis_tac[sue_expand_function_supply_identity] >>
  `gas_events_block fuel ctx fn'.fn_name (bb with bb_instructions := FLAT segs)
    (v' with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
   gas_events_block fuel ctx fn.fn_name bb
    (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[] >> irule sue_block_supply_gas_events >> simp[phi_prefix_length_le] >> metis_tac[]) >>
  `sue_result_rel (set (fn_ir_vars fn))
    (exec_block fuel ctx bb (v with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    (exec_block fuel ctx (bb with bb_instructions := FLAT segs)
      (v' with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (irule sue_exec_block_supply_sim >> simp[phi_prefix_length_le] >> metis_tac[]) >>
  Cases_on `exec_block fuel ctx bb
    (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  Cases_on `exec_block fuel ctx (bb with bb_instructions := FLAT segs)
    (v' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[sue_result_rel_def, lift_result_def] >>
  suspend "exit"
QED

Resume sue_function_supply_gas_events[exit]:
  rename1 `sue_state_rel (set (fn_ir_vars fn)) src dst` >>
  `src.vs_halted = dst.vs_halted` by
    (fs[sue_state_rel_def] >>
     qpat_x_assum `execution_frame src = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  Cases_on `src.vs_halted` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  irule sue_exec_block_defined_exit >> simp[] >>
  qexistsl [`bb`, `ctx`, `fuel`,
    `v with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[phi_prefix_length_le]
QED

Finalise sue_function_supply_gas_events
