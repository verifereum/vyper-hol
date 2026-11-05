(* Checked interface probes for abort-frame preparation. *)
Theory fnFrameTerminalAbort
Ancestors
  fnFrameTerminalPrep generatedPrefixSim planSpillBounds mixedPrefixSim
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst
  asmFrame asmSem codegenRel frameRel contextCodegenRel genBlockSim
  preparedPrefixSim genFrameSim frameViewFacts frameViewMemory
  venomState regularMemorySim venomWf venomEffects asmIR allocMono
  list stackOpSim planExec emitSim blockSimHelpers venomMemProps

(* A transient spill is covered by the output high-water mark even though
   the live spill map is empty again after restoration. *)
Theorem abort_escape_output_allocator_probe:
  !lv dfg cfg fn ih nt lbl.
  (SND (THE (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 REVERT [Var "size"; Lit 32w] [])
    ["size"] ih nt lbl terminal_escape_ps))).ps_alloc.sa_next_offset = 32 /\
  (apply_prefix_ops 0 FEMPTY
    [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1]
    terminal_escape_ps).ps_alloc.sa_next_offset = 32
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem abort_assert_prefix_probe:
  !lv dfg cfg fn ih nt lbl.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 ASSERT [Lit 0w] []) [] ih nt lbl (init_plan_state 0)) =
  SOME [SOPush (Lit 0w); SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem abort_assert_unreachable_prefix_probe:
  !lv dfg cfg fn ih nt lbl.
  ?endlabel.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 ASSERT_UNREACHABLE [Lit 0w] []) [] ih nt lbl
    (init_plan_state 0)) =
  SOME [SOPush (Lit 0w); SOPushLabel endlabel; SOEmit "JUMPI";
        SOEmit "INVALID"; SOLabel endlabel]
Proof
  rpt gen_tac >> qexists `"reachable_1"` >> EVAL_TAC >> simp[]
QED

(* Consume the actual prefix simulation at its allocator boundary.  The
   memory clause already accounts for transient stores, not just live slots. *)
Theorem prepared_local_run_frame_context:
  st.as_stack = top ++ rest /\
  asm_steps lo o2pc prog n (st with as_stack := top) = AsmOK mid /\
  venom_asm_rel lo arranged
    (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
  context_memory_rel cplan vs.vs_memory st.as_memory /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset ==>
  asm_steps lo o2pc prog n st =
    AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
  context_memory_rel cplan vs.vs_memory mid.as_memory
Proof
  strip_tac >> conj_tac
  >- (drule asm_steps_frame >>
      disch_then (qspec_then `rest` mp_tac) >>
      `st with as_stack := top ++ rest = st` by
        simp[asm_state_component_equality] >> simp[]) >>
  irule context_memory_rel_local_prefix >>
  qexistsl [`arranged.ps_alloc`, `st.as_memory`, `r`] >>
  gvs[venom_asm_rel_def]
QED

Theorem selected_prefix_prepared_frame_sim:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := st.as_memory)
    (st with as_stack := top) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) /\
  st.as_stack = top ++ rest /\
  context_memory_rel cplan vs.vs_memory st.as_memory /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset ==>
  plan_state_residual_wf spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?mid.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops))) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged
      (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    context_memory_rel cplan vs.vs_memory mid.as_memory /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  strip_tac >>
  `asm_block_at prog (st with as_stack := top).as_pc
     (execute_plan initial_fmp (iops ++ rops))` by simp[] >>
  drule_all selected_prefix_prepared_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  simp[] >> qexists `st'` >> simp[] >>
  drule_all prepared_local_run_frame_context >> simp[]
QED

Theorem frame_entry_selected_prefix_sim:
  !opc operands lo ps nl iops prepared dfg selected rops arranged spillbase
    fn ra vs cplan ops suffix ctx rest mem0 st prog r final o2pc.
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf spillbase ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  ops = iops ++ rops ++ suffix /\ suffix <> [] /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset ==>
  plan_state_residual_wf spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?mid.
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged
      (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    context_memory_rel cplan vs.vs_memory mid.as_memory /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest)
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (fs[stack_get_depth_def] >> drule stack_find_el >>
         drule planWfTheory.stack_find_bound >>
         metis_tac[MEM_EL, MEM_REVERSE]) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  `residual_budget_wf spillbase [] ps` by
    metis_tac[generated_plan_state_wf_residual_nil] >>
  `plan_slots_bounded spillbase ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_def] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (irule scratchPrefixSimTheory.prefix_spill_wf_address_bounds >>
     qexistsl_tac [`cplan.cp_initial_fmp`, `lo`, `ps`] >>
     irule prefix_spill_wf_front_prefix >> qexists `suffix` >>
     gvs[APPEND_ASSOC]) >>
  `asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     simp[execute_plan_append, asm_block_at_append]) >>
  drule fn_frame_inv_local_state >> strip_tac >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    fs[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at` by
    (simp[] >> metis_tac[]) >>
  drule_all selected_prefix_prepared_frame_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  simp[] >> qexists `mid` >> simp[] >>
  qpat_x_assum `venom_asm_rel lo arranged _ mid` mp_tac >>
  simp[venom_asm_rel_def, venom_asm_terminal_rel_def, frame_view_def]
QED

Theorem abort_operands_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [REVERT; INVALID; ASSERT; ASSERT_UNREACHABLE; CREATE; CREATE2; RETURNDATACOPY] ==>
  eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := m) =
  eval_operands inst.inst_operands vs
Proof
  strip_tac >> irule eval_operands_frame_view >> gen_tac >> disch_tac >>
  irule ordinary_operand_not_retpc >>
  simp[] >> qexists `inst` >> gvs[]
QED

Theorem revert_context_payload_agree:
  inst.inst_opcode = REVERT /\ inst.inst_operands = [off_op; size_op] /\
  eval_operand off_op vs = SOME off /\ eval_operand size_op vs = SOME sz /\
  source_memory_reads_disjoint cplan inst vs /\
  context_memory_rel cplan vs.vs_memory m ==>
  TAKE (w2n sz) (DROP (w2n off) m ++ REPLICATE (w2n sz) 0w) =
  TAKE (w2n sz) (DROP (w2n off) vs.vs_memory ++ REPLICATE (w2n sz) 0w)
Proof
  strip_tac >> irule context_source_payload_agree >>
  qexistsl [`cplan`, `inst`] >>
  simp[source_memory_read_ranges_def, memory_range_of_operands_def]
QED

Theorem terminal_rel_frame_view_stack:
  venom_asm_terminal_rel (frame_view fn ra vs) (st with as_stack := stk) <=>
  venom_asm_terminal_rel vs st
Proof
  simp[venom_asm_terminal_rel_def, frame_view_def]
QED

(* General terminal step: payload agreement is the only memory requirement. *)
Theorem terminal_revert_step_payload:
  asm_block_at prog st.as_pc [AsmOp "REVERT"] /\
  st.as_stack = off :: sz :: tail /\
  venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n off) vs.vs_memory ++ REPLICATE (w2n sz) 0w) =
  TAKE (w2n sz) (DROP (w2n off) st.as_memory ++ REPLICATE (w2n sz) 0w) ==>
  ?out.
    asm_steps lo o2pc prog 1 st = AsmRevert out /\
    venom_asm_terminal_rel
      (revert_state (set_returndata
        (TAKE (w2n sz) (DROP (w2n off) vs.vs_memory ++
          REPLICATE (w2n sz) 0w)) vs)) out
Proof
  strip_tac >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  drule asm_step_revert_eq >>
  disch_then (qspecl_then [`lo`, `o2pc`] assume_tac) >>
  gvs[asm_block_at_def] >>
  gvs[venom_asm_terminal_rel_def, revert_state_def, set_returndata_def] >>
  Cases_on `w2n sz = 0` >>
  gvs[asm_returndata_read_byte, venom_returndata_read_byte]
QED

Theorem gen_inst_revert_frame_sim:
  !inst cplan vs fn r final base ps nl lo ra dfg ops ctx rest mem0 st
    lv cfg halting term label prog fuel a vs' o2pc.
  inst.inst_opcode = REVERT /\
  source_memory_reads_disjoint cplan inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH (SND
    (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n out. a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert out /\
    venom_asm_terminal_rel vs' out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_inst_revert_abort >> strip_tac >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps =
    (ops,final)` by
    gvs[generate_inst_plan_def, is_param_opcode_def] >>
  `venom_to_evm_name inst.inst_opcode = SOME "REVERT"` by
    simp[venom_to_evm_name_def] >>
  drule_all regular_plan_selected_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  gvs[is_commutative_def] >>
  `r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    gvs[release_dead_spills_spill_base, release_dead_spills_next_offset] >>
  suspend "decomposed"
QED

Resume gen_inst_revert_frame_sim[decomposed]:
  rename1 `generated_plan_state_wf spillbase ps` >>
  `asm_block_at prog (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)))
     [AsmOp "REVERT"]` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     simp[execute_plan_append, execute_plan_def, exec_stack_op_def, asm_block_at_append]) >>
  `plan_state_residual_wf spillbase (compute_operands inst)
     (LENGTH (compute_operands inst)) arranged /\
   arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
     compute_operands inst /\
   ?mid. asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
       AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
     venom_asm_rel lo arranged
       (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
     context_memory_rel cplan vs.vs_memory mid.as_memory /\
     mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
     venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest)` by
    (irule frame_entry_selected_prefix_sim >>
     simp[] >> rpt conj_tac
     >- (qexistsl_tac [`arranged`, `r`] >> simp[]) >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
     qexists `[SOEmit "REVERT"]` >>
     simp[sortingTheory.PERM_REFL] >> metis_tac[]) >>
  suspend "prepared"
QED

Resume gen_inst_revert_frame_sim[prepared]:
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := st.as_memory) =
    SOME [off_val; sz_val]` by
    (drule abort_operands_frame_view >> simp[eval_operands_def]) >>
  `mid.as_stack = [off_val; sz_val] ++ DROP (LENGTH inst.inst_operands) mid.as_stack` by
    (irule arranged_eval_operands_stack >>
     conj_tac
     >- (gvs[compute_operands_def, EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     qexists `stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack` >>
     gvs[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
       eval_operand_with_memory] >>
     metis_tac[]) >>
  `TAKE (w2n sz_val) (DROP (w2n off_val) mid.as_memory ++ REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++ REPLICATE (w2n sz_val) 0w)` by
    (irule revert_context_payload_agree >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `?out. asm_steps lo o2pc prog 1 (mid with as_stack := mid.as_stack ++ rest) = AsmRevert out /\
    venom_asm_terminal_rel
      (revert_state (set_returndata
        (TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++ REPLICATE (w2n sz_val) 0w)) vs)) out` by
    (irule terminal_revert_step_payload >>
     simp[] >> conj_tac
     >- (qexists `DROP (LENGTH inst.inst_operands) mid.as_stack ++ rest` >>
         metis_tac[APPEND_ASSOC, APPEND]) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 1`, `out`] >>
  simp[] >> irule asm_steps_compose_revert >> goal_assum (drule_at Any) >> simp[]
QED

Finalise gen_inst_revert_frame_sim

Theorem gen_inst_assert_frame_sim:
  !inst cplan vs fn r final base ps nl lo ra dfg ops ctx rest mem0 st
    lv cfg halting term label prog fuel a vs' o2pc.
  inst.inst_opcode = ASSERT /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH (SND
    (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  (?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword(:256) /\
    FLOOKUP o2pc off = SOME pc /\
    asm_block_at prog pc (execute_plan cplan.cp_initial_fmp revert_postamble)) /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n out. a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert out /\
    venom_asm_terminal_rel vs' out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_inst_assert_abort >> strip_tac >>
  drule_all assert_plan_decompose >> strip_tac >>
  rename1 `reorder_plan dfg [cond] prepared = (rops,arranged)` >>
  rename1 `emit_input_plan ASSERT [cond] nl ps = (iops,prepared)` >>
  suspend "decomposed"
QED

Resume gen_inst_assert_frame_sim[decomposed]:
  rename1 `generated_plan_state_wf spillbase ps` >>
  `asm_block_at prog (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)))
     [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]` by
    (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[execute_plan_append, execute_plan_def, exec_stack_op_def, asm_block_at_append]) >>
  `plan_state_residual_wf spillbase [cond] (LENGTH [cond]) arranged /\
   arranged.ps_stack = stack_pop (LENGTH [cond]) arranged.ps_stack ++ [cond] /\
   ?mid. asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
       AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
     venom_asm_rel lo arranged
       (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
     context_memory_rel cplan vs.vs_memory mid.as_memory /\
     mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
     venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest)` by
    (irule frame_entry_selected_prefix_sim >>
     simp[] >> rpt conj_tac
     >- (qexistsl_tac [`final`, `r`] >>
         gvs[release_dead_spills_spill_base, release_dead_spills_next_offset]) >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
     qexists `[SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]` >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     gvs[sortingTheory.PERM_REFL] >> metis_tac[]) >>
  suspend "prepared"
QED

Resume gen_inst_assert_frame_sim[prepared]:
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := st.as_memory) =
    SOME [0w]` by
    (drule abort_operands_frame_view >> simp[eval_operands_def]) >>
  `mid.as_stack = [0w] ++ DROP (LENGTH inst.inst_operands) mid.as_stack` by
    (irule arranged_eval_operands_stack >>
     conj_tac
     >- (gvs[compute_operands_def, EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     qexists `stack_pop 1 arranged.ps_stack` >>
     gvs[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
       eval_operand_with_memory] >> metis_tac[]) >>
  `?out. asm_steps lo o2pc prog 7 (mid with as_stack := mid.as_stack ++ rest) = AsmRevert out /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) out` by
    (irule asm_assert_zero_revert >>
     simp[] >> rpt conj_tac
     >- (qexists `DROP (LENGTH inst.inst_operands) mid.as_stack ++ rest` >>
         metis_tac[APPEND, APPEND_ASSOC])
     >- (qexists `cplan.cp_initial_fmp` >> simp[]) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 7`, `out`] >>
  simp[] >> irule asm_steps_compose_revert >> goal_assum (drule_at Any) >> simp[]
QED

Finalise gen_inst_assert_frame_sim

Theorem gen_inst_assert_unreachable_frame_sim:
  !inst cplan vs fn r final base ps nl lo ra dfg ops ctx rest mem0 st
    lv cfg halting term label prog fuel a vs' o2pc.
  inst.inst_opcode = ASSERT_UNREACHABLE /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH (SND
    (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  (!lbl i. i < LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    EL i (execute_plan cplan.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword(:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n out. a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault out /\
    venom_asm_terminal_rel vs' out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_inst_assert_unreachable_abort >> strip_tac >>
  drule_all assert_unreachable_plan_decompose >> strip_tac >>
  rename1 `reorder_plan dfg [cond] prepared = (rops,arranged)` >>
  rename1 `emit_input_plan ASSERT_UNREACHABLE [cond] nl ps = (iops,prepared)` >>
  rename1 `fresh_label "reachable" _ = (endlabel,after)` >>
  `after.ps_alloc = arranged.ps_alloc` by
    gvs[fresh_label_def, plan_state_component_equality] >>
  suspend "decomposed"
QED

Resume gen_inst_assert_unreachable_frame_sim[decomposed]:
  rename1 `generated_plan_state_wf spillbase ps` >>
  `asm_block_at prog (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)))
     [AsmPushLabel endlabel; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel endlabel]` by
    (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[execute_plan_append, execute_plan_def, exec_stack_op_def, asm_block_at_append]) >>
  `?off. FLOOKUP lo endlabel = SOME off` by
    (qpat_x_assum `!lbl i. _` (qspecl_then [`endlabel`,
       `LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3`] mp_tac) >>
     simp[execute_plan_append, execute_plan_def, exec_stack_op_def, EL_APPEND_EQN,
       LENGTH_APPEND, APPEND_ASSOC] >> metis_tac[]) >>
  `plan_state_residual_wf spillbase [cond] (LENGTH [cond]) arranged /\
   arranged.ps_stack = stack_pop (LENGTH [cond]) arranged.ps_stack ++ [cond] /\
   ?mid. asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
       AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
     venom_asm_rel lo arranged
       (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
     context_memory_rel cplan vs.vs_memory mid.as_memory /\
     mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
     venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest)` by
    (irule frame_entry_selected_prefix_sim >>
     simp[] >> rpt conj_tac
     >- (qexistsl_tac [`final`, `r`] >>
         gvs[release_dead_spills_spill_base, release_dead_spills_next_offset]) >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
     qexists `[SOPushLabel endlabel; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel endlabel]` >>
     gvs[sortingTheory.PERM_REFL] >> metis_tac[]) >>
  suspend "prepared"
QED

Resume gen_inst_assert_unreachable_frame_sim[prepared]:
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := st.as_memory) =
    SOME [0w]` by
    (drule abort_operands_frame_view >> simp[eval_operands_def]) >>
  `mid.as_stack = [0w] ++ DROP (LENGTH inst.inst_operands) mid.as_stack` by
    (irule arranged_eval_operands_stack >>
     conj_tac
     >- (gvs[compute_operands_def, EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     qexists `stack_pop 1 arranged.ps_stack` >>
     gvs[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
       eval_operand_with_memory] >> metis_tac[]) >>
  `?out. asm_steps lo o2pc prog 3 (mid with as_stack := mid.as_stack ++ rest) = AsmFault out /\
    venom_asm_terminal_rel (vs with <|vs_returndata := []; vs_halted := T|>) out` by
    (irule terminal_pushlabel_jumpi_invalid >>
     simp[] >> conj_tac
     >- (qexists `DROP (LENGTH inst.inst_operands) mid.as_stack ++ rest` >>
         metis_tac[APPEND, APPEND_ASSOC]) >>
     qexistsl_tac [`endlabel`, `off`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3`, `out`] >>
  simp[halt_state_def, set_returndata_def] >>
  irule asm_steps_compose_fault >> goal_assum (drule_at Any) >> simp[]
QED

Finalise gen_inst_assert_unreachable_frame_sim

Theorem gen_inst_invalid_frame_sim:
  !inst cplan vs fn r final base ps nl lo ra dfg ops ctx rest mem0 st
    lv cfg halting term label prog fuel a vs' o2pc.
  inst.inst_opcode = INVALID /\ inst_wf inst /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH (SND
    (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n out. a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault out /\
    venom_asm_terminal_rel vs' out
Proof
  rpt gen_tac >> strip_tac >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def] >>
     `~is_pre_codegen_opcode INVALID /\ ~is_param_opcode INVALID` by EVAL_TAC >> simp[]) >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `a = ExHalt_abort /\ vs' = halt_state (set_returndata [] vs)` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once venomExecSemanticsTheory.step_inst_def, is_terminator_def] >>
     simp[Once venomExecSemanticsTheory.step_inst_base_def]) >>
  `?iops prepared rops arranged.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "INVALID"] /\
    final = release_dead_spills nl
      (arranged with ps_stack := stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack)` by
    (qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_regular_inst_plan_def, is_commutative_def,
       generate_emit_ops_def, venom_to_evm_name_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >> metis_tac[]) >>
  suspend "decomposed"
QED

Resume gen_inst_invalid_frame_sim[decomposed]:
  rename1 `generated_plan_state_wf spillbase ps` >>
  `asm_block_at prog (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)))
     [AsmOp "INVALID"]` by
    (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     once_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[execute_plan_append, execute_plan_def, exec_stack_op_def, asm_block_at_append]) >>
  `plan_state_residual_wf spillbase (compute_operands inst)
       (LENGTH (compute_operands inst)) arranged /\
   arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
   ?mid. asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
       AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
     venom_asm_rel lo arranged
       (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
     context_memory_rel cplan vs.vs_memory mid.as_memory /\
     mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
     venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest)` by
    (irule frame_entry_selected_prefix_sim >>
     simp[] >> rpt conj_tac
     >- (qexistsl_tac [`final`, `r`] >>
         gvs[release_dead_spills_spill_base, release_dead_spills_next_offset]) >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
     qexists `[SOEmit "INVALID"]` >>
     gvs[sortingTheory.PERM_REFL] >> metis_tac[]) >>
  `?out. asm_steps lo o2pc prog 1 (mid with as_stack := mid.as_stack ++ rest) = AsmFault out /\
    venom_asm_terminal_rel (vs with <|vs_returndata := []; vs_halted := T|>) out` by
    (irule terminal_invalid_step >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 1`, `out`] >>
  simp[halt_state_def, set_returndata_def] >>
  irule asm_steps_compose_fault >> goal_assum (drule_at Any) >> simp[]
QED

Finalise gen_inst_invalid_frame_sim

(* Regular single-output fault opcodes share one preparation boundary. *)
Theorem regular_abort_frame_prefix:
  !inst name lv dfg cfg fn nl halting term label ps ops final lo
    cplan r base ctx ra rest mem0 vs st prog o2pc.
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
  LENGTH inst.inst_outputs <= 1 /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops, final) /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH (SND
    (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) ==>
  ?pre arranged mid.
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    asm_block_at prog mid.as_pc [AsmOp name]
Proof
  rpt gen_tac >> strip_tac >>
  drule_all regular_plan_selected_prefix >> strip_tac >>
  `selected = compute_operands inst` by metis_tac[] >>
  `arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by
    (`emitted.ps_alloc = arranged.ps_alloc` by simp[emit_output_fold_alloc] >>
     `emitted.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
      emitted.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by
       (irule regular_postfix_alloc_frame >>
        goal_assum (drule_at (Pat `final = release_dead_spills _ _`)) >>
        goal_assum (drule_at (Pat `if _ then _ else optimistic_swap_plan _ _ _ _ _ = _`)) >>
        goal_assum (drule_at (Pat `if _ then _ else popmany_plan _ _ = _`)) >> gvs[]) >>
     metis_tac[]) >>
  suspend "decomposed"
QED

Resume regular_abort_frame_prefix[decomposed]:
  qpat_x_assum `selected = _` SUBST_ALL_TAC >>
  rename1 `generated_plan_state_wf spillbase ps` >>
  `plan_state_residual_wf spillbase (compute_operands inst)
       (LENGTH (compute_operands inst)) arranged /\
   arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
   ?mid. asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
       AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
     venom_asm_rel lo arranged
       (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
     context_memory_rel cplan vs.vs_memory mid.as_memory /\
     mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
     venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest)` by
    (irule frame_entry_selected_prefix_sim >>
     simp[] >> rpt conj_tac
     >- (qexistsl_tac [`final`, `r`] >> gvs[]) >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
     qexists `[SOEmit name] ++ popops ++ optops` >>
     gvs[sortingTheory.PERM_REFL, APPEND_ASSOC] >> metis_tac[]) >>
  qexistsl_tac [`iops ++ rops`, `arranged`, `mid`] >> simp[] >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, execute_plan_append, asm_block_at_append] >>
  simp[execute_plan_def, exec_stack_op_def]
QED

Finalise regular_abort_frame_prefix

Theorem abort_frame_arranged_stack:
  inst_wf inst /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ 
  MEM inst.inst_opcode
    [REVERT; INVALID; ASSERT; ASSERT_UNREACHABLE; CREATE; CREATE2; RETURNDATACOPY] /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
    compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  eval_operands inst.inst_operands vs = SOME vals ==>
  mid.as_stack = vals ++ DROP (LENGTH inst.inst_operands) mid.as_stack
Proof
  strip_tac >>
  `eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := m) = SOME vals` by
    (drule_all abort_operands_frame_view >> simp[]) >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := m) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `compute_operands inst = REVERSE inst.inst_operands` by
    (Cases_on `inst.inst_operands` >>
     gvs[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
       inst_wf_def] >>
     rename1 `LENGTH t` >> Cases_on `t` >> gvs[]) >>
  irule arranged_eval_operands_stack >> conj_tac
  >- (gvs[EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
  goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  qexists `stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack` >>
  gvs[MEM_REVERSE, eval_operand_with_memory] >> metis_tac[]
QED

Theorem gen_inst_ext_fault_frame_sim:
  !inst cplan vs fn r final base ps nl lo ra dfg ops ctx rest mem0 st
    lv cfg halting term label prog fuel a vs' o2pc.
  MEM inst.inst_opcode [CREATE; CREATE2; RETURNDATACOPY] /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH (SND
    (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  ~vs.vs_call_ctx.cc_static /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n out. a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault out /\
    venom_asm_terminal_rel vs' out
Proof
  rpt gen_tac >> strip_tac >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name` by
    (gvs[venom_to_evm_name_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
   LENGTH inst.inst_outputs <= 1` by gvs[inst_wf_def, is_commutative_def] >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
       is_unlowered_fmp_opcode_def, is_raw_fmp_opcode_def,
       is_unlowered_internal_call_opcode_def]) >>
  drule_all regular_abort_frame_prefix >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `?out. a = ExHalt_abort /\
    asm_steps lo o2pc prog 1 (mid with as_stack := mid.as_stack ++ rest) = AsmFault out /\
    venom_asm_terminal_rel vs' out` by
    (Cases_on `inst.inst_opcode = CREATE` >- suspend "create" >>
     Cases_on `inst.inst_opcode = CREATE2` >- suspend "create2" >>
     suspend "returndatacopy") >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp pre) + 1`, `out`] >>
  simp[] >> irule asm_steps_compose_fault >> goal_assum (drule_at Any) >> simp[]
QED

Resume gen_inst_ext_fault_frame_sim[create]:
  drule_all step_inst_create_abort >> strip_tac >>
  `mid.as_stack = [value; offset; sz] ++ DROP (LENGTH inst.inst_operands) mid.as_stack` by
    (irule abort_frame_arranged_stack >> simp[] >> conj_tac
     >- (qexists `dfg` >> gvs[]) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     gvs[eval_operands_def] >> metis_tac[]) >>
  `name = "CREATE"` by gvs[venom_to_evm_name_def] >>
  simp[] >> irule terminal_create_fault_step >> simp[] >>
  conj_tac
  >- (qpat_x_assum `mid.as_stack = _` (fn th => once_rewrite_tac[th]) >>
      simp[APPEND_ASSOC]) >> gvs[]
QED

Resume gen_inst_ext_fault_frame_sim[create2]:
  drule_all step_inst_create2_abort >> strip_tac >>
  `mid.as_stack = [value; offset; sz; salt] ++ DROP (LENGTH inst.inst_operands) mid.as_stack` by
    (irule abort_frame_arranged_stack >> simp[] >> conj_tac
     >- (qexists `dfg` >> gvs[]) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     gvs[eval_operands_def] >> metis_tac[]) >>
  `name = "CREATE2"` by gvs[venom_to_evm_name_def] >>
  simp[] >> irule terminal_create2_fault_step >> simp[] >>
  conj_tac
  >- (qpat_x_assum `mid.as_stack = _` (fn th => once_rewrite_tac[th]) >>
      simp[APPEND_ASSOC]) >> gvs[]
QED

Resume gen_inst_ext_fault_frame_sim[returndatacopy]:
  `inst.inst_opcode = RETURNDATACOPY` by gvs[] >>
  drule_all step_inst_returndatacopy_abort >> strip_tac >>
  `mid.as_stack = [dest_val; src_val; sz_val] ++ DROP (LENGTH inst.inst_operands) mid.as_stack` by
    (irule abort_frame_arranged_stack >> simp[] >> conj_tac
     >- (qexists `dfg` >> gvs[]) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     gvs[eval_operands_def] >> metis_tac[]) >>
  `name = "RETURNDATACOPY"` by gvs[venom_to_evm_name_def] >>
  simp[] >> irule terminal_returndatacopy_fault_step >> simp[] >>
  conj_tac
  >- (qpat_x_assum `mid.as_stack = _` (fn th => once_rewrite_tac[th]) >>
      simp[APPEND_ASSOC]) >> gvs[]
QED

Finalise gen_inst_ext_fault_frame_sim
