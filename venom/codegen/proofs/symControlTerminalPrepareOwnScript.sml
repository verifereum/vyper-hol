(* Selected terminal prefixes at supplied offsets, shared by both modes. *)
Theory symControlTerminalPrepareOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] symControlPrefixOwn
  codegenSymRel fnFrameDeepAbort fnFrameTerminalHalt generatedPrefixSim
  symControlTerminalSafetyOwn symControlTerminalWordStackOwn
  deepInstSim fnPlanPrefix deepResidualSim allocMono stackOpSim
  asmSplice frameRel contextCodegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem asmSymSem venomInst dfgDefs

(* Parser abbreviation only, exactly the existing bridge-core relation. *)
val prepare_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", prepare_bridge_core_tm);

Theorem sym_frame_entry_selected_prefix_sim_marked_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  opc <> INVOKE /\ o2pc = build_offset_to_pc prog /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked spillbase ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  ops = iops ++ rops ++ suffix /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\
  bridge_core lo code_ok st ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) ==>
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?mid ss_mid.
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged
      (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    context_memory_rel cplan vs.vs_memory mid.as_memory /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) ss = SymOK ss_mid /\
    bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss_mid /\
    sym_kinds_ok cplan fn ret srest arranged ss_mid /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss_mid.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all frame_entry_selected_prefix_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[deepInstSimTheory.marked_operand_owned] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
   plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps` by
    metis_tac[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
              deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base` by
    metis_tac[allocMonoTheory.reorder_plan_spill_base,
              allocMonoTheory.emit_input_plan_spill_base] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
        stackOpSimTheory.asm_block_at_append] >>
  `arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  drule_all sym_selected_prefix_frame_sim_marked_mode_conditional >> strip_tac >>
  gvs[] >> qexists `mid` >> simp[] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

(* These pure decompositions are migrated to this lower preparation boundary;
   the owner join retains their old qualified APIs as corollaries. *)
Theorem assert_selected_prefix_decompose:
  inst.inst_opcode = ASSERT /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) ==>
  compute_operands inst = [cond] /\
  ?iops prepared rops arranged.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"] /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule_all genBlockSimTheory.assert_plan_decompose >> strip_tac >>
  rename1 `emit_input_plan ASSERT [cond] nl ps = (iops,prepared)` >>
  rename1 `reorder_plan dfg [cond] prepared = (rops,arranged)` >>
  conj_tac >- simp[] >> qexistsl [`iops`, `prepared`, `rops`, `arranged`] >>
  gvs[allocMonoTheory.release_dead_spills_spill_base, allocMonoTheory.release_dead_spills_next_offset]
QED

Theorem assert_unreachable_selected_prefix_decompose:
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) ==>
  compute_operands inst = [cond] /\
  ?iops prepared rops arranged lbl.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl] /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule_all genBlockSimTheory.assert_unreachable_plan_decompose >> strip_tac >>
  rename1 `emit_input_plan ASSERT_UNREACHABLE [cond] nl ps = (iops,prepared)` >>
  rename1 `reorder_plan dfg [cond] prepared = (rops,arranged)` >>
  rename1 `fresh_label "reachable" _ = (endlabel,after)` >>
  conj_tac >- simp[] >> qexistsl [`iops`, `prepared`, `rops`, `arranged`, `endlabel`] >>
  gvs[allocMonoTheory.release_dead_spills_spill_base, allocMonoTheory.release_dead_spills_next_offset,
      fresh_label_def, plan_state_component_equality]
QED

Theorem sym_conditional_abort_frame_prefix_deep_mode_conditional:
  !base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\
  bridge_core lo code_ok st ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) ==>
  ?pre arranged mid ss_mid suffix.
    ops = pre ++ suffix /\
    ((inst.inst_opcode = ASSERT /\
      suffix = [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]) \/
     (inst.inst_opcode = ASSERT_UNREACHABLE /\ ?lbl.
      suffix = [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl])) /\
    arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp suffix) /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK ss_mid /\
    bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss_mid /\
    sym_kinds_ok cplan fn ret srest arranged ss_mid /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss_mid.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog)
Proof
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `?iops prepared rops arranged suffix.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ suffix /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
    compute_operands inst = [cond] /\
    ((inst.inst_opcode = ASSERT /\
      suffix = [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]) \/
     (inst.inst_opcode = ASSERT_UNREACHABLE /\ ?lbl.
      suffix = [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl]))` by
    (Cases_on `inst.inst_opcode = ASSERT`
     >- (drule_all assert_selected_prefix_decompose >> metis_tac[])
     >> metis_tac[assert_unreachable_selected_prefix_decompose]) >>
  `inst.inst_opcode <> INVOKE /\
   PERM (compute_operands inst) (compute_operands inst) /\
   LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked_mode_conditional >>
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  pop_assum (qx_choose_then `mid` (qx_choose_then `ss_mid` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`iops ++ rops`, `arranged`, `mid`, `ss_mid`, `suffix`] >> simp[] >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  gvs[] >> metis_tac[]
QED

Theorem sym_regular_abort_frame_prefix_deep_mode_conditional:
  !base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\
  bridge_core lo code_ok st ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) ==>
  ?pre arranged mid ss_mid.
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    asm_block_at prog mid.as_pc [AsmOp name] /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK ss_mid /\
    bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss_mid /\
    sym_kinds_ok cplan fn ret srest arranged ss_mid /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss_mid.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog)
Proof
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all generatedPrefixSimTheory.regular_plan_selected_prefix >> strip_tac >>
  `selected = compute_operands inst` by metis_tac[] >>
  `emitted.ps_alloc = arranged.ps_alloc` by
    simp[generatedPrefixSimTheory.emit_output_fold_alloc] >>
  `emitted.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
   emitted.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by
    (drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> simp[]) >>
  `arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
   PERM (compute_operands inst) selected /\
   LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
   ops = iops ++ rops ++ ([SOEmit name] ++ popops ++ optops)` by
    gvs[listTheory.APPEND_ASSOC] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked_mode_conditional >>
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  pop_assum (qx_choose_then `mid` (qx_choose_then `ss_mid` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`iops ++ rops`, `arranged`, `mid`, `ss_mid`] >> simp[] >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
       execute_plan_def, exec_stack_op_def] >> gvs[] >> metis_tac[]
QED

Theorem terminal_operands_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x
Proof
  ACCEPT_TAC symControlTerminalWordStackOwnTheory.terminal_operands_not_retpc
QED

Theorem terminal_arranged_word_stack_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
  (mid.as_stack ++ rest = values ++
     DROP (LENGTH (compute_operands inst)) (mid.as_stack ++ rest)) /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  ACCEPT_TAC (symControlTerminalWordStackOwnTheory.terminal_arranged_word_stack_mode_split_maps
    |> Q.INST [`bridge_lo` |-> `lo`])
QED

Theorem sym_frame_terminal_prefix_setup_marked_mode_conditional:
  !cp base.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
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
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ codegen_ready_fn fn /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\
  bridge_core lo code_ok st ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) ==>
  ?n mid name ss_mid.
    asm_steps lo o2pc prog n st = AsmOK mid /\
    asm_block_at prog mid.as_pc [AsmOp name] /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    context_memory_rel cp vs.vs_memory mid.as_memory /\
    venom_asm_terminal_rel vs mid /\ mid.as_call_ctx = vs.vs_call_ctx /\
    (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
      mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack /\
      ?suffix. ss_mid.sym_stack = MAP Val values ++ suffix) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss_mid /\
    bridge_core lo code_ok mid ss_mid /\
    (!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rename1 `MEM r cplan.cp_regions` >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] /\ ~is_commutative inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term label ps =
      (ops,final)` by
    (gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
        venomWfTheory.inst_wf_def, asmIRTheory.venom_to_evm_name_def,
        venomEffectsTheory.is_commutative_def, compute_operands_def]) >>
  drule_all fnFrameTerminalHaltTheory.output_free_regular_plan >> strip_tac >>
  `ssa_form fn /\ label_positions_ok inst` by
    metis_tac[stackPlanGenTheory.codegen_ready_fn_def,
              unitShapeDefsTheory.fn_shape_ok_def,
              unitShapeDefsTheory.inst_shape_ok_def, listTheory.EVERY_MEM] >>
  `PERM (compute_operands inst) (compute_operands inst) /\
   LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
   arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by gvs[] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked_mode_conditional >>
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  pop_assum (qx_choose_then `mid` (qx_choose_then `ss_mid` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))`,
    `mid with as_stack := mid.as_stack ++ rest`, `name`, `ss_mid`] >>
  simp[] >>
  `asm_block_at prog mid.as_pc [AsmOp name]` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
        execute_plan_def, exec_stack_op_def] >>
  `!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cplan b` by
    metis_tac[sym_kinds_ok_def] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `venom_asm_rel _ _ _ mid` mp_tac >>
      simp[codegenRelTheory.venom_asm_rel_def, frame_view_def]) >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
   MEM inst.inst_opcode
     [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
      INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL]` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all terminal_arranged_word_stack_mode >> simp[]
QED
