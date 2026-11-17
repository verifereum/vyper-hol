(* Terminal INVOKE outcomes share the selected call and its paired count.
 * The support import is redirected atomically by the owner assembly join.
 *)
Theory symFrameInvokeTerminalSource
Ancestors
  symFrameInvoke fnFrameBoundaryInvoke

Theorem sym_invoke_source_halt_local:
  asm_steps lo o2pc prog k st = AsmOK cas /\
  sym_steps_mode allow_own prog env own k ss = SymOK scas /\
  run_blocks fuel ctx callee cvs = Halt vs' /\
  (!v. run_blocks fuel ctx callee cvs = Halt v ==>
    ?n a. asm_steps lo o2pc prog n cas = AsmHalt a /\
      venom_asm_terminal_rel v a /\
      sym_terminal (sym_steps_mode allow_own prog env own n scas)) ==>
  ?n as'. asm_steps lo o2pc prog n st = AsmHalt as' /\
    venom_asm_terminal_rel vs' as' /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  strip_tac >>
  qpat_x_assum `!v. run_blocks _ _ _ _ = Halt v ==> _` drule >>
  strip_tac >> drule_all sym_invoke_halt_compose_mode >> simp[]
QED

Theorem sym_invoke_source_abort_local:
  asm_steps lo o2pc prog k st = AsmOK cas /\
  sym_steps_mode allow_own prog env own k ss = SymOK scas /\
  run_blocks fuel ctx callee cvs = Abort a vs' /\
  (!ab v. run_blocks fuel ctx callee cvs = Abort ab v ==>
    ?n fin. ((ab = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert fin) \/
             (ab = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault fin)) /\
      venom_asm_terminal_rel v fin /\
      sym_terminal (sym_steps_mode allow_own prog env own n scas)) ==>
  ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert as') \/
           (a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault as')) /\
    venom_asm_terminal_rel vs' as' /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  strip_tac >>
  qpat_x_assum `!ab v. run_blocks _ _ _ _ = Abort ab v ==> _` drule >>
  disch_then (qx_choose_then `n` (qx_choose_then `fin`
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  drule_all sym_invoke_abort_compose_mode >> simp[]
QED

Theorem sym_invoke_source_halt_own:
  !allow_own own fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss vs'.
  (!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss') /\
  ctx = unit.cu_context /\
  code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\ codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\ MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\ MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
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
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_fn_sim_at_own allow_own fuel /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?n as'. asm_steps lo o2pc prog n st = AsmHalt as' /\
    venom_asm_terminal_rel vs' as' /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_halt >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_prefix_own >>
  disch_then (drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule_all >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cplan` >>
  `EL j cplan.cp_regions = EL j cplan.cp_regions` by simp[] >>
  `scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ (saved_sym ++ srest)` by
    simp[listTheory.APPEND_ASSOC] >>
  drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`) sym_invoke_callee_sim_own >>
  disch_then (drule_at (Pat `asm_sym_rel_own _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at_own _ _`)) >>
  disch_then (drule_at (Pat `scas.sym_stack = _`)) >>
  disch_then drule_all >> strip_tac >>
  drule_all sym_invoke_source_halt_local >> simp[]
QED

Theorem sym_invoke_source_abort_own:
  !allow_own own fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss a vs'.
  (!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss') /\
  ctx = unit.cu_context /\
  code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\ codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\ MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\ MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
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
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_fn_sim_at_own allow_own fuel /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert as') \/
           (a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault as')) /\
    venom_asm_terminal_rel vs' as' /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_abort >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_prefix_own >>
  disch_then (drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule_all >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cplan` >>
  `EL j cplan.cp_regions = EL j cplan.cp_regions` by simp[] >>
  `scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ (saved_sym ++ srest)` by
    simp[listTheory.APPEND_ASSOC] >>
  drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`) sym_invoke_callee_sim_own >>
  disch_then (drule_at (Pat `asm_sym_rel_own _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at_own _ _`)) >>
  disch_then (drule_at (Pat `scas.sym_stack = _`)) >>
  disch_then drule_all >> strip_tac >>
  drule_all sym_invoke_source_abort_local >> simp[]
QED
