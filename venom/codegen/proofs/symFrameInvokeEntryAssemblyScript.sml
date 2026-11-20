(* Selection and local callee specialization share no global old/own implication. *)
Theory symFrameInvokeEntryAssembly
Ancestors
  symFrameInvokeSupport symFrameInvokePrefixOwn
  symInvokeEntryFacts symInvokeEntryOwn asmSymOwnStep
  symFnSimSpec codegenSymRel fnFrameDeepInvoke asmSymBridge asmSymSem
  frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs list symPlannerSim prefixExec mixedPrefixSim symShuffleSim gasFrameSim
  fnFrameStepsRevertForward

(* Parametric in execution, relation and frame: the canonical adapter uses
   sym_steps/asm_sym_rel/sym_frame_inv directly, without own-data bounds. *)
Theorem sym_invoke_enter_callee_paired_local:
  !run rel frame fuel ctx cp callee Inv cvs prog o2pc args rest srest lo st
   inst arg_ops nm nl ps dfg ops fn ra mem0 vs base r ret ss.
  (!j cas ret_off saved ret_lbl scas saved_sym cpc.
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) = SOME cpc /\
    rel cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ (saved_sym ++ srest) /\
    MEM (AsmLabel ret_lbl) prog /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) ==>
    (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (run n scas)) /\
    (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (run n scas)) /\
    (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
      ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
        as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ (saved ++ rest) /\
        fn_return_state_rel ctx cp callee vs' cas as' /\
        run n scas = SymOK ss' /\ rel as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest) /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))) /\
  (?j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc sms scas saved_sym.
    callee.fn_name = nm /\ compute_operands inst = arg_ops /\
    LENGTH args = LENGTH arg_ops /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH arg_ops) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |> /\
    frame arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) st = AsmOK cas /\
    run (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
    rel cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) prog) ==>
  ?j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc sms scas saved_sym.
    callee.fn_name = nm /\ compute_operands inst = arg_ops /\
    LENGTH args = LENGTH arg_ops /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH arg_ops) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |> /\
    frame arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) st = AsmOK cas /\
    run (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
    rel cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) prog /\
    (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (run n scas)) /\
    (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (run n scas)) /\
    (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
      ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
        as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3 /\
        as'.as_stack = REVERSE rv.iret_values ++ (saved ++ rest) /\
        fn_return_state_rel ctx cp callee vs' cas as' /\
        run n scas = SymOK ss' /\ rel as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest) /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
Proof
  rpt gen_tac >> strip_tac >>
  `scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ (saved_sym ++ srest)` by
    simp[APPEND_ASSOC] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`j`, `iops`, `prepared`, `rops`, `arranged`, `ret_lbl`, `ret_off`,
    `post`, `mid`, `saved`, `cas`, `pc`, `sms`, `scas`, `saved_sym`] >>
  simp[]
QED

Theorem sym_invoke_enter_callee_paired_own:
  !allow_own own fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops callee args cvs
   rpolicy env ret srest labs0 ss.
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
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_fn_sim_at_own allow_own fuel /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps st ss ==>
  ?j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc sms scas saved_sym.
    callee.fn_name = nm /\ compute_operands inst = arg_ops /\
    LENGTH args = LENGTH arg_ops /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH arg_ops) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |> /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) st = AsmOK cas /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
    asm_sym_rel_own lo prog env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) prog /\
    (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n scas)) /\
    (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n scas)) /\
    (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
      ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
        as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3 /\
        as'.as_stack = REVERSE rv.iret_values ++ (saved ++ rest) /\
        fn_return_state_rel ctx cp callee vs' cas as' /\
        sym_steps_mode allow_own prog env own n scas = SymOK ss' /\
        asm_sym_rel_own lo prog env own as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest) /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
Proof
  rpt gen_tac >> strip_tac >>
  irule sym_invoke_enter_callee_paired_local >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule sym_invoke_callee_sim_own >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule sym_invoke_enter_callee_prefix_own >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
