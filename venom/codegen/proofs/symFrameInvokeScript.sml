(*
 * Leaf B of the label-discipline proof, INVOKE: the call runs on the
 * symbolic machine without SymBad, from the callee's symbolic
 * function-level simulation at the same fuel (sym_fn_sim_at).  The
 * statement is codegen's own gen_invoke_frame_sim_deep with the symbolic
 * premises and conclusions added, over the same n steps.
 *
 * TOP-LEVEL:
 *   sym_invoke_frame_sim_deep
 *)
Theory symFrameInvoke
Ancestors
  symFrameInvokeSupport symFrameInvokePrefixOwn symFrameInvokeEntryAssembly
  symFrameInvokeTerminalSource symFrameInvokeReturnSource symFrameInvokeSourceOwn
  symInvokeEntryFacts symInvokeEntryOwn
  symFrameBoundaryPairing[qualified,ignore_grammar] asmSymOwnStep
  symPostfixSim
  symFnSimSpec codegenSymRel fnFrameDeepInvoke asmSymBridge asmSymSem
  frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs list symPlannerSim prefixExec mixedPrefixSim symShuffleSim gasFrameSim
  fnFrameStepsRevertForward
  symFrameInvokeCalleePointwise

(* Canonical entry APIs are corollaries of the shared entry facts. *)
Theorem sym_invoke_argument_not_code_end:
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  metis_tac[sym_invoke_argument_not_code_end_own,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_invoke_argument_word_kind:
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\ MEM op args /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  metis_tac[sym_invoke_argument_word_kind_own,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

(* Label-free INVOKE preparation is precisely ADD preparation.  This is
   the same reduction used by invoke_selected_prefix_sim_marked. *)
Theorem sym_invoke_prefix_pair:
  !lo o2pc p env ctx cp fn ret srest labs0 ps cs ss r n cs' ss' ps'.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  asm_steps lo o2pc p n cs = AsmOK cs' /\
  sym_steps p env n ss = SymOK ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rpt strip_tac >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`cs.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env cs.as_code
     ctx cplan fn ret srest labs0 ps cs ss` by
    simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >>
  `sym_steps_mode F p env cs.as_code n ss = SymOK ss'` by
    simp[sym_steps_mode_def] >>
  drule_all sym_invoke_prefix_pair_own >>
  simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own]
QED

Theorem sym_invoke_selected_frame_prefix:
  !p env ctx cp fn ret srest labs0 ps cs ss mid operands nl iops prepared
   dfg rops arranged base r lo o2pc.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at p cs.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) /\
  asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) cs =
    AsmOK mid ==>
  ?sms. sym_steps p env (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) ss =
          SymOK sms /\
        sym_frame_inv p env ctx cp fn ret srest labs0 arranged mid sms
Proof
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`cs.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env cs.as_code
     ctx cplan fn ret srest labs0 ps cs ss` by
    simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >>
  drule_all sym_invoke_selected_frame_prefix_own >>
  simp[sym_steps_mode_def, symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >> metis_tac[]
QED

Theorem sym_invoke_argument_list_words:
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  LIST_REL (op_kind_ok fn ret) (REVERSE args) svs ==>
  EVERY (\sv. ?w. sv = Val w) svs
Proof
  metis_tac[sym_invoke_argument_list_words_own,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_invoke_arranged_stack:
  !p env ctx cp fn ret srest ps cs ss inst nm args saved_ops values saved rest.
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  sym_kinds_ok cp fn ret srest ps ss /\ asm_sym_rel p env cs ss /\
  ps.ps_stack = saved_ops ++ args /\
  cs.as_stack = values ++ saved ++ rest /\ LENGTH values = LENGTH args ==>
  ?saved_sym.
    ss.sym_stack = MAP Val values ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym
Proof
  rpt strip_tac >> irule sym_invoke_arranged_stack_core >>
  gvs[asm_sym_rel_def] >>
  metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_invoke_call_entry_pair:
  !p env lo o2pc mid sms cas ret_lbl nm.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\ asm_sym_rel p env mid sms /\
  asm_block_at p mid.as_pc
    [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"] /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas ==>
  ?scas. sym_steps p env 3 sms = SymOK scas /\
    asm_sym_rel p env cas scas /\
    scas.sym_stack = Lab ret_lbl 0 :: sms.sym_stack /\
    scas.sym_mem_labels = sms.sym_mem_labels
Proof
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`mid.as_code`, `env`] assume_tac) >>
  `asm_sym_rel_own (SND (compute_label_offsets p)) p env mid.as_code mid sms` by
    simp[asm_sym_rel_own_canonical] >>
  drule_all sym_invoke_call_entry_pair_own >>
  simp[sym_steps_mode_def, asm_sym_rel_own_canonical] >> metis_tac[]
QED

Theorem sym_invoke_entry_symbolic_boundary:
  !p env lo o2pc ctx cp fn ret srest labs0 arranged mid sms cas inst nm args
   saved_ops values saved rest ret_lbl fmp post n ss.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  sym_frame_inv p env ctx cp fn ret srest labs0 arranged mid sms /\
  arranged.ps_stack = saved_ops ++ args /\
  mid.as_stack = values ++ saved ++ rest /\ LENGTH values = LENGTH args /\
  asm_block_at p mid.as_pc (execute_plan fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas /\
  sym_steps p env n ss = SymOK sms ==>
  ?scas saved_sym.
    sym_steps p env (n + 3) ss = SymOK scas /\
    sym_steps p env 3 sms = SymOK scas /\ asm_sym_rel p env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val values ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) p
Proof
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 arranged mid sms` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`mid.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env mid.as_code
     ctx cplan fn ret srest labs0 arranged mid sms` by
    simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >>
  `sym_steps_mode F p env mid.as_code n ss = SymOK sms` by
    simp[sym_steps_mode_def] >>
  drule_all (REWRITE_RULE [boolTheory.COND_CLAUSES] (Q.SPEC `F` sym_invoke_entry_symbolic_boundary_own)) >>
  simp[sym_steps_mode_def, asm_sym_rel_own_canonical] >> metis_tac[]
QED

(* Shared symbolic execution of the return label and numeric cleanup. *)
(* The function contract specialized to a callee installed by INVOKE. *)
(* Paired call-prefix composition keeps the witness chosen by the callee. *)
(* Pair the concrete entry witnesses with the symbolic prefix and call. *)
Theorem sym_invoke_selected_entry_pair:
  !p env ctx cp fn ret srest labs0 ps cs ss mid nl iops prepared dfg rops
   arranged base r lo o2pc inst nm arg_ops args saved rest ret_lbl post cas.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\ fn_shape_ok fn /\ ssa_form fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  compute_operands inst = arg_ops /\
  EVERY (\op. ~is_label_operand op) arg_ops /\
  (!op. MEM op arg_ops /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE arg_ops nl ps = (iops,prepared) /\
  reorder_plan dfg arg_ops prepared = (rops,arranged) /\
  LENGTH arg_ops <= 16 /\ LENGTH arg_ops <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) arg_ops /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at p cs.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) /\
  asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) cs = AsmOK mid /\
  arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\ LENGTH args = LENGTH arg_ops /\
  asm_block_at p mid.as_pc (execute_plan cp.cp_initial_fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas ==>
  ?sms scas saved_sym.
    sym_frame_inv p env ctx cp fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3)
      cs = AsmOK cas /\
    sym_steps p env (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3)
      ss = SymOK scas /\
    asm_sym_rel p env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) p
Proof
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`cs.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env cs.as_code
     ctx cplan fn ret srest labs0 ps cs ss` by
    simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >>
  drule_all (REWRITE_RULE [boolTheory.COND_CLAUSES] (Q.SPEC `F` sym_invoke_selected_entry_pair_own)) >>
  simp[sym_steps_mode_def, symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own,
       asm_sym_rel_own_canonical] >> metis_tac[]
QED

(* Source invariants needed only on a successful internal return. *)
(* The spill/stack argument is independent of the concrete relation. *)
(* Rebuild the caller's symbolic frame at the callee's internal return. *)
(* Source-to-paired-entry boundary, retaining the concrete return witnesses. *)
Theorem sym_invoke_enter_callee_paired:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops callee args cvs
   rpolicy env ret srest labs0 ss.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
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
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss ==>
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
    sym_frame_inv prog env ctx cp fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) st = AsmOK cas /\
    sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
    asm_sym_rel prog env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) prog /\
    (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n scas)) /\
    (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n scas)) /\
    (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
      ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
        as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3 /\
        as'.as_stack = REVERSE rv.iret_values ++ (saved ++ rest) /\
        fn_return_state_rel ctx cp callee vs' cas as' /\
        sym_steps prog env n scas = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest) /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
Proof
  rpt gen_tac >> strip_tac >>
  irule sym_invoke_enter_callee_paired_local >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule symFrameInvokeSupportTheory.sym_invoke_callee_sim >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`st.as_code`, `env`] assume_tac) >>
  rename1 `generate_context_plan ctx = SOME cplan` >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env st.as_code
     ctx cplan fn ret srest labs0 ps st ss` by
    simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >>
  drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (symFrameInvokePrefixOwnTheory.sym_invoke_enter_callee_prefix_own
      |> Q.SPEC `F` |> PURE_REWRITE_RULE [COND_CLAUSES]) >>
  disch_then drule_all >>
  simp[sym_steps_mode_def, symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own,
    asm_sym_rel_own_canonical] >> metis_tac[]
QED

(* Source-level halting outcome: select one paired call, then compose. *)
Theorem sym_invoke_source_halt:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss vs'.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
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
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?n as'. asm_steps lo o2pc prog n st = AsmHalt as' /\
    venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_halt >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_paired >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at _`)) >>
  disch_then drule_all >> strip_tac >>
  drule_all (symFrameInvokeCalleePointwiseTheory.sym_invoke_halt_pointwise_compose
    |> SPEC_ALL |> Q.INST [`allow_own` |-> `F`]
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]) >>
  simp[]
QED

Theorem sym_invoke_source_abort:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss a vs'.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
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
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert as') \/
           (a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault as')) /\
    venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_abort >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_paired >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at _`)) >>
  disch_then drule_all >> strip_tac >>
  drule_all (symFrameInvokeCalleePointwiseTheory.sym_invoke_abort_pointwise_compose
    |> SPEC_ALL |> Q.INST [`allow_own` |-> `F`]
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]) >>
  simp[]
QED

Theorem sym_invoke_source_ok:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss vs'.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
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
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?n as' ss'. asm_steps lo o2pc prog n st = AsmOK as' /\
    fn_frame_inv ctx cp lo fn ra rest mem0 final vs' as' /\
    as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss' /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 final as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_ok >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_paired >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at _`)) >>
  disch_then drule_all >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cplan` >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by
    (qpat_x_assum `LENGTH (compute_operands inst) <= LENGTH (SND _).ps_stack` mp_tac >>
     qpat_x_assum `emit_input_plan _ _ _ _ = _` mp_tac >> simp[]) >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env mid.as_code
     ctx cplan fn ret srest labs0 arranged mid sms` by
    simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`mid.as_code`, `env`] assume_tac) >>
  `!rv v. run_blocks fuel ctx (EL j ctx.ctx_functions) cvs = IntRet rv v ==>
    ?n a s. asm_steps (SND (compute_label_offsets prog)) o2pc prog n cas = AsmOK a /\
      a.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3 /\
      a.as_stack = REVERSE rv.iret_values ++ (saved ++ rest) /\
      fn_return_state_rel ctx cplan (EL j ctx.ctx_functions) v cas a /\
      sym_steps_mode F prog env mid.as_code n scas = SymOK s /\
      asm_sym_rel_own (SND (compute_label_offsets prog)) prog env mid.as_code a s /\
      s.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest) /\
      (!b. context_spill_byte cplan b /\
        ~closure_spill_byte ctx cplan (EL j ctx.ctx_functions).fn_name b ==>
        FLOOKUP s.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
      (!b. b IN FDOM s.sym_mem_labels ==> context_spill_byte cplan b)` by
    (rpt gen_tac >> strip_tac >> fs[] >>
     qpat_x_assum `!rv v. run_blocks _ _ _ _ = IntRet rv v ==> _` drule >>
     strip_tac >>
     imp_res_tac asmOwnCodeInvariantTheory.asm_steps_code_preserved >>
     rename1 `sym_steps prog env nret scas = SymOK sret` >>
     rename1 `asm_steps _ _ prog nret cas = AsmOK aret` >>
     qexistsl [`nret`, `aret`, `sret`] >>
     gvs[sym_steps_mode_def, asm_sym_rel_own_canonical, APPEND_ASSOC]) >>
  qpat_x_assum `EL j ctx.ctx_functions = callee` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    (symFrameInvokeCalleePointwiseTheory.sym_invoke_return_pointwise_compose |> SPEC_ALL |> Q.INST [`allow_own` |-> `F`]
      |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]) >>
  disch_then (drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ arranged _ _`)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pat `sym_steps _ _ _ _ = SymOK _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ arranged _ _`)) >>
  disch_then drule_all >>
  simp[sym_steps_mode_def, symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >> metis_tac[]
QED

Theorem sym_invoke_frame_sim_deep:
  !fuel rpolicy unit cp prog ctx lo o2pc Inv liveness dfg cfg fn inst
   next_liveness is_halting next_is_term bb_label base ps vs as ops ps' r ra
   rest mem0 nm arg_ops
   env ret srest labs0 ss.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\
    MEM fn ctx.ctx_functions /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    Inv ctx fn inst vs /\ active_inst fn inst vs /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
       ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
                FLOOKUP o2pc off = SOME pc /\
                asm_block_at prog pc
                  (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
    (* The callee's function-level simulation at this fuel. *)
    (!j callee rj cvs cas cra crest cpc.
       j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
       EL j cp.cp_regions = rj /\
       MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
       (!l. FLOOKUP cvs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
       fn_entry_inv Inv ctx callee cvs /\
       asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
       LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
       fn_entry_state_rel cp callee cvs cas cra crest /\
       (fn_has_retpc callee ==> FLOOKUP o2pc (w2n cra) = SOME cpc) ==>
       (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
                  venom_asm_terminal_rel vs' as') /\
       (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
          ?n as'. ((a = Revert_abort /\
                    asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\
                    asm_steps lo o2pc prog n cas = AsmFault as')) /\
                  venom_asm_terminal_rel vs' as') /\
       (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
                  as'.as_pc = cpc /\
                  as'.as_stack = REVERSE rv.iret_values ++ crest /\
                  fn_return_state_rel ctx cp callee vs' cas as')) /\
    opaque_use_ok fn /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    (* The callee's symbolic function-level simulation at this fuel. *)
    sym_fn_sim_at fuel /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    (!vs'. step_inst fuel ctx inst vs = OK vs' ==>
       ?n as' ss'.
         asm_steps lo o2pc prog n as = AsmOK as' /\
         fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
         as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
         sym_steps prog env n ss = SymOK ss' /\
         sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss') /\
    (!vs'. step_inst fuel ctx inst vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_ok >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_halt >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_abort >> simp[]
QED

(* Return restoration at supplied label offsets and fixed own-code bytes. *)
(* The numeric supplier selects fin; the symbolic suffix reconstructs its
   matching frame without reproving the concrete return theorem. *)
