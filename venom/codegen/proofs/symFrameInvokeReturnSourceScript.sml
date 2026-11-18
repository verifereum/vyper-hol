Theory symFrameInvokeReturnSource
Ancestors
  symFrameInvokeSupport symFrameInvokePrefixOwn frameRel list planExec symFrameInvokeCalleePointwise

(* Only the installed callee's internal-return contract is used here. *)

Theorem sym_invoke_source_ok_local:
  !cp allow_own lo prog env own o2pc Inv ctx fn inst nm arg_ops callee base ps
   prepared nl dfg iops rops arranged liveness cfg halting term label ops final
   st r ra rest mem0 vs mid args saved cas ret_off pc ret srest labs0 sms scas
   saved_sym ret_lbl post ss fuel cvs rv rvs vs'.
  (!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss') /\
  o2pc = build_offset_to_pc prog /\
  codegen_context_obligations Inv ctx cp /\ codegen_ready_fn fn /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\ callee.fn_name = nm /\
  generated_plan_state_wf_marked base ps /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
  emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
  reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  compute_operands inst = arg_ops /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
  arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\ LENGTH args = LENGTH arg_ops /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  cas = mid with <|as_stack := n2w ret_off :: mid.as_stack; as_pc := pc|> /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 arranged mid sms /\
  scas.sym_mem_labels = sms.sym_mem_labels /\
  LIST_REL (op_kind_ok fn ret)
    (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
  ops = iops ++ rops ++
    [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
  asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) st = AsmOK cas /\
  sym_steps_mode allow_own prog env own
    (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
  (!rv v. run_blocks fuel ctx callee cvs = IntRet rv v ==>
    ?n a s. asm_steps lo o2pc prog n cas = AsmOK a /\
      a.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3 /\
      a.as_stack = REVERSE rv.iret_values ++ (saved ++ rest) /\
      fn_return_state_rel ctx cp callee v cas a /\
      sym_steps_mode allow_own prog env own n scas = SymOK s /\
      asm_sym_rel_own lo prog env own a s /\
      s.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest) /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
        FLOOKUP s.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
      (!b. b IN FDOM s.sym_mem_labels ==> context_spill_byte cp b)) /\
  run_blocks fuel ctx callee cvs = IntRet rv rvs /\
  bind_outputs inst.inst_outputs rv.iret_values
    (adopt_return_fmp rv (merge_callee_state vs rvs)) = SOME vs' ==>
  ?n as' ss'. asm_steps lo o2pc prog n st = AsmOK as' /\
    fn_frame_inv ctx cp lo fn ra rest mem0 final vs' as' /\
    as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 final as' ss'
Proof
  ACCEPT_TAC sym_invoke_return_pointwise_compose
QED

Theorem sym_invoke_source_ok_own:
  !allow_own own fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss vs'.
  (!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss') /\
  ctx = unit.cu_context /\ code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
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
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_fn_sim_at_own allow_own fuel /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?n as' ss'. asm_steps lo o2pc prog n st = AsmOK as' /\
    fn_frame_inv ctx cp lo fn ra rest mem0 final vs' as' /\
    as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 final as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_source_ok_pointwise >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then irule >>
  simp[SF CONJ_ss] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      irule symFrameInvokeSupportTheory.sym_invoke_callee_sim_own >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED
