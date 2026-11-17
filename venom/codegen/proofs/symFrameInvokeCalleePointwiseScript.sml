(* INVOKE composition from the installed callee's pointwise run contract.
 * This lower companion does not depend on the global source wrappers. *)
Theory symFrameInvokeCalleePointwise
Ancestors
  symFrameInvokeSupport symFrameInvokePrefixOwn frameRel list planExec

(* The return restoration argument lives here once; the public local API
 * in ReturnSource is an exact-statement corollary. *)
Theorem sym_invoke_return_pointwise_compose:
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!rv v. run_blocks _ _ _ _ = IntRet rv v ==> _` drule >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_plan_decompose >> strip_tac >>
  rename1 `codegen_context_obligations Inv ctx cplan` >>
  rename1 `asm_steps lo o2pc prog n cas = AsmOK asr` >>
  `fn_return_state_rel ctx cplan callee rvs mid asr` by
    (qpat_x_assum `fn_return_state_rel _ _ _ _ _ asr` mp_tac >>
     simp[fn_return_state_rel_def]) >>
  gvs[] >>
  drule_all sym_invoke_return_source_facts >> strip_tac >>
  rename1 `asm_sym_rel_own lo prog env own asr ssr` >>
  `ssr.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest)` by
    simp[APPEND_ASSOC] >>
  `!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan callee.fn_name b ==>
    FLOOKUP ssr.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b` by simp[] >>
  drule_at (Pat `fresh_label _ _ = _`) sym_invoke_return_frame_from_callee_own >>
  disch_then drule_all >> strip_tac >>
  `asm_block_at prog asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))` by
    (qpat_x_assum `asr.as_pc = _` SUBST1_TAC >>
     drule fnFrameBoundaryInvokeTheory.invoke_return_block >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts)` by
    gvs[EVERY_APPEND] >>
  drule fnFrameBoundaryInvokeTheory.invoke_called_plan_fields >> strip_tac >>
  `spill_alloc_layout_wf called.ps_alloc called.ps_spilled` by gvs[] >>
  drule_all (fnFrameDeepInvokeTheory.invoke_return_frame_numeric_exact
    |> SPEC_ALL |> Q.INST [`final` |-> `release_dead_spills nl swapped`]
    |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >>
  disch_then (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ called _ _`)
    (sym_invoke_return_frame_numeric_own
      |> Q.INST [`final` |-> `release_dead_spills nl swapped`]
      |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >>
  disch_then drule_all >> strip_tac >>
  `fin.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp
    (iops ++ rops ++ [SOPushLabel ret_lbl;
      SOPushLabel callee.fn_name; SOEmit "JUMP"; SOLabel ret_lbl] ++ pops ++ opts))` by
    (fs[execute_plan_def, exec_stack_op_def] >> decide_tac) >>
  drule_at (Pat `fin.as_pc = _`) sym_invoke_ok_compose_own >>
  disch_then drule_all >> simp_tac pure_ss [arithmeticTheory.ADD_COMM] >>
  disch_then ACCEPT_TAC
QED

Theorem sym_invoke_source_ok_pointwise:
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
  (!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest.
    ctx = unit.cu_context /\
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    EL j cp.cp_regions = rj /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
    fn_entry_inv Inv ctx callee cvs /\
    setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp callee cvs cas cra crest /\
    FLOOKUP o2pc (w2n cra) = SOME cpc /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
    asm_sym_rel_own lo prog env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ csrest /\
    MEM (AsmLabel ret_lbl) prog /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) ==>
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
         as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
         fn_return_state_rel ctx cp callee vs' cas as' /\
         sym_steps_mode allow_own prog env own n scas = SymOK ss' /\
         asm_sym_rel_own lo prog env own as' ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ csrest /\
         (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
            FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))) /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?n as' ss'. asm_steps lo o2pc prog n st = AsmOK as' /\
    fn_frame_inv ctx cp lo fn ra rest mem0 final vs' as' /\
    as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 final as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_ok >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_prefix_own >>
  disch_then drule_all >> strip_tac >>
  rename1 `codegen_context_obligations Inv ctx cplan` >>
  `EL j cplan.cp_regions = EL j cplan.cp_regions` by simp[] >>
  `scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ (saved_sym ++ srest)` by
    simp[APPEND_ASSOC] >>
  qpat_x_assum `!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest. _`
    (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`)) >>
  disch_then drule_all >> strip_tac >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by
    (qpat_x_assum `LENGTH (compute_operands inst) <= LENGTH (SND _).ps_stack` mp_tac >>
     qpat_x_assum `emit_input_plan _ _ _ _ = _` mp_tac >> simp[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_return_pointwise_compose >>
  disch_then (drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ arranged _ _`)) >>
  disch_then (drule_at (Pat `sym_steps_mode _ _ _ _ _ _ = SymOK _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ arranged _ _`)) >>
  disch_then drule_all >> simp[]
QED

Theorem sym_invoke_halt_pointwise_compose:
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

Theorem sym_invoke_abort_pointwise_compose:
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

Theorem sym_invoke_source_halt_pointwise:
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
  (!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest.
    ctx = unit.cu_context /\
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    EL j cp.cp_regions = rj /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
    fn_entry_inv Inv ctx callee cvs /\
    setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp callee cvs cas cra crest /\
    FLOOKUP o2pc (w2n cra) = SOME cpc /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
    asm_sym_rel_own lo prog env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ csrest /\
    MEM (AsmLabel ret_lbl) prog /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) ==>
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
         as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
         fn_return_state_rel ctx cp callee vs' cas as' /\
         sym_steps_mode allow_own prog env own n scas = SymOK ss' /\
         asm_sym_rel_own lo prog env own as' ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ csrest /\
         (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
            FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))) /\
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
  qpat_x_assum `!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest. _`
    (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `scas.sym_stack = _`)) >>
  disch_then drule_all >> strip_tac >>
  drule_all sym_invoke_halt_pointwise_compose >> simp[]
QED

Theorem sym_invoke_source_abort_pointwise:
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
  (!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest.
    ctx = unit.cu_context /\
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    EL j cp.cp_regions = rj /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
    fn_entry_inv Inv ctx callee cvs /\
    setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp callee cvs cas cra crest /\
    FLOOKUP o2pc (w2n cra) = SOME cpc /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
    asm_sym_rel_own lo prog env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ csrest /\
    MEM (AsmLabel ret_lbl) prog /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) ==>
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
         as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
         fn_return_state_rel ctx cp callee vs' cas as' /\
         sym_steps_mode allow_own prog env own n scas = SymOK ss' /\
         asm_sym_rel_own lo prog env own as' ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ csrest /\
         (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
            FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))) /\
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
  qpat_x_assum `!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest. _`
    (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `scas.sym_stack = _`)) >>
  disch_then drule_all >> strip_tac >>
  drule_all sym_invoke_abort_pointwise_compose >> simp[]
QED

Theorem sym_invoke_frame_sim_deep_pointwise:
  !allow_own own fuel rpolicy unit cp prog ctx lo o2pc Inv liveness dfg cfg fn inst
   next_liveness is_halting next_is_term bb_label base ps vs as ops ps' r ra
   rest mem0 nm arg_ops env ret srest labs0 ss.
    (!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        asm_sym_rel_own lo prog env own cs' ss') /\
    ctx = unit.cu_context /\
    code_labels_agree prog lo /\
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
       MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
       ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
                FLOOKUP o2pc off = SOME pc /\
                asm_block_at prog pc
                  (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
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
          ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
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
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\ operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
    (!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest.
      ctx = unit.cu_context /\
      code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
      generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
      unit_shape_ok unit /\
      j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
      EL j cp.cp_regions = rj /\
      MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
      (!f inst callee_name args callee.
         MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
         MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
         inst.inst_operands = Label callee_name :: args /\
         lookup_function callee_name ctx.ctx_functions = SOME callee ==>
         fn_has_retpc callee) /\
      (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
      codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
      fn_entry_inv Inv ctx callee cvs /\
      setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
      asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
      LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
      fn_entry_state_rel cp callee cvs cas cra crest /\
      FLOOKUP o2pc (w2n cra) = SOME cpc /\
      (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
      code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
      (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
      asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
      asm_sym_rel_own lo prog env own cas scas /\
      scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ csrest /\
      MEM (AsmLabel ret_lbl) prog /\
      (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) ==>
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
           as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
           fn_return_state_rel ctx cp callee vs' cas as' /\
           sym_steps_mode allow_own prog env own n scas = SymOK ss' /\
           asm_sym_rel_own lo prog env own as' ss' /\
           ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ csrest /\
           (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
              FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
           (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))) /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    (!vs'. step_inst fuel ctx inst vs = OK vs' ==>
       ?n as' ss'.
         asm_steps lo o2pc prog n as = AsmOK as' /\
         fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
         as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
         sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
         sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps' as' ss') /\
    (!vs'. step_inst fuel ctx inst vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_ok_pointwise >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_halt_pointwise >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_abort_pointwise >> simp[]
QED
