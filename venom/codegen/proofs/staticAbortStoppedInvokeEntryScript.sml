Theory staticAbortStoppedInvokeEntry
Ancestors
  fnStaticAbortBodyFacts fnBlockBodyClasses fnBlockBodySteps symFrameInvoke
  codegenSymRel fnStaticAbortBoundary unitShapeDefs genBlockSim
  fnFrameBoundaryInvoke fnFrameDeepInvoke contextStaticAbortRel
  contextCodegenRelProps venomExecProps venomExecSemantics venomInst
  contextCodegenRel list
  symFrameInvokeSupport symInvokeEntryOwn asmSymModeOwn
  asmSymOwnStep symFrameBoundaryPairing

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

(* The caller prefix is independent of the recursive callee simulation.
   In particular it requires neither ordinary global memory obligations
   nor sym_fn_sim_at's terminal-only Abort clause. *)
Theorem stopped_invoke_paired_entry_mode:
  !allow_own own.
  (if allow_own then body_inv_abort_reloc else body_inv_abort) rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  LENGTH (compute_operands inst) <= 16 /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps ast ss ==>
  ?ops ps' rest' j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc
   sms scas saved_sym.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    callee.fn_name = nm /\ compute_operands inst = arg_ops /\
    LENGTH args = LENGTH arg_ops /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cpl.cp_initial_fmp (EL j cpl.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cpl callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE arg_ops (live_vars_at liveness bb.bb_label (k + 1)) ps =
      (iops,prepared) /\
    reorder_plan dfg arg_ops prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops))) ast = AsmOK mid /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 arranged vs mid /\
    arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH arg_ops) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <|as_stack := n2w ret_off :: mid.as_stack; as_pc := pc|> /\
    (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3)
      ast = AsmOK cas /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3)
      ss = SymOK scas /\
    (if allow_own then asm_sym_rel_own lo prog env own else asm_sym_rel prog env) cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cpl b) /\
    MEM (AsmLabel ret_lbl) prog
Proof
  ntac 2 gen_tac >> strip_tac >>
  `body_inv_abort_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0` by
    (Cases_on `allow_own` >> fs[body_inv_abort_reloc_canonical]) >>
  qabbrev_tac `fixed = if allow_own then own else ast.as_code` >>
  `sym_frame_inv_own lo prog env fixed ctx cpl fn ret srest labs0 ps ast ss` by
    (Cases_on `allow_own` >>
     gvs[Abbr `fixed`, body_inv_abort_def, sym_frame_inv_canonical_own]) >>
  drule body_inv_abort_plan_reloc >> strip_tac >>
  drule_all body_plan_call_entry_reloc >> strip_tac >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_step_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  `ops' = ops /\ ps'' = ps'` by fs[] >>
  `ctx = unit.cu_context /\ unit_shape_ok unit /\
   code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
   dfg = dfg_build_function fn` by fs[body_plan_inv_reloc_def] >>
  `compute_operands inst = arg_ops /\
   EVERY (\op. ~is_label_operand op) arg_ops /\ ssa_form fn /\
   (!op. MEM op arg_ops /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
   LENGTH arg_ops <= LENGTH prepared.ps_stack /\
   EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp (iops ++ rops))` by
    (irule (Q.INST [`ops` |-> `ops`,
       `post` |-> `[SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post`]
       (SPEC_ALL symFrameInvokeSupportTheory.sym_invoke_selected_entry_facts)) >>
     rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qexistsl_tac [`arranged`, `dfg`] >> first_assum ACCEPT_TAC)
     >- (qexists `live_vars_at liveness bb.bb_label (k + 1)` >>
         conj_tac >> first_assum ACCEPT_TAC)
     >- (qexistsl_tac [`ctx`, `unit`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC)
     >> qexistsl_tac [`nm`, `ops`, `post`, `ret_lbl`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (pure_rewrite_tac[APPEND_ASSOC] >>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_ASSOC])) >>
     qpat_x_assum `ops' = ops` (SUBST1_TAC o SYM) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_shape_ok fn` by
    (fs[unit_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `generate_context_plan ctx = SOME cpl` by fs[body_plan_inv_reloc_def] >>
  `fn_shape_ok callee` by
    (fs[unit_shape_ok_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `MEM (AsmLabel nm) prog` by
    (qpat_x_assum `callee.fn_name = nm` (SUBST1_TAC o SYM) >>
     irule symFrameInvokeSupportTheory.sym_invoke_callee_code_label >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cpl`, `ctx`, `j`, `cas.as_pc`, `EL j cpl.cp_regions`] >>
     rpt conj_tac >> TRY (REFL_TAC >> NO_TAC) >> first_assum ACCEPT_TAC) >>
  qpat_assum `compute_operands inst = arg_ops`
    (fn th => SUBST_ALL_TAC th >> assume_tac th) >>
  `!n cs now next. asm_sym_rel_own lo prog env fixed cs now /\
      sym_steps_mode allow_own prog env fixed n now = SymOK next ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        asm_sym_rel_own lo prog env fixed cs' next` by
    (rpt gen_tac >> strip_tac >> metis_tac[asm_sym_steps_mode_sim]) >>
  drule_all sym_invoke_selected_entry_pair_own >> strip_tac >>
  `sym_steps_mode allow_own prog env own
     (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
   (if allow_own then asm_sym_rel_own lo prog env own else asm_sym_rel prog env) cas scas /\
   (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env)
     ctx cpl fn ret srest labs0 arranged mid sms` by
    (Cases_on `allow_own` >>
     gvs[Abbr `fixed`, body_inv_abort_def, sym_frame_inv_canonical_own,
        asm_sym_rel_own_canonical, sym_steps_mode_def]) >>
  qhdtm_assum `body_inv_abort_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_reloc_def]) >>
  `active_inst fn inst vs` by
    (simp[active_inst_def, get_instruction_def] >> metis_tac[lookup_block_label]) >>
  `Inv ctx fn inst vs` by metis_tac[] >>
  `decode_invoke inst = SOME (nm,arg_ops)` by simp[decode_invoke_def] >>
  drule_all reachability_closed_callee >> strip_tac >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `j`, `iops`, `prepared`, `rops`,
    `arranged`, `ret_lbl`, `ret_off`, `post`, `mid`, `saved`, `cas`, `pc`,
    `sms`, `scas`, `saved_sym`] >>
  rpt conj_tac >> TRY (REFL_TAC >> NO_TAC) >> first_assum ACCEPT_TAC
QED

Theorem stopped_invoke_paired_entry:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  LENGTH (compute_operands inst) <= 16 /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
  ?ops ps' rest' j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc
   sms scas saved_sym.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    callee.fn_name = nm /\ compute_operands inst = arg_ops /\
    LENGTH args = LENGTH arg_ops /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cpl.cp_initial_fmp (EL j cpl.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cpl callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE arg_ops (live_vars_at liveness bb.bb_label (k + 1)) ps =
      (iops,prepared) /\
    reorder_plan dfg arg_ops prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops))) ast = AsmOK mid /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 arranged vs mid /\
    arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH arg_ops) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <|as_stack := n2w ret_off :: mid.as_stack; as_pc := pc|> /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3)
      ast = AsmOK cas /\
    sym_steps prog env (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3)
      ss = SymOK scas /\
    asm_sym_rel prog env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cpl b) /\
    MEM (AsmLabel ret_lbl) prog
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]
    (Q.SPECL [`F`, `[]`] stopped_invoke_paired_entry_mode))
QED
