(* Forwarded-revert continuations, shared by both symbolic execution modes. *)
Theory symControlForwardRunOwn
Ancestors
  symControlForwardStackOwn symControlForwardPrepareOwn symControlForwardCopyExecutionOwn symControlTerminalSafetyOwn
  symFrameControlFacts codegenSymRel codegenSymOwnRel asmSymBridge[qualified,ignore_grammar]
  fnFrameStepsRevertForwardDeep asmSplice asmSpliceOwn asmSymOwnCode
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs symPlannerSim symShuffleSim asmSymPc codegenEncodingWf symEmitSim

(* Transparent syntax for the producer's precise theorem-only interfaces. *)
val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);
val _ = Parse.temp_overload_on ("rf_B",
  fst (dest_imp (concl sym_rf_assign_plan_execution_mode_conditional)));
val _ = Parse.temp_overload_on ("rf_L", ``\allow_own prog env own lo code_ok.
  !n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss'``);
val control_bridge_result_tm = let
  val body = lhs (concl asmSymBridgeTheory.asm_sym_step_rel_core_canonical)
  val rel = ``asm_sym_rel p env``
  val r = mk_var ("R", type_of rel)
  val body = subst [rel |-> r] body
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars body) of
      [v] => v | _ => raise Fail ("missing result parameter " ^ n)
in list_mk_abs ([r, named "sr", named "cr"], body) end;
val _ = Parse.temp_overload_on ("bridge_result", control_bridge_result_tm);
val _ = Parse.temp_overload_on ("rf_T", ``\allow_own prog env own lo code_ok.
  !cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at prog cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc prog) ai cs = cr /\
    (!e. (if allow_own then sym_step_own prog env own ai ss
          else sym_step prog env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own prog env own ai ss else sym_step prog env ai ss) cr``);

Theorem sym_revert_prepared_stack_core:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = REVERT /\ inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  bridge_core lo code_ok cs ss /\ cs.as_stack = dst :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top ==>
  ?suffix. ss.sym_stack = MAP Val [dst;sz] ++ suffix
Proof
  strip_tac >>
  drule_all sym_revert_source_stack_words_mode >> strip_tac >>
  gvs[asmSymBridgeTheory.sval_conc_def]
QED

Theorem sym_revert_prepared_terminal_mode_conditional:
  rf_T allow_own prog env own lo code_ok /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = REVERT /\ inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  plan_stack_rel lo current (tail ++ [zop;dop]) stk /\
  operand_val current lo dop = SOME dst /\ operand_val current lo zop = SOME sz /\
  cs.as_stack = stk ++ rest /\ bridge_core lo code_ok cs ss /\ asm_static_wf prog /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) /\
  asm_block_at prog cs.as_pc [AsmOp "REVERT"] /\
  asm_step lo (build_offset_to_pc prog) (AsmOp "REVERT") cs = AsmRevert out ==>
  sym_terminal (sym_steps_mode allow_own prog env own 1 ss)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `dop <> dead_stack_marker /\ zop <> dead_stack_marker` by
    (rpt strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  `?remaining. cs.as_stack = dst :: sz :: remaining` by
    (`?d z residual. stk = d :: z :: residual /\
      operand_val current lo dop = SOME d /\ operand_val current lo zop = SOME z` by
       (irule emitSimTheory.asm_stack_top2_from_plan >> simp[] >>
        qexists `tail` >> simp[]) >> gvs[]) >>
  `?suffix. ss.sym_stack = MAP Val [dst;sz] ++ suffix` by
    (drule_all sym_revert_source_stack_words_mode >> strip_tac >>
     gvs[asmSymBridgeTheory.sval_conc_def]) >>
  irule sym_terminal_opcode_transfer_mode_conditional >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`[dst;sz]`, `code_ok`, `AsmRevert out`, `cs`, `lo`, `"REVERT"`, `suffix`] >>
  simp[asm_op_arity_def, asm_op_arity_table_def, asm_op_mem_reads_def,
       asmSemTheory.log_table_def] >>
  conj_tac
  >- (qpat_x_assum `rf_T _ _ _ _ _ _` mp_tac >> simp[]) >>
  metis_tac[]
QED

Theorem sym_plan_stack_rel_inst_idx:
  plan_stack_rel lo (frame_view fn ra (s with vs_inst_idx := k)) ops stk <=>
  plan_stack_rel lo (frame_view fn ra s) ops stk
Proof
  simp[codegenRelTheory.plan_stack_rel_def] >>
  AP_TERM_TAC >> AP_TERM_TAC >> ABS_TAC >>
  Cases_on `EL i (REVERSE ops)` >>
  simp[frame_view_def, codegenRelTheory.operand_val_def, venomStateTheory.lookup_var_def]
QED

Theorem sym_terminal_rel_inst_idx:
  venom_asm_terminal_rel (s with vs_inst_idx := k) st <=>
  venom_asm_terminal_rel s st
Proof
  simp[venom_asm_terminal_rel_def]
QED

Theorem sym_assign_success_state:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ step_inst fuel ctx inst s = OK s' ==>
  ?w. s' = s with vs_vars := s.vs_vars |+ (out,w)
Proof
  strip_tac >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  gvs[] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  once_rewrite_tac[step_inst_base_def] >> simp[] >> Cases_on `eval_operand rhs s` >>
  simp[venomStateTheory.update_var_def] >> metis_tac[]
QED

Theorem sym_assign_block_abort_continuation:
  s.vs_inst_idx = k /\ get_instruction bb k = SOME inst /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ exec_block fuel ctx bb s = Abort a s_end ==>
  ?s'. step_inst fuel ctx inst s = OK s' /\
    exec_block fuel ctx bb (s' with vs_inst_idx := SUC k) = Abort a s_end
Proof
  strip_tac >> qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, is_terminator_def] >> Cases_on `eval_operand rhs s` >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  pop_assum SUBST1_TAC >> once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = ASSIGN` SUBST1_TAC >>
  qpat_assum `inst.inst_operands = [rhs]` SUBST1_TAC >>
  qpat_assum `inst.inst_outputs = [out]` SUBST1_TAC >> simp[]
QED

Theorem sym_rf_future_non_phi:
  revert_forward_pair bb i j /\ i < k ==>
  !r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI
Proof
  rpt strip_tac >>
  `ti.inst_opcode =
    (if r = i then RETURNDATACOPY else if r = j then REVERT else ASSIGN)` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_instruction_opcode >>
     conj_tac >- decide_tac >> simp[] >> qexists `bb` >> simp[]) >>
  Cases_on `r = i` >> fs[] >> Cases_on `r = j` >> fs[]
QED

Theorem sym_rf_assign_continuation_execution_mode_conditional:
  rf_B ==>
  !cp. rf_L allow_own prog env own lo code_ok /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel s st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?st' ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra (s' with vs_inst_idx := k)) ps'.ps_stack stk' /\
    st'.as_memory = st.as_memory /\ s'.vs_memory = s.vs_memory /\
    venom_asm_terminal_rel (s' with vs_inst_idx := k) st' /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    bridge_core lo code_ok st' ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  disch_then (fn bundle => mk_asm "assign"
    (MP (SPEC_ALL sym_rf_assign_plan_execution_mode_conditional) bundle)) >>
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  asm_x "assign" drule_all >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_plan_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  `st'.as_memory = st.as_memory /\ venom_asm_terminal_rel s st'` by
    gvs[venom_asm_terminal_rel_def] >>
  drule_all sym_assign_success_state >> strip_tac >>
  qexistsl [`st'`,`ss'`,`stk'`,`top'`] >>
  gvs[sym_plan_stack_rel_inst_idx, sym_terminal_rel_inst_idx, venom_asm_terminal_rel_def] >>
  conj_tac >- (qexists `m` >> simp[]) >> first_assum ACCEPT_TAC
QED
