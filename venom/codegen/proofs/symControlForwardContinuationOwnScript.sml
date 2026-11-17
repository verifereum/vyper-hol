(* Forwarded-revert continuations, shared by both symbolic execution modes. *)
Theory symControlForwardContinuationOwn
Ancestors
  symControlPreparedTerminalOwn symControlForwardStackOwn symControlForwardPrepareOwn symControlForwardCopyExecutionOwn symControlTerminalSafetyOwn
  symFrameControlFacts codegenSymRel codegenSymOwnRel asmSymBridge[qualified,ignore_grammar]
  fnFrameStepsRevertForwardDeep asmSplice asmSpliceOwn asmSymOwnCode
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs symPlannerSim symShuffleSim asmSymPc codegenEncodingWf symEmitSim symControlForwardRunOwn

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

Theorem sym_rf_suffix_revert_abort_mode_conditional:
  rf_B ==>
  !cp.
  rf_L allow_own prog env own lo code_ok /\ rf_T allow_own prog env own lo code_ok /\
  o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = REVERT /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  a = Revert_abort /\
  ?out. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
    AsmRevert out /\ venom_asm_terminal_rel vs' out /\
    sym_terminal (sym_steps_mode allow_own prog env own (LENGTH (execute_plan initial_fmp ops)) ss)
Proof
  disch_then (fn bundle => mk_asm "prepare"
    (MP (SPEC_ALL sym_rf_suffix_preparation_execution_mode_conditional) bundle)) >>
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_suffix_revert_abort >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  simp[] >>
  Cases_on `emit_input_plan REVERT (compute_operands inst) nl ps` >>
  rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) ps1` >>
  rename1 `_ = (ros,ps2)` >>
  `compute_operands inst = [zop;dop]` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  `ops = ins ++ ros ++ [SOEmit "REVERT"]` by
    gvs[generate_regular_inst_plan_def, venomEffectsTheory.is_commutative_def,
        generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (ins ++ ros)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros)))
     [AsmOp "REVERT"]` by
    gvs[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
        stackOpSimTheory.asm_block_at_append, listTheory.APPEND_ASSOC] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)` by fs[listTheory.MEM_APPEND] >>
  `REVERT <> INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
   EVERY (\op. ~is_label_operand op) (compute_operands inst)` by gvs[] >>
  `EVERY is_simple_stack_op (ins ++ ros)` by
    metis_tac[fnFrameStepsRevertForwardTheory.spill_free_preparation_simple] >>
  `prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros)` by
    (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
     qexistsl [`dfg_build_function fn`, `compute_operands inst`, `nl`, `REVERT`,
               `ps1`, `ps2`] >>
     simp[] >> rpt strip_tac >> gvs[is_label_operand_def]) >>
  asm_x "prepare" drule_all >>
  disch_then (qx_choose_then `mid` (qx_choose_then `ss'`
    (qx_choose_then `stk'` (qx_choose_then `top'` assume_tac)))) >>
  ntac 7 (pop_assum (CONJUNCTS_THEN assume_tac)) >>
  pop_assum (CONJUNCTS_THEN2 (mk_asm "mid_core") strip_assume_tac) >>
  `asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmRevert out` by
    (qpat_assum `asm_steps _ _ _ _ st = AsmOK mid`
       (mp_then Any (qspec_then `1` mp_tac) stackOpSimTheory.asm_steps_add_ok) >>
     gvs[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC]) >>
  `asm_block_at prog mid.as_pc [AsmOp "REVERT"]` by metis_tac[] >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp "REVERT") mid = AsmRevert out` by
    (qpat_x_assum `asm_steps _ _ _ 1 mid = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asmSemTheory.asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  `ss'.sym_mem_labels = ss.sym_mem_labels` by
    metis_tac[finite_mapTheory.FLOOKUP_EXT] >>
  `sym_terminal (sym_steps_mode allow_own prog env own 1 ss')` by
    (`plan_stack_rel lo (frame_view fn ra vs)
        (stack_pop 2 ps2.ps_stack ++ [zop;dop]) stk' /\
      LIST_REL (op_kind_ok fn ret)
        (REVERSE (stack_pop 2 ps2.ps_stack ++ [zop;dop])) top'` by
       (qpat_assum `compute_operands inst = _` (fn eq =>
          qpat_assum `ps2.ps_stack = _`
            (fn th => pure_rewrite_tac[GSYM (SRULE [eq] th)])) >> simp[]) >>
     `~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))` by simp[] >>
     asm "mid_core" assume_tac >>
     first_assum (mp_tac o MATCH_MP (GEN_ALL sym_revert_prepared_terminal_forward_mode_conditional)) >>
     ntac 18 (disch_then (fn th => first_assum (mp_tac o MATCH_MP (GEN_ALL th)))) >>
     disch_then ACCEPT_TAC) >>
  `LENGTH (execute_plan initial_fmp ops) =
     LENGTH (execute_plan initial_fmp (ins ++ ros)) + 1` by
    simp[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC] >>
  asm_simp_tac (srw_ss()) [sym_steps_mode_add]
QED
