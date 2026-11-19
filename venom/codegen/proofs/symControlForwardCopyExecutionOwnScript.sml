(* Whole forwarded return-data copies, conditional only on preparation. *)
Theory symControlForwardCopyExecutionOwn
Ancestors
  symControlForwardCopyOwn asmSymBridge codegenSymRel codegenSymOwnRel symEmitSim
  fnFrameStepsRevertForward emitSim frameViewFacts
  stackPlanGen stackPlanTypes planExec asmSem asmSymSem frameRel
  contextCodegenRel unitShapeDefs dfgDefs asmSplice asmSpliceOwn asmSymOwnCode

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);

Theorem sym_rf_copy_success_execution_mode_conditional:
  (!cp fn ps inst dop sop zop nl ins ps1 ros ps2 lv cfg halting term lbl ops ps'
    entry ra vs stk st rest fmp ss top srest ret.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) (cfg:'cfg) fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  bridge_core lo code_ok st ss /\ ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop 3 ps2.ps_stack ++ [zop;sop;dop] /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    bridge_core lo code_ok mid ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)) ==>
  !cp.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) (cfg:'cfg) fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  w2n src + w2n sz <= LENGTH vs.vs_returndata /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?out ss_out stk_out top_out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK out /\
    out.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    out.as_stack = stk_out ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk_out /\
    venom_asm_terminal_rel vs' out /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp ops)) ss = SymOK ss_out /\
    bridge_core lo code_ok out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top_out /\
    (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  disch_then (mk_asm "prep") >>
  qx_gen_tac `cplan` >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all rf_suffix_copy_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` mp_tac) >> simp[] >> strip_tac >>
  rename1 `asm_steps _ _ _ (LENGTH (execute_plan fmp ops)) st = AsmOK out` >>
  rename1 `out.as_stack = stk_out ++ rest` >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok st ss` assume_tac
  >- (simp[] >> metis_tac[]) >>
  asm_x "prep" (fn prep =>
    if is_forall (concl prep) andalso is_imp (snd (strip_forall (concl prep)))
       andalso List.all (fn v => List.exists (fn n => fst (dest_var v) = n)
         ["lo", "code_ok", "prog", "allow_own", "env", "own"]) (free_vars (concl prep))
    then drule_all prep else FAIL_TAC "malformed preparation interface") >>
  disch_then (qx_choose_then `mid` (qx_choose_then `ss'`
    (qx_choose_then `stk_mid` (qx_choose_then `top_mid` assume_tac)))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `LENGTH (execute_plan fmp ops) = LENGTH (execute_plan fmp (ins ++ ros)) + 1` by
    simp[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC] >>
  `asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmOK out` by
    (qpat_assum `asm_steps _ _ _ _ st = AsmOK mid`
       (mp_then Any (qspec_then `1` mp_tac) stackOpSimTheory.asm_steps_add_ok) >>
     gvs[]) >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp "RETURNDATACOPY") mid = AsmOK out` by
    (qpat_x_assum `asm_steps _ _ _ 1 mid = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asmSemTheory.asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  `plan_stack_rel lo (frame_view fn ra vs)
     (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop]) stk_mid /\
   LIST_REL (op_kind_ok fn ret)
     (REVERSE (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop])) top_mid` by metis_tac[] >>
  `ss'.sym_mem_labels = ss.sym_mem_labels` by
    metis_tac[finite_mapTheory.FLOOKUP_EXT] >>
  `!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cplan b` by simp[] >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok mid ss'` assume_tac
  >- (simp[] >> metis_tac[]) >>
  drule_all sym_rf_copy_prepared_success_mode_core >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] strip_assume_tac) >>
  rename1 `sym_steps_mode _ _ _ _ 1 ss' = SymOK ss_out` >>
  rename1 `ss_out.sym_stack = top_out ++ srest` >>
  qexistsl [`out`, `ss_out`, `stk_out`, `top_out`] >>
  gvs[fnPlanPrefixTheory.release_dead_spills_stack, sym_steps_mode_add] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);

Theorem sym_rf_copy_fault_execution_mode_conditional:
  (!cp fn ps inst dop sop zop nl ins ps1 ros ps2 lv cfg halting term lbl ops ps'
    entry ra vs stk st rest fmp ss top srest ret.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) (cfg:'cfg) fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  bridge_core lo code_ok st ss /\ ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop 3 ps2.ps_stack ++ [zop;sop;dop] /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    bridge_core lo code_ok mid ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)) ==>
  !cp.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) (cfg:'cfg) fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  w2n src + w2n sz > LENGTH vs.vs_returndata /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmFault out /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) out /\
    sym_terminal (sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp ops)) ss)
Proof
  disch_then (mk_asm "prep") >>
  qx_gen_tac `cplan` >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all (SRULE [] (Q.INST [`vs'` |-> `write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs`] rf_suffix_copy_execution)) >>
  disch_then (qspec_then `build_offset_to_pc prog` mp_tac) >> simp[] >> strip_tac >>
  rename1 `asm_steps _ _ _ (LENGTH (execute_plan fmp ops)) st = AsmFault out` >>
  asm_x "prep" drule_all >>
  disch_then (qx_choose_then `mid` (qx_choose_then `ss'`
    (qx_choose_then `stk_mid` (qx_choose_then `top_mid` assume_tac)))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `LENGTH (execute_plan fmp ops) = LENGTH (execute_plan fmp (ins ++ ros)) + 1` by
    simp[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC] >>
  `asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmFault out` by
    (qpat_assum `asm_steps _ _ _ _ st = AsmOK mid`
       (mp_then Any (qspec_then `1` mp_tac) stackOpSimTheory.asm_steps_add_ok) >> gvs[]) >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp "RETURNDATACOPY") mid = AsmFault out` by
    (qpat_x_assum `asm_steps _ _ _ 1 mid = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asmSemTheory.asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  `dop <> dead_stack_marker /\ sop <> dead_stack_marker /\ zop <> dead_stack_marker` by
    (rpt strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  `?d s z residual. stk_mid = d :: s :: z :: residual /\
    operand_val (frame_view fn ra vs) lo dop = SOME d /\
    operand_val (frame_view fn ra vs) lo sop = SOME s /\
    operand_val (frame_view fn ra vs) lo zop = SOME z` by
    (irule asm_stack_top3_from_plan >> simp[] >>
     qexists `stack_pop 3 ps2.ps_stack` >> metis_tac[]) >>
  `mid.as_stack = dst :: src :: sz :: (residual ++ rest)` by
    metis_tac[optionTheory.SOME_11, listTheory.APPEND] >>
  `LIST_REL (op_kind_ok fn ret)
    (REVERSE (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop])) top_mid` by metis_tac[] >>
  drule_all sym_rf_copy_fault_stack_mode_core >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  qexists `out` >> simp[sym_steps_mode_add]
QED

Theorem sym_rf_entry_copy_execution_mode_conditional:
  (!cp fn ps inst dop sop zop nl ins ps1 ros ps2 lv cfg halting term lbl ops ps'
    entry ra vs stk st rest fmp ss top srest ret.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) (cfg:'cfg) fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  bridge_core lo code_ok st ss /\ ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop 3 ps2.ps_stack ++ [zop;sop;dop] /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    bridge_core lo code_ok mid ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)) ==>
  !cp.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) (cfg:'cfg) fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_own_ok ctx /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  if w2n src + w2n sz <= LENGTH vs.vs_returndata then
  (?out ss_out stk_out top_out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK out /\
    out.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    out.as_stack = stk_out ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk_out /\
    venom_asm_terminal_rel vs' out /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp ops)) ss = SymOK ss_out /\
    bridge_core lo code_ok out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top_out /\
    (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)))
  else
  (?out. asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmFault out /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) out /\
    sym_terminal (sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp ops)) ss))
Proof
  disch_tac >> gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs` by
    (irule rf_inventory_inv_entry >> gvs[]) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >> irule rf_inventory_inv_input_value >>
     qexists `ps` >> simp[]) >>
  Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata` >> simp[]
  >- (drule_all sym_rf_copy_success_execution_mode_conditional >> simp[]) >>
  `w2n src + w2n sz > LENGTH vs.vs_returndata` by simp[] >>
  drule_all sym_rf_copy_fault_execution_mode_conditional >> simp[]
QED
