(* Forwarded-revert continuations, shared by both symbolic execution modes. *)
Theory symControlForwardContinuationOwn
Ancestors
  symControlForwardSourceFacts symControlPreparedTerminalOwn symControlForwardStackOwn symControlForwardPrepareOwn symControlForwardCopyExecutionOwn symControlTerminalSafetyOwn
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

Theorem sym_rf_strict_suffix_abort_mode_conditional:
  rf_B ==>
  !k s st ps stk ops ps_end ss top.
  rf_L allow_own prog env own lo code_ok /\ rf_T allow_own prog env own lo code_ok /\
  o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ i < k /\ k <= j /\ s.vs_inst_idx = k /\
  LENGTH (get_params bb.bb_instructions) <= k /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [cdop;csop;czop] /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] cdop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] czop) = SOME sz /\
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\
  rf_spills_separated ps /\ rf_value_inv fn ra bb j lo entry k s /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel s st /\
  TAKE (w2n sz) (DROP (w2n dst) s.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (k - LENGTH (get_params bb.bb_instructions)) (DROP k bb.bb_instructions)
    ps = SOME (ops,ps_end) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ bridge_core lo code_ok st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b) /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  exec_block fuel ctx bb s = Abort a s_end ==>
  a = Revert_abort /\
  ?n out. asm_steps lo o2pc prog n st = AsmRevert out /\
    venom_asm_terminal_rel s_end out /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  disch_then (fn bundle => let
    fun typed_cfg th = let
      val cfg = List.find (fn v => fst (dest_var v) = "cfg") (free_vars (concl th))
        |> valOf
      val target = type_of ``cfg_analyze fn``
    in INST_TYPE (match_type (type_of cfg) target) th end
  in
    markerLib.hide_tac "suffix" (GEN_ALL (MP (typed_cfg sym_rf_suffix_revert_abort_mode_conditional) bundle)) >>
    markerLib.hide_tac "assign" (GEN_ALL (MP (typed_cfg sym_rf_assign_continuation_execution_mode_conditional) bundle))
  end) >>
  measureInduct_on `j - k` >> rpt gen_tac >> strip_tac >> disch_tac >>
  `i <= k` by decide_tac >>
  `?inst. get_instruction bb k = SOME inst` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_instruction_exists >>
     qexistsl [`i`,`j`] >> simp[]) >>
  `MEM inst (fn_insts fn)` by
    (irule allocaRemapSSATheory.mem_fn_insts_intro >> qexists `bb` >>
     conj_tac >- (drule livenessTransferProofsTheory.lookup_block_mem >> simp[]) >>
     qpat_x_assum `get_instruction bb k = SOME inst` mp_tac >>
     simp[get_instruction_def] >> strip_tac >>
     qpat_x_assum `_ = inst` (SUBST1_TAC o SYM) >>
     irule listTheory.EL_MEM >> first_assum ACCEPT_TAC) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_instruction_opcode >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_instruction_shape >> strip_tac >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule fnFrameStepsRevertForwardTheory.rf_suffix_instruction_no_labels >>
     qexistsl [`bb`,`i`,`k`] >> simp[]) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >>
     qpat_x_assum `rf_value_inv _ _ _ _ _ _ _ _` mp_tac >>
     simp[fnFrameStepsRevertForwardTheory.rf_value_inv_def] >> disch_then irule >>
     irule fnFrameStepsRevertForwardTheory.rf_live_use_current >>
     simp[] >> qexists `inst` >> simp[]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule fnFrameStepsRevertForwardTheory.rf_live_use_current >> simp[]) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_block_plan_step >> strip_tac >>
  `generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
     (cfg_analyze fn) fn inst
     (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) (bb_is_halting bb)
     (case DROP (SUC k) bb.bb_instructions of
        [] => F | next_i::tail => is_terminator next_i.inst_opcode)
     bb.bb_label ps = (step_ops,ps1)` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_regular_plan_result >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl [`bb`,`i`,`j`,`k`] >> simp[]) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp step_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp step_ops))
     (execute_plan initial_fmp rest_ops)` by
    (qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
     simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append]) >>
  `!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops` by
    fs[listTheory.MEM_APPEND] >>
  Cases_on `k = j` >- suspend "revert" >>
  suspend "assign"
QED

Resume sym_rf_strict_suffix_abort_mode_conditional[revert]:
  pop_last_assum kall_tac >>
  qpat_x_assum `k = j` SUBST_ALL_TAC >>
  `inst.inst_opcode = REVERT /\ inst.inst_outputs = []` by gvs[] >>
  `?dop zop. inst.inst_operands = [dop;zop]` by
    gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  `operand_val (frame_view fn ra s) lo dop = SOME dst /\
   operand_val (frame_view fn ra s) lo zop = SOME sz` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_revert_range >>
     simp[] >> qexistsl [`bb`,`cdop`,`copy`,`csop`,`czop`,`entry`,`i`,`j`,`inst`] >> simp[]) >>
  `step_inst fuel ctx inst s = Abort a s_end` by
    (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
     gvs[Once exec_block_def, is_terminator_def, AllCaseEqs()]) >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok st ss` assume_tac
  >- (simp[] >> conj_tac >- (qexists `m` >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _` drule >> simp[]) >>
  markerLib.use_hidden_assum "suffix" drule >>
  rpt (disch_then drule) >>
  disch_then (qspecl_then [`top`,`srest`,`ret`,`cplan`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _` drule >> simp[])) >> strip_tac >>
  simp[] >> qexistsl [`LENGTH (execute_plan initial_fmp step_ops)`,`out`] >> gvs[]
QED

Resume sym_rf_strict_suffix_abort_mode_conditional[assign]:
  `k < j /\ inst.inst_opcode = ASSIGN` by gvs[] >>
  `?rhs out. inst.inst_operands = [rhs] /\ inst.inst_outputs = [out]` by (simp[]) >>
  `~is_label_operand rhs` by fs[] >>
  drule_all sym_assign_block_abort_continuation >> strip_tac >>
  `!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI` by
    (match_mp_tac (GEN_ALL symControlForwardRunOwnTheory.sym_rf_future_non_phi) >>
     qexists `i` >> simp[]) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_success_invariants >> strip_tac >>
  `is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled` by
    (strip_tac >> first_x_assum irule >>
     simp[compute_operands_def, python_stack_operands_def]) >>
  `operand_val (frame_view fn ra s) lo rhs =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs)` by
    (first_x_assum irule >> simp[compute_operands_def, python_stack_operands_def]) >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok st ss` assume_tac
  >- (simp[] >> conj_tac >- (qexists `m` >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _` drule >> simp[]) >>
  markerLib.use_hidden_assum "assign"
    (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  rpt (disch_then drule) >>
  disch_then (qspecl_then [`top`,`srest`,`ret`,`SUC k`,`cplan`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _` drule >> simp[])) >>
  strip_tac >>
  `!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops` by
    fs[listTheory.MEM_APPEND] >>
  `asm_block_at prog st'.as_pc (execute_plan initial_fmp rest_ops)` by
    (qpat_x_assum `st'.as_pc = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))` by
    (`ss'.sym_mem_labels = ss.sym_mem_labels` by
      (rewrite_tac[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM] >> first_assum ACCEPT_TAC) >> simp[]) >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok st' ss'` assume_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qexists `m'` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  `j - SUC k < j - k` by decide_tac >>
  qpat_x_assum `!y. j - y < j - k ==> _`
    (qspec_then `SUC k` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `s' with vs_inst_idx := SUC k` mp_tac) >>
  disch_then (qspec_then `st'` mp_tac) >>
  disch_then (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`stk'`,`ss'`,`top'`] mp_tac) >>
  (impl_tac >- (pure_rewrite_tac[GSYM CONJ_ASSOC] >>
    conj_tac >- first_assum (ACCEPT_TAC o PURE_REWRITE_RULE[GSYM CONJ_ASSOC]) >>
    conj_tac >- first_assum (ACCEPT_TAC o PURE_REWRITE_RULE[GSYM CONJ_ASSOC]) >> simp[] >>
    rpt strip_tac >>
    qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _` drule >> simp[])) >>
  strip_tac >> simp[] >>
  qexistsl [`LENGTH (execute_plan initial_fmp step_ops) + n`, `out'`] >>
  conj_tac
  >- (qpat_assum `asm_steps _ _ _ _ st = AsmOK _`
        (mp_then Any (qspec_then `n` mp_tac) stackOpSimTheory.asm_steps_add_ok) >> gvs[]) >>
  simp[sym_steps_mode_add]
QED

Finalise sym_rf_strict_suffix_abort_mode_conditional

Theorem sym_rf_entry_success_terminal_mode_conditional:
  rf_B ==>
  !cp.
  rf_L allow_own prog env own lo code_ok /\ rf_T allow_own prog env own lo code_ok /\
  o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i < j /\
  LENGTH (get_params bb.bb_instructions) <= i /\
  get_instruction bb i = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\
  rf_spills_separated ps /\
  rf_value_inv fn ra bb j lo (frame_view fn ra vs) i vs /\
  rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs /\
  (!op. rf_live_use bb i j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn inst (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
    halting term bb.bb_label ps = (step_ops,ps1) /\
  (!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  step_inst fuel ctx inst vs = OK copied /\
  exec_block fuel ctx bb vs = Abort a vs_end /\
  asm_steps lo (build_offset_to_pc prog) prog
    (LENGTH (execute_plan fmp step_ops)) ast = AsmOK out /\
  out.as_pc = ast.as_pc + LENGTH (execute_plan fmp step_ops) /\
  out.as_stack = stk_out ++ rest /\
  plan_stack_rel lo (frame_view fn ra copied) ps1.ps_stack stk_out /\
  venom_asm_terminal_rel copied out /\
  TAKE (w2n sz) (DROP (w2n dst) copied.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (SUC i - LENGTH (get_params bb.bb_instructions)) (DROP (SUC i) bb.bb_instructions)
    ps1 = SOME (rest_ops,ps_end) /\
  (!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops) /\
  asm_block_at prog (ast.as_pc + LENGTH (execute_plan fmp step_ops))
    (execute_plan fmp rest_ops) /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\
  sym_steps_mode allow_own prog env own (LENGTH (execute_plan fmp step_ops)) ss = SymOK ss_out /\
  bridge_core lo code_ok out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps1.ps_stack) top_out /\
  (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
  ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  ?n ast_end.
    ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
    venom_asm_terminal_rel vs_end ast_end /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  disch_then (fn bundle => markerLib.hide_tac "suffix"
    (GEN_ALL (MP sym_rf_strict_suffix_abort_mode_conditional bundle))) >>
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `i <= j` by decide_tac >>
  drule_all sym_rf_abort_source_success >> disch_tac >>
  `LENGTH (compute_operands inst) <= 16` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  drule sym_rf_entry_future_non_phi >> disch_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_suffix_copy_success_invariants >> strip_tac >>
  drule_all sym_rf_copy_normalized_range >> strip_tac >>
  `i < SUC i /\ SUC i <= j /\ LENGTH (get_params bb.bb_instructions) <= SUC i` by decide_tac >>
  `plan_stack_rel lo (frame_view fn ra (copied with vs_inst_idx := SUC i)) ps1.ps_stack stk_out /\
   venom_asm_terminal_rel (copied with vs_inst_idx := SUC i) out /\
   TAKE (w2n sz) (DROP (w2n dst) (copied with vs_inst_idx := SUC i).vs_memory) =
     TAKE (w2n sz) (DROP (w2n dst) out.as_memory)` by
    simp[sym_plan_stack_rel_inst_idx, sym_terminal_rel_inst_idx] >>
  `(copied with vs_inst_idx := SUC i).vs_inst_idx = SUC i` by simp[] >>
  `asm_block_at prog out.as_pc (execute_plan fmp rest_ops)` by
    (qpat_assum `out.as_pc = _` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok out ss_out` assume_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  markerLib.use_hidden_assum "suffix"
    (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  drule_all sym_rf_revert_runs_compose_mode >> strip_tac >>
  qexistsl [`LENGTH (execute_plan fmp step_ops) + n`, `out'`] >>
  ASM_SIMP_TAC bool_ss []
QED

(* The planner's unused cfg parameter is specialized before hiding its contract. *)

val rf_copy_entry_typed = let
  val th = sym_rf_entry_copy_execution_mode_conditional
  val cfg = valOf (List.find (fn v => fst (dest_var v) = "cfg")
    (free_vars (concl th)))
in INST_TYPE (match_type (type_of cfg) (type_of ``cfg_analyze fn``)) th end;
val _ = Parse.temp_overload_on ("rf_C", fst (dest_imp (concl rf_copy_entry_typed)));

Theorem sym_rf_entry_forward_abort_mode_conditional:
  rf_B ==> rf_C ==>
  !fuel ctx cp o2pc liveness dfg cfg fn bb i j ps vs ast ops
   ps_end ra rest mem0 a vs_end ret srest ss top.
    rf_L allow_own prog env own lo code_ok /\ rf_T allow_own prog env own lo code_ok /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ rf_spills_separated ps /\
    (!k inst op. i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    asm_static_wf prog /\ bridge_core lo code_ok ast ss /\
    ss.sym_stack = top ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
    exec_block fuel ctx bb vs = Abort a vs_end ==>
    ?n ast_end.
      ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
       (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
      venom_asm_terminal_rel vs_end ast_end /\
      sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  disch_then (fn bundle => markerLib.hide_tac "success"
    (GEN_ALL (MP sym_rf_entry_success_terminal_mode_conditional bundle))) >>
  disch_then (fn prep => markerLib.hide_tac "copy"
    (GEN_ALL (MP rf_copy_entry_typed prep))) >>
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_entry_copy_setup >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_copy_source_alignment >>
  disch_then (qspec_then `fuel` (qspec_then `ctx` assume_tac)) >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst)
    (live_vars_at liveness bb.bb_label (SUC i)) ps` >>
  rename1 `_ = (ins,prep)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) prep` >>
  rename1 `_ = (ros,arr)` >>
  qpat_x_assum `liveness = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  `!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops` by
    (gen_tac >> first_x_assum (qspec_then `off` mp_tac) >> simp[]) >>
  qabbrev_tac `copied = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` >>
  `copied = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` by simp[Abbr `copied`] >>
  `!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops` by
    (gen_tac >> first_x_assum (qspec_then `off` mp_tac) >> simp[]) >>
  `label_flow_own_ok ctx` by
    (qpat_assum `if allow_own then _ else _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `allow_own` >>
     simp[label_flow_ok_imp_label_flow_own_ok]) >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok ast ss` assume_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  markerLib.use_hidden_assum "copy"
    (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >>
  reverse (Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata`) >>
  pure_asm_rewrite_tac[COND_CLAUSES] >> strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst vs = _` mp_tac >>
  pure_asm_rewrite_tac[COND_CLAUSES] >> disch_tac >>
  qpat_x_assum `copied = write_memory_with_expansion _ _ _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]))
  >- suspend "fault" >> suspend "success"
QED

Resume sym_rf_entry_forward_abort_mode_conditional[fault]:
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  `i <= j` by decide_tac >>
  drule_all sym_rf_entry_fault_terminal_mode >> simp[]
QED

Resume sym_rf_entry_forward_abort_mode_conditional[success]:
  Q.SUBGOAL_THEN `bridge_core lo code_ok out ss_out` assume_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qexists `m` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  markerLib.use_hidden_assum "success"
    (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  rpt (disch_then drule) >> simp[] >>
  disch_then (qspecl_then [`top_out`, `srest`, `ret`, `cp'`] mp_tac) >>
  impl_tac >-
    (simp[] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i l d j. FLOOKUP ss_out.sym_mem_labels i = SOME (l,d,j) ==> _`
       (drule_then strip_assume_tac) >> simp[]) >> simp[]
QED

Finalise sym_rf_entry_forward_abort_mode_conditional

Theorem sym_revert_forward_frame_sim_deep_mode_conditional:
  rf_B ==> rf_C ==>
  !fuel ctx cp o2pc liveness dfg cfg fn bb i j base ps vs ast ops
   ps_end ra rest mem0 ret srest labs0 ss.
    rf_L allow_own prog env own lo code_ok /\ rf_T allow_own prog env own lo code_ok /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ generated_plan_state_wf_marked base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    asm_static_wf prog /\ bridge_core lo code_ok ast ss /\
    sym_kinds_ok cp fn ret srest ps ss /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) ==>
    !a vs_end. exec_block fuel ctx bb vs = Abort a vs_end ==>
    ?n ast_end.
      ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
       (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
      venom_asm_terminal_rel vs_end ast_end /\
      sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  disch_then (fn bundle => disch_then (fn prep => markerLib.hide_tac "entry"
    (GEN_ALL (MP (MP sym_rf_entry_forward_abort_mode_conditional bundle) prep)))) >>
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rpt gen_tac >> disch_tac >>
  drule rf_spills_separated_entry_marked >> disch_tac >>
  qpat_x_assum `sym_kinds_ok _ _ _ _ _ _` mp_tac >>
  simp[sym_kinds_ok_def] >> strip_tac >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok ast ss` assume_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  markerLib.use_hidden_assum "entry"
    (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >> simp[]
QED
