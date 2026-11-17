(* Failing assertions: prepared word stack and terminal suffixes in either mode. *)
Theory symControlAbortConditionalOwn
Ancestors
  symControlTerminalSafetyOwn symControlJumpOwn symFrameControlFacts
  asmSymBridge[qualified,ignore_grammar] codegenSymRel codegenSymOwnRel
  asmSplice asmSymSem frameRel contextCodegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  frameViewFacts genBlockSim genFrameSim fnFrameDeepAbort stackPlanCfgIrrelevance

(* Syntax abbreviations only, with the same structural interface as preparation. *)
val conditional_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", conditional_bridge_core_tm);
val _ = Parse.temp_overload_on ("control_frame", ``\lo code_ok p ctx cp fn ret srest labs0 ps cs ss.
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p)``);

Theorem sym_assert_unreachable_suffix_terminal_mode:
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel l; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel l] /\
  ss.sym_stack = Val 0w :: stk ==>
  sym_terminal (sym_steps_mode allow_own p env own 3 ss)
Proof
  strip_tac >>
  `sym_terminal (sym_steps p env 3 ss)` suffices_by
    metis_tac[sym_steps_mode_nonbad, sym_terminal_def] >>
  fs[stackOpSimTheory.asm_block_at_cons] >>
  rewrite_tac[numLib.num_CONV ``3:num``, arithmeticTheory.TWO,
              arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  simp[Once sym_step_def, sym_set_stack_def, asm_next_def] >>
  simp[Once sym_step_def, sym_step_op_def, sym_jumpi_def] >>
  simp[sym_set_stack_def, asm_next_def] >>
  simp[Once sym_step_def, sym_terminal_opcode_concrete] >>
  simp[sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
       asm_op_mem_reads_def, asmSemTheory.log_table_def, mem_labels_hit_def] >>
  simp[SRULE [asm_step_def] stackOpAsmSimTheory.asm_step_invalid,
       sym_lift_def, sym_terminal_def]
QED

Theorem sym_assert_zero_iszero_mode:
  asm_block_at p ss.sym_base.as_pc [AsmOp "ISZERO"] /\
  ss.sym_stack = Val 0w :: stk ==>
  sym_steps_mode allow_own p env own 1 ss = SymOK
    (ss with <|sym_base := asm_next (ss.sym_base with as_stack := []);
               sym_stack := Val 1w :: stk|>)
Proof
  strip_tac >> irule sym_steps_mode_ok >>
  fs[stackOpSimTheory.asm_block_at_cons] >>
  rewrite_tac[arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  drule asmSpliceTheory.sym_step_iszero_val >>
  disch_then (qspecl_then [`p`, `env`] assume_tac) >> simp[]
QED

Theorem sym_assert_revert_postamble_steps_mode:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp revert_postamble) ==>
  sym_terminal (sym_steps_mode allow_own p env own 4 ss)
Proof
  strip_tac >>
  `sym_terminal (sym_steps p env 4 ss)` suffices_by
    metis_tac[sym_steps_mode_nonbad, sym_terminal_def] >>
  fs[revert_postamble_def, execute_plan_def, exec_stack_op_def,
     stackOpSimTheory.asm_block_at_cons] >>
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              arithmeticTheory.TWO, arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  `word_of_bytes F (0w:bytes32) (REVERSE (encode_num_bytes_fuel 32 0)) = 0w`
    by EVAL_TAC >>
  simp[Once sym_step_def, sym_lift_def, asm_step_def, asm_next_def] >>
  simp[Once sym_step_def, sym_lift_def, asm_step_def, asm_next_def] >>
  simp[Once sym_step_def] >>
  simp[sym_step_op_def, asmSemTheory.dup_table_def, asmSemTheory.swap_table_def,
       sym_dup_def, sym_set_stack_def, asm_next_def] >>
  simp[Once sym_step_def, sym_terminal_opcode_concrete] >>
  simp[sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
       sval_val_def, asm_op_mem_reads_def, asmSemTheory.log_table_def,
       mem_labels_hit_def, in_mem_range_def] >>
  simp[SRULE [asm_step_def] stackOpAsmSimTheory.asm_step_revert,
       asm_revert_op_def, sym_lift_def, sym_terminal_def]
QED

Theorem sym_assert_suffix_terminal_mode:
  asm_block_at p ss.sym_base.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] /\
  ss.sym_stack = Val 0w :: stk /\
  sym_jump_dest p (Lab "revert" 0) = SOME pc /\
  asm_block_at p pc (execute_plan fmp revert_postamble) ==>
  sym_terminal (sym_steps_mode allow_own p env own 7 ss)
Proof
  strip_tac >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "ISZERO"]` by
    fs[stackOpSimTheory.asm_block_at_cons] >>
  drule_all sym_assert_zero_iszero_mode >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  `sym_steps_mode allow_own p env own 2
     (ss with <|sym_base := asm_next (ss.sym_base with as_stack := []);
                sym_stack := Val 1w :: stk|>) = SymOK
     (ss with <|sym_base := (ss.sym_base with as_stack := []) with as_pc := pc;
                sym_stack := stk|>)` by
    (qspec_then `ss with <|sym_base := asm_next (ss.sym_base with as_stack := []);
                          sym_stack := Val 1w :: stk|>` mp_tac
       (GEN ``ss:sym_state``
         (Q.INST [`l` |-> `"revert"`, `w` |-> `1w:bytes32`]
           sym_jnz_suffix_nonzero_mode)) >>
     simp[asm_next_def] >>
     disch_then irule >> fs[stackOpSimTheory.asm_block_at_cons]) >>
  `sym_terminal (sym_steps_mode allow_own p env own 4
     (ss with <|sym_base := (ss.sym_base with as_stack := []) with as_pc := pc;
                sym_stack := stk|>))` by
    (irule sym_assert_revert_postamble_steps_mode >> simp[] >> metis_tac[]) >>
  once_rewrite_tac[GSYM (numLib.REDUCE_CONV ``1 + (2 + 4):num``)] >>
  asm_rewrite_tac[sym_steps_mode_add] >> simp[] >> gvs[]
QED

Theorem sym_conditional_abort_zero_stack_mode:
  !cp.
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\ eval_operand cond vs = SOME 0w /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  control_frame lo code_ok prog ctx cp fn ret srest labs0 arranged
    (mid with as_stack := mid.as_stack ++ rest) ss ==>
  ?stk. ss.sym_stack = Val 0w :: stk
Proof
  gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `eval_operands (REVERSE (compute_operands inst))
      (frame_view fn ra vs with vs_memory := m) = SOME [0w]` by
    (`eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := m) =
        eval_operands inst.inst_operands vs` by
       (irule fnFrameTerminalAbortTheory.abort_operands_frame_view >>
        simp[] >> metis_tac[listTheory.MEM]) >>
     Cases_on `inst.inst_opcode = ASSERT` >>
     gvs[compute_operands_def, python_stack_operands_def,
         ir_specific_operand_order_def, eval_operands_def]) >>
  `!op sv. MEM op (compute_operands inst) /\ op_kind_ok fn ret op sv ==>
      ?w. sv = Val w` by
    (rpt strip_tac >> irule terminal_operand_word_kind_mode >>
     goal_assum (drule_at Any) >>
     qexistsl [`allow_own`, `ctx`, `inst`] >>
     gvs[listTheory.EVERY_MEM, listTheory.MEM] >> metis_tac[]) >>
  `!op. MEM op (compute_operands inst) ==>
     eval_operand op (frame_view fn ra vs with vs_memory := m) =
     operand_val (frame_view fn ra vs with vs_memory := m) lo op` by
    simp[venomMemPropsTheory.eval_operand_with_memory,
         genFrameSimTheory.operand_val_memory_update] >>
  drule_all arranged_word_prepared_symbolic_stack_core >> simp[]
QED

Theorem sym_conditional_abort_inversion:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?cond. inst.inst_operands = [cond] /\ eval_operand cond vs = SOME 0w
Proof
  metis_tac[genBlockSimTheory.step_inst_assert_abort,
            genBlockSimTheory.step_inst_assert_unreachable_abort]
QED

(* Preparation is a producer interface, not a second planner proof. The local
   terminal join discharges this complete generalized prefix statement. *)
Theorem sym_abort_conditional_terminal_exists_mode_kernel:
  !allow_own code_ok own fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss a vs'.
  (!base inst lv dfg cfg fn nl halting term label ps ops final r cplan
      cond ctx ra rest mem0 vs st ret srest labs0 ss.
    (!n cs ss ss'. bridge_core lo code_ok cs ss /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        bridge_core lo code_ok cs' ss') /\
    (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
    inst_wf inst /\ inst.inst_operands = [cond] /\
    generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
    final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!op at. MEM op (compute_operands inst) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
      operand_equiv dfg op at ==>
      operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
    asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
    asm_static_wf prog /\
    control_frame lo code_ok prog ctx cplan fn ret srest labs0 ps st ss ==>
    ?pre arranged mid ss_mid suffix.
      ops = pre ++ suffix /\
      ((inst.inst_opcode = ASSERT /\
        suffix = [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]) \/
       (inst.inst_opcode = ASSERT_UNREACHABLE /\ ?lbl.
        suffix = [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl])) /\
      arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
      asm_steps lo (build_offset_to_pc prog) prog
        (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
        AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
      venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
      venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
      asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp suffix) /\
      sym_steps_mode allow_own prog env own
        (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK ss_mid /\
      control_frame lo code_ok prog ctx cplan fn ret srest labs0 arranged
        (mid with as_stack := mid.as_stack ++ rest) ss_mid) /\
  (!l off pc. MEM (AsmLabel l) prog /\ FLOOKUP lo l = SOME off /\
    FLOOKUP (build_offset_to_pc prog) off = SOME pc ==>
    sym_jump_dest prog (Lab l 0) = SOME pc) /\
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  o2pc = build_offset_to_pc prog /\
  inst.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cp inst vs /\ opaque_use_ok fn /\
  ~is_param_opcode inst.inst_opcode /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ inst_wf inst /\
  (inst.inst_opcode = ASSERT ==>
   ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
            FLOOKUP o2pc off = SOME pc /\
            asm_block_at prog pc (execute_plan cp.cp_initial_fmp revert_postamble)) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) next_liveness ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
           EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
           ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                 FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
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
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
  generate_inst_plan liveness dfg cfg fn inst
    next_liveness is_halting next_is_term bb_label ps = SOME (ops, ps') /\
  asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  (inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog) /\
  control_frame lo code_ok prog ctx cp fn ret srest labs0 ps as ss /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) ==>
  ?m. sym_terminal (sym_steps_mode allow_own prog env own m ss)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all sym_conditional_abort_inversion >> strip_tac >>
  `ssa_form fn` by fs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `label_positions_ok inst` by
    metis_tac[unitShapeDefsTheory.fn_shape_ok_def,
              unitShapeDefsTheory.inst_shape_ok_def, listTheory.EVERY_MEM] >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (qpat_x_assum `EVERY (\op. op <> dead_stack_marker /\ _) _` mp_tac >>
     simp[listTheory.EVERY_CONJ]) >>
  `compute_operands inst = [cond]` by
    (qpat_x_assum `inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE`
       mp_tac >> strip_tac >>
     simp[compute_operands_def, python_stack_operands_def,
          ir_specific_operand_order_def]) >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs as` >>
  Q.SUBGOAL_THEN
    `control_frame lo code_ok prog ctx cplan fn ret srest labs0 ps as ss` assume_tac
  >- asm_rewrite_tac[] >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [generate_inst_plan_cfg_unit]) >>
  qpat_x_assum `!base inst lv dfg fn nl halting term label ps ops final r cplan cond ctx ra rest mem0 vs st ret srest labs0 ss. _`
    (drule_at_then (Pat `inst_wf _`)
      (drule_at_then (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`) mp_tac)) >>
  disch_then (drule_at_then (Pat `generate_inst_plan`) mp_tac) >>
  disch_then (drule_at_then (Pat `generated_plan_state_wf_marked`) mp_tac) >>
  disch_then (drule_at_then (Pat `MEM _ _.cp_regions`) mp_tac) >>
  disch_then (drule_at_then (Pat `_.inst_operands = _`) mp_tac) >>
  asm_rewrite_tac[] >>
  disch_then (qspecl_then [`ret`, `srest`, `labs0`, `ss`] mp_tac) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choose_then `pre` (qx_choose_then `arranged`
    (qx_choose_then `mid` (qx_choose_then `ss_mid`
      (qx_choose_then `suffix` strip_assume_tac))))) >>
  `arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ compute_operands inst` by gvs[] >>
  drule_all sym_conditional_abort_zero_stack_mode >> strip_tac >>
  `ss_mid.sym_base.as_pc = mid.as_pc` by
    (drule asmSymBridgeTheory.asm_sym_rel_core_pc >> simp[]) >>
  reverse (Cases_on `inst.inst_opcode = ASSERT`)
  >- (`sym_terminal (sym_steps_mode allow_own prog env own 3 ss_mid)` by
        (irule sym_assert_unreachable_suffix_terminal_mode >>
         gvs[execute_plan_def, exec_stack_op_def] >> metis_tac[]) >>
      qexists `LENGTH (execute_plan cp.cp_initial_fmp pre) + 3` >>
      asm_rewrite_tac[sym_steps_mode_add] >> simp[]) >>
  `?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
     FLOOKUP o2pc off = SOME pc /\
     asm_block_at prog pc (execute_plan cp.cp_initial_fmp revert_postamble)` by metis_tac[] >>
  `sym_jump_dest prog (Lab "revert" 0) = SOME pc` by metis_tac[] >>
  `sym_terminal (sym_steps_mode allow_own prog env own 7 ss_mid)` by
    (irule sym_assert_suffix_terminal_mode >>
     gvs[execute_plan_def, exec_stack_op_def] >> metis_tac[]) >>
  qexists `LENGTH (execute_plan cp.cp_initial_fmp pre) + 7` >>
  asm_rewrite_tac[sym_steps_mode_add] >> simp[]
QED
