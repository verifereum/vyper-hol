(* Terminal/GAS assembly: the single subject kernels supply the real proofs. *)
Theory symControlTerminalOwn
Ancestors
  symControlTerminalSafetyOwn symControlTerminalPrepareOwn symControlHaltOwn
  symControlAbortRegularOwn symControlAbortStaticOwn symControlAbortConditionalOwn
  symControlGasOwn symControlJumpOwn asmSymBridge[qualified,ignore_grammar]
  codegenSymRel codegenSymOwnRel fnFrameDeepAbort asmSplice asmSymOwnCode
  asmSem asmSymSem frameRel contextCodegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec venomExecSemantics venomInst venomState frameViewFacts
  genFrameSim emitSim opcodeClass

(* Parser-only abbreviations: no new logical definitions. *)
val terminal_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val terminal_bridge_result_tm = let
  val body = lhs (concl asmSymBridgeTheory.asm_sym_step_rel_core_canonical)
  val rel = ``asm_sym_rel p env``
  val r = mk_var ("R", type_of rel)
  val body = subst [rel |-> r] body
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars body) of
      [v] => v | _ => raise Fail ("missing result parameter " ^ n)
in list_mk_abs ([r, named "sr", named "cr"], body) end;
val _ = Parse.temp_overload_on ("bridge_core", terminal_bridge_core_tm);
val _ = Parse.temp_overload_on ("bridge_result", terminal_bridge_result_tm);
val _ = Parse.temp_overload_on ("control_frame", ``\lo code_ok p ctx cp fn ret srest labs0 ps cs ss.
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p)``);
val _ = Parse.temp_overload_on ("terminal_transfer", ``\lo code_ok p env own allow_own.
  !cs ss ai cr.
    bridge_core lo code_ok cs ss /\ asm_block_at p cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc p) ai cs = cr /\
    (!e. (if allow_own then sym_step_own p env own ai ss
          else sym_step p env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (bridge_core lo code_ok)
      (if allow_own then sym_step_own p env own ai ss else sym_step p env ai ss) cr``);

Theorem sym_halt_frame_sim_deep_mode_conditional:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs st ops ps' r ra rest mem0
   env ret srest labs0 ss allow_own own code_ok.
    (!n cs ss ss'. bridge_core lo code_ok cs ss /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        bridge_core lo code_ok cs' ss') /\
    terminal_transfer lo code_ok prog env own allow_own /\
    o2pc = build_offset_to_pc prog /\ inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\ opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
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
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term
      bb_label ps = SOME (ops, ps') /\
    asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    asm_static_wf prog /\ control_frame lo code_ok prog ctx cp fn ret srest labs0 ps st ss ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n out. asm_steps lo o2pc prog n st = AsmHalt out /\
        venom_asm_terminal_rel vs' out /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  ACCEPT_TAC symControlHaltOwnTheory.sym_halt_frame_sim_deep_mode_kernel
QED

Theorem sym_abort_terminal_counts_join_mode:
  ((a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert out) \/
   (a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault out)) /\
  venom_asm_terminal_rel vs out /\
  sym_terminal (sym_steps_mode allow_own prog env own m ss) ==>
  ?k fin.
    ((a = Revert_abort /\ asm_steps lo o2pc prog k st = AsmRevert fin) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog k st = AsmFault fin)) /\
    venom_asm_terminal_rel vs fin /\
    sym_terminal (sym_steps_mode allow_own prog env own k ss)
Proof
  strip_tac >> qexistsl [`n + m`, `out`] >>
  simp[stackOpSimTheory.asm_steps_add] >>
  metis_tac[sym_steps_terminal_extend_mode, arithmeticTheory.ADD_COMM]
QED

(* Match the conditional-branch interface, fixing the already supplied o2pc. *)
Theorem conditional_abort_prefix_interface[local]:
  !base inst lv dfg cfg fn nl halting term label ps ops final r cplan
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
        (mid with as_stack := mid.as_stack ++ rest) ss_mid
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.SUBGOAL_THEN `bridge_core lo code_ok st ss` assume_tac
  >- asm_rewrite_tac[] >>
  irule sym_conditional_abort_frame_prefix_deep_mode_conditional >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `fn_frame_inv`)) >>
  goal_assum (drule_at (Pat `generate_inst_plan`)) >>
  goal_assum (drule_at (Pat `generated_plan_state_wf_marked`)) >>
  goal_assum (drule_at (Pat `MEM _ _.cp_regions`)) >> asm_rewrite_tac[]
QED

Theorem sym_abort_frame_sim_deep_mode_conditional:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss allow_own own code_ok.
    (!n cs ss ss'. bridge_core lo code_ok cs ss /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        bridge_core lo code_ok cs' ss') /\
    terminal_transfer lo code_ok prog env own allow_own /\
    (!l off pc. MEM (AsmLabel l) prog /\ FLOOKUP lo l = SOME off /\
      FLOOKUP (build_offset_to_pc prog) off = SOME pc ==>
      sym_jump_dest prog (Lab l 0) = SOME pc) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
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
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term
      bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    asm_static_wf prog /\
    (inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog) /\
    control_frame lo code_ok prog ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  `?m. sym_terminal (sym_steps_mode allow_own prog env own m ss)` by
    (Cases_on `inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE`
     >- (drule_all (REWRITE_RULE [EQT_INTRO conditional_abort_prefix_interface]
           sym_abort_conditional_terminal_exists_mode_kernel) >> simp[]) >>
     Cases_on `vs.vs_call_ctx.cc_static /\
       MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL; LOG]`
     >- (qpat_x_assum `vs.vs_call_ctx.cc_static /\ _` strip_assume_tac >>
         Cases_on `inst.inst_opcode = LOG`
         >- (drule_all sym_abort_static_log_terminal_exists_mode_kernel >> simp[]) >>
         `MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL]` by
           gvs[listTheory.MEM] >>
         drule_all sym_abort_static_regular_terminal_exists_mode_kernel >> simp[]) >>
     `MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL]` by
       (drule opcodeClassTheory.step_inst_abort_opcodes >> fs[listTheory.MEM] >> metis_tac[]) >>
     drule_all sym_abort_regular_terminal_exists_mode_kernel >> simp[]) >>
  drule_all gen_inst_abort_frame_sim_deep_reloc >>
  disch_then (qx_choose_then `n` (qx_choose_then `out` strip_assume_tac)) >>
  irule sym_abort_terminal_counts_join_mode >> metis_tac[]
QED
