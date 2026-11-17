(* Unconditional own-mode terminal interfaces. *)
Theory symControlTerminalDischargeOwn
Ancestors symFrameControlOwn symControlTerminalOwn asmSymModeOwn asmSymBridge
  codegenSymRel codegenSymOwnRel spillWordBounds

val result_rel = mk_var ("R", type_of ``asm_sym_rel p env``);
val result_body = subst [``asm_sym_rel p env`` |-> result_rel]
  (lhs (concl asm_sym_step_rel_core_canonical));
val result_vars = result_rel :: List.map (fn name =>
  List.find (fn v => fst (dest_var v) = name) (free_vars result_body)
  |> valOf) ["sr", "cr"];
val _ = Parse.temp_overload_on
  ("bridge_result", list_mk_abs (result_vars, result_body));

Theorem sym_terminal_transfer_own:
  asm_static_wf prog /\ code_labels_agree prog lo ==>
  !cs ss ai cr.
    asm_sym_rel_own lo prog env own cs ss /\ asm_block_at prog cs.as_pc [ai] /\
    asm_step lo (build_offset_to_pc prog) ai cs = cr /\
    (!e. (if allow_own then sym_step_own prog env own ai ss
          else sym_step prog env ai ss) <> SymBad e) /\
    ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
    bridge_result (asm_sym_rel_own lo prog env own)
      (if allow_own then sym_step_own prog env own ai ss
       else sym_step prog env ai ss) cr
Proof
  rpt strip_tac >>
  `MEM ai prog` by metis_tac[asm_block_at_member, listTheory.MEM] >>
  metis_tac[asm_sym_inst_step_mode]
QED

Theorem sym_halt_frame_sim_deep_own:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs st ops ps' r ra rest mem0
   env ret srest labs0 ss allow_own own.
    code_labels_agree prog lo /\
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
    asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps st ss ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n out. asm_steps lo o2pc prog n st = AsmHalt out /\
        venom_asm_terminal_rel vs' out /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  drule sym_terminal_transfer_own >> simp[] >> disch_tac >>
  qx_gen_tac `vs'` >> strip_tac >>
  drule_at (Pat `generated_plan_state_wf_marked`)
    (GEN_ALL (SRULE [asm_sym_rel_core_own]
      (Q.INST [`code_ok` |->
        `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
        (SPEC_ALL sym_halt_frame_sim_deep_mode_conditional)))) >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `generate_inst_plan`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok`)) >> simp[] >>
  disch_then (qspecl_then [`r`, `labs0`, `fuel`, `vs'`] mp_tac) >>
  gvs[] >> disch_then irule >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem sym_abort_frame_sim_deep_own:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss allow_own own.
    code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\ inst.inst_opcode <> INVOKE /\
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
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  drule sym_terminal_transfer_own >> simp[] >> disch_tac >>
  `!l off pc. MEM (AsmLabel l) prog /\ FLOOKUP lo l = SOME off /\
      FLOOKUP (build_offset_to_pc prog) off = SOME pc ==>
      sym_jump_dest prog (Lab l 0) = SOME pc` by
    metis_tac[sym_code_label_dest_reloc] >>
  map_every qx_gen_tac [`a`, `vs'`] >> strip_tac >>
  drule_at (Pat `generated_plan_state_wf_marked`)
    (GEN_ALL (SRULE [asm_sym_rel_core_own]
      (Q.INST [`code_ok` |->
        `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
        (SPEC_ALL sym_abort_frame_sim_deep_mode_conditional)))) >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `generate_inst_plan`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok`)) >> simp[] >>
  disch_then (qspecl_then [`r`, `labs0`, `fuel`, `a`, `vs'`] mp_tac) >>
  gvs[] >> disch_then irule >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[]) >>
  asm_rewrite_tac[]
QED
