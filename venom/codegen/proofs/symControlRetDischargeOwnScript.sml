(* Relocated own-mode read-only preparation and return discharge. *)
Theory symControlRetDischargeOwn
Ancestors symFrameControlOwn symControlRetOwn symControlReplayOwn asmSymModeOwn
  asmSymBridge codegenSymRel codegenSymOwnRel fnFrameDeepRet

Theorem sym_read_only_selected_prefix_frame_sim_own:
  !allow_own lo own opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp p env ctx cp srest labs0 cs ss.
  code_labels_agree p lo /\
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  prefix_wf lo (LENGTH ps.ps_stack) (iops ++ rops) /\
  EVERY is_prefix_op (iops ++ rops) /\
  EVERY (\op. !l d. op <> SOPushOfst l d) (iops ++ rops) /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  drule_at (Pat `emit_input_plan`)
    (GEN_ALL (SRULE [asm_sym_rel_core_own]
      (Q.INST [`code_ok` |->
        `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
        (SPEC_ALL sym_read_only_selected_prefix_frame_sim_mode_conditional)))) >>
  disch_then (drule_at (Pat `reorder_plan`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok`)) >> simp[] >>
  disch_then (qspecl_then [`labs0`, `fmp`, `ctx`, `cs`] mp_tac) >>
  gvs[] >> (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `out` (qx_choose_then `sout` strip_assume_tac)) >>
  qexistsl [`out`, `sout`] >> simp[]
QED

Theorem sym_ret_frame_sim_deep_own:
  !allow_own own fuel ctx cp lo prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs cs ops final ra rest mem0 pc_ret
   env ret srest labs0 ss.
  code_labels_agree prog lo /\
  inst.inst_opcode = RET /\ MEM inst (fn_insts (reachable_fn fn)) /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  generated_plan_state_wf_marked base ps /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) next_liveness ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
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
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs cs /\
  (fn_has_retpc fn ==> FLOOKUP (build_offset_to_pc prog) (w2n ra) = SOME pc_ret) /\
  generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term bb_label ps =
    SOME (ops,final) /\ final.ps_stack = [] /\
  asm_block_at prog cs.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps cs ss ==>
  !rv vs'. step_inst fuel ctx inst vs = IntRet rv vs' ==>
    ?n out sout.
      asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK out /\
      out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
      context_memory_rel cp vs'.vs_memory out.as_memory /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        read_byte b out.as_memory = read_byte b mem0) /\ shared_state_rel vs' out /\
      sym_steps_mode allow_own prog env own n ss = SymOK sout /\
      asm_sym_rel_own lo prog env own out sout /\
      sout.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        FLOOKUP sout.sym_mem_labels b = FLOOKUP labs0 b) /\
      (!b. b IN FDOM sout.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  map_every qx_gen_tac [`rv`, `vs'`] >> strip_tac >>
  drule_at (Pat `generated_plan_state_wf_marked`)
    (GEN_ALL (SRULE [asm_sym_rel_core_own]
      (Q.INST [`code_ok` |->
        `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
        (SPEC_ALL sym_ret_frame_sim_deep_mode_conditional)))) >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `generate_inst_plan`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok`)) >> simp[] >>
  disch_then (qspecl_then [`pc_ret`, `labs0`, `fuel`] mp_tac) >>
  disch_then (qspecl_then [`rv`, `vs'`] mp_tac) >> simp[] >>
  (impl_tac >-
    (conj_tac
     >- (rpt gen_tac >> strip_tac >>
         drule_all (SRULE [sym_frame_inv_own_def]
           sym_read_only_selected_prefix_frame_sim_own) >>
         (simp[])) >>
     conj_tac
     >- (drule_at (Pat `generated_plan_state_wf_marked`)
           gen_ret_frame_sim_deep_exact_reloc >>
         disch_then (drule_at (Pat `fn_frame_inv`)) >>
         disch_then (drule_at (Pat `generate_inst_plan`)) >> simp[] >>
         disch_then (qspecl_then [`fuel`, `prog`, `pc_ret`] mp_tac) >>
         disch_then (qspecl_then [`rv`, `vs'`] mp_tac) >>
         simp[] >>
         (impl_tac >- asm_rewrite_tac[]) >>
         disch_then (qx_choose_then `out` strip_assume_tac) >>
         qexists_tac `out` >> simp[]) >>
     asm_rewrite_tac[])) >> simp[]
QED
