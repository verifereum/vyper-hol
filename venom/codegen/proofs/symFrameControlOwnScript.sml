(* Unconditional control interfaces at relocated offsets and fixed own code. *)
Theory symFrameControlOwn
Ancestors
  symControlPrefixOwn symControlScratchOwn symControlReorderOwn
  symControlReplayOwn symControlJumpOwn symControlRetOwn symControlTerminalOwn
  symControlForwardPrepareOwn symControlForwardCopyExecutionOwn
  symControlForwardRunOwn symControlForwardContinuationOwn
  asmSymModeOwn asmSymBridge codegenSymRel codegenSymOwnRel
  frameRel contextCodegenRel unitShapeDefs stackPlanGen stackPlanTypes
  planExec asmSem asmSymSem venomExecSemantics venomState venomInst dfgDefs

Theorem sym_selected_prefix_frame_sim_marked_own:
  !allow_own lo own opc operands nl ps iops prepared dfg selected rops
    arranged spillbase fn r cp p env ret srest labs0 ctx cs ss initial_fmp.
  code_labels_agree p lo /\
  opc <> INVOKE /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss = SymOK ss' /\
    sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  drule_all (SRULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`,
             `dfg` |-> `dfg_build_function fn`]
      (SPEC_ALL sym_selected_prefix_frame_sim_marked_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_code_label_dest_reloc:
  asm_static_wf p /\ code_labels_agree p lo /\
  MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
  sym_jump_dest p (Lab l 0) = SOME pc
Proof
  strip_tac >>
  `?i. INDEX_OF (AsmLabel l) p = SOME i` by
    metis_tac[listTheory.INDEX_OF_eq_NONE, optionTheory.option_CASES] >>
  drule_all asm_static_wf_code_label >> strip_tac >>
  gvs[fnPlanPlaceRevertPostambleTheory.code_labels_agree_def, sym_jump_dest_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem sym_jnz_frame_sim_deep_own:
  !allow_own own fuel cplan base.
  code_labels_agree p lo /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
  ~is_label_operand cond_op /\ inst.inst_outputs = [] /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
  (is_var_operand cond_op ==> IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
  eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\ operand_equiv dfg cond_op at ==>
    operand_val (frame_view fn ra vs) lo cond_op = operand_val (frame_view fn ra vs) lo at) /\
  cond_op <> dead_stack_marker /\
  (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword(:256) /\
  FLOOKUP (build_offset_to_pc p) off_nz = SOME pc_nz /\
  FLOOKUP lo if_z = SOME off_z /\ off_z < dimword(:256) /\
  FLOOKUP (build_offset_to_pc p) off_z = SOME pc_z /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
    next_is_term bb_label ps = SOME (ops, ps') /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf p /\ codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  MEM (AsmLabel if_nz) p /\ MEM (AsmLabel if_z) p /\
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 ps cs ss ==>
  !vs'. step_inst fuel ctx inst vs = OK vs' ==>
    ?n cs' ss'.
      asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      fn_frame_inv ctx cplan lo fn ra rest mem0 ps' vs' cs' /\
      ((vs' = jump_to if_nz vs /\ cs'.as_pc = pc_nz) \/
       (vs' = jump_to if_z vs /\ cs'.as_pc = pc_z)) /\
      sym_steps_mode allow_own p env own n ss = SymOK ss' /\
      sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 ps' cs' ss'
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  `!l off pc. MEM (AsmLabel l) p /\ FLOOKUP lo l = SOME off /\
    FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
    sym_jump_dest p (Lab l 0) = SOME pc` by
    metis_tac[sym_code_label_dest_reloc] >>
  qx_gen_tac `vs'` >> strip_tac >>
  drule_all (SRULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`,
             `dfg` |-> `dfg_build_function fn`]
      (SPEC_ALL sym_jnz_frame_sim_deep_mode_conditional))) >>
  strip_tac >> qexistsl [`n`, `cs'`, `ss'`] >> simp[]
QED

Theorem sym_prefix_ops_frame_sim_own:
  !allow_own lo own ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs r.
  code_labels_agree p lo /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\ context_spill_byte cp b) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv_own lo p env own ctx cp fn ret srest labs0
      (apply_prefix_ops initial_fmp lo ops ps) cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  drule_all (SRULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
      (SPEC_ALL sym_prefix_ops_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_spill_free_prefix_frame_sim_own:
  !allow_own lo own ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs.
  code_labels_agree p lo /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off. ~MEM (SOSpill off) ops) /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv_own lo p env own ctx cp fn ret srest labs0
      (apply_prefix_ops initial_fmp lo ops ps) cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_own_def] >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    metis_tac[asm_sym_steps_mode_sim] >>
  drule_all (SRULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
      (SPEC_ALL sym_spill_free_prefix_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED
