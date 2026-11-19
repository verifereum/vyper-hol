(* Relocated paired INVOKE entry, using the shared numeric entry seeds. *)
Theory symInvokeEntryOwn
Ancestors
  symInvokeEntryFacts codegenSymRel asmSymOwnStep codegenSymOwnRel asmSymBridge
  asmOwnCodeInvariant symFrameBoundaryPairing[qualified,ignore_grammar]

Theorem sym_invoke_frame_own_canonical:
  asm_static_wf p ==>
  (sym_frame_inv_own (SND (compute_label_offsets p)) p env own
     ctx cplan fn ret srest labs0 ps cs ss <=>
   sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\ cs.as_code = own)
Proof
  MATCH_ACCEPT_TAC symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own
QED

Theorem sym_invoke_canonical_lockstep:
  asm_static_wf p ==>
  !n cs ss ss'.
    asm_sym_rel_own (SND (compute_label_offsets p)) p env own cs ss /\
    sym_steps_mode F p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own (SND (compute_label_offsets p)) p env own cs' ss'
Proof
  simp[sym_steps_mode_def] >> rpt strip_tac >>
  irule symFrameBoundaryPairingTheory.asm_sym_legacy_steps_own >>
  simp[fnPlanPlaceRevertPostambleTheory.code_labels_agree_refl] >>
  HINT_EXISTS_TAC >> simp[]
QED

Theorem sym_invoke_prefix_pair_own:
  !allow_own lo o2pc p env own ctx cp fn ret srest labs0 ps cs ss r n cs' ss' ps'.
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss') /\
  o2pc = build_offset_to_pc p /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps cs ss /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  asm_steps lo o2pc p n cs = AsmOK cs' /\
  sym_steps_mode allow_own p env own n ss = SymOK ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rpt strip_tac >>
  `asm_sym_rel_own lo p env own cs' ss'` by
    (gvs[sym_frame_inv_own_def] >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[]) >>
  drule_all sym_frame_inv_own_region_transfer >> simp[]
QED

Theorem sym_invoke_selected_frame_prefix_own:
  !allow_own p env own ctx cp fn ret srest labs0 ps cs ss mid operands nl iops prepared
   dfg rops arranged base r lo o2pc.
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss') /\
  o2pc = build_offset_to_pc p /\
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at p cs.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) /\
  asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) cs =
    AsmOK mid ==>
  ?sms. sym_steps_mode allow_own p env own
          (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) ss = SymOK sms /\
        sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 arranged mid sms
Proof
  rpt strip_tac >>
  rename1 `sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 ps cs ss` >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  `sym_kinds_ok cplan fn ret srest ps ss /\
   asm_block_at p ss.sym_base.as_pc
     (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[sym_frame_inv_own_def, asm_sym_rel_own_def] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
   plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps` by
    metis_tac[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
              deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  drule_all symInvokeEntryFactsTheory.sym_invoke_selected_prefix_sim_marked >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  goal_assum (drule_at Any) >>
  drule_all sym_invoke_prefix_pair_own >> simp[]
QED

Theorem sym_invoke_call_entry_pair_own:
  !allow_own p env own lo o2pc mid sms cas ret_lbl nm.
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss') /\
  o2pc = build_offset_to_pc p /\ asm_sym_rel_own lo p env own mid sms /\
  asm_block_at p mid.as_pc
    [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"] /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas ==>
  ?scas. sym_steps_mode allow_own p env own 3 sms = SymOK scas /\
    asm_sym_rel_own lo p env own cas scas /\
    scas.sym_stack = Lab ret_lbl 0 :: sms.sym_stack /\
    scas.sym_mem_labels = sms.sym_mem_labels
Proof
  rpt strip_tac >>
  `?pc. INDEX_OF (AsmLabel nm) p = SOME pc` by
    (Cases_on `INDEX_OF (AsmLabel nm) p` >> gvs[listTheory.INDEX_OF_eq_NONE]) >>
  `asm_block_at p sms.sym_base.as_pc
     [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"]` by
    (gvs[asm_sym_rel_own_def] >> simp[]) >>
  drule_all symInvokeEntryFactsTheory.sym_invoke_call_packet >>
  disch_then (qspec_then `env` assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  gvs[] >> first_x_assum (drule_all_then strip_assume_tac) >> gvs[]
QED

Theorem sym_invoke_entry_symbolic_boundary_own:
  !allow_own p env own lo o2pc ctx cp fn ret srest labs0 arranged mid sms cas inst nm args
   saved_ops values saved rest ret_lbl fmp post n ss.
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss') /\
  o2pc = build_offset_to_pc p /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 arranged mid sms /\
  arranged.ps_stack = saved_ops ++ args /\
  mid.as_stack = values ++ saved ++ rest /\ LENGTH values = LENGTH args /\
  asm_block_at p mid.as_pc (execute_plan fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas /\
  sym_steps_mode allow_own p env own n ss = SymOK sms ==>
  ?scas saved_sym.
    sym_steps_mode allow_own p env own (n + 3) ss = SymOK scas /\
    sym_steps_mode allow_own p env own 3 sms = SymOK scas /\
    asm_sym_rel_own lo p env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val values ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) p
Proof
  rpt strip_tac >>
  rename1 `sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 arranged mid sms` >>
  `label_flow_own_ok ctx` by
    (Cases_on `allow_own` >> gvs[] >>
     metis_tac[label_flow_ok_imp_label_flow_own_ok]) >>
  `asm_sym_rel_own lo p env own mid sms /\ sym_kinds_ok cplan fn ret srest arranged sms` by
    gvs[sym_frame_inv_own_def] >>
  drule_all sym_invoke_arranged_stack_own >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_packet_block >> strip_tac >>
  drule_all sym_invoke_call_entry_pair_own >> strip_tac >>
  drule_all symInvokeEntryFactsTheory.sym_invoke_return_code_label >> strip_tac >>
  gvs[sym_kinds_ok_def, sym_steps_mode_add]
QED

Theorem sym_invoke_selected_entry_pair_own:
  !allow_own p env own ctx cp fn ret srest labs0 ps cs ss mid nl iops prepared dfg rops
   arranged base r lo o2pc inst nm arg_ops args saved rest ret_lbl post cas.
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss') /\
  o2pc = build_offset_to_pc p /\ fn_shape_ok fn /\ ssa_form fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  compute_operands inst = arg_ops /\
  EVERY (\op. ~is_label_operand op) arg_ops /\
  (!op. MEM op arg_ops /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE arg_ops nl ps = (iops,prepared) /\
  reorder_plan dfg arg_ops prepared = (rops,arranged) /\
  LENGTH arg_ops <= 16 /\ LENGTH arg_ops <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) arg_ops /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at p cs.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) /\
  asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) cs = AsmOK mid /\
  arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\ LENGTH args = LENGTH arg_ops /\
  asm_block_at p mid.as_pc (execute_plan cp.cp_initial_fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas ==>
  ?sms scas saved_sym.
    sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3)
      cs = AsmOK cas /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
    asm_sym_rel_own lo p env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) p
Proof
  rpt gen_tac >> strip_tac >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base` by
    metis_tac[allocMonoTheory.emit_input_plan_spill_base,
              allocMonoTheory.reorder_plan_spill_base] >>
  drule_all sym_invoke_selected_frame_prefix_own >> strip_tac >>
  `EVERY (\op. op <> dead_stack_marker) arg_ops` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `LENGTH (REVERSE args) = LENGTH arg_ops` by simp[] >>
  drule_all sym_invoke_entry_symbolic_boundary_own >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[blockSimHelpersTheory.asm_steps_compose_ok]
QED
