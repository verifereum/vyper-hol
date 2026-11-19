(* Discharged selected-prefix pairing at supplied offsets and fixed own code. *)
Theory symInstPrefixPairOwn
Ancestors symInstPrefixOwn asmSymModeOwn codegenSymRel asmSymBridge

Theorem sym_prepared_prefix_endpoint_own:
  asm_static_wf p /\ code_labels_agree p lo /\
  asm_sym_rel_own lo p env own cs ss /\ cs.as_stack = top ++ rest /\
  asm_steps lo (build_offset_to_pc p) p n
    (cs with as_stack := top) = AsmOK mid /\
  sym_steps_mode allow_own p env own n ss = SymOK prepared ==>
  asm_sym_rel_own lo p env own
    (mid with as_stack := mid.as_stack ++ rest) prepared
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    (rpt strip_tac >> irule asm_sym_steps_mode_sim >> metis_tac[]) >>
  drule_all (PURE_REWRITE_RULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
      (SPEC_ALL sym_prepared_prefix_endpoint_mode_conditional))) >> simp[]
QED

Theorem sym_prepared_emit_localize_own:
  asm_sym_rel_own lo p env own
    (cs with as_stack := cs.as_stack ++ rest) ss /\
  venom_asm_rel lo ps vs cs /\ sym_kinds_ok cplan fn ret srest ps ss ==>
  ?top. ss.sym_stack = top ++ srest /\
    asm_sym_rel_own lo p env own cs (ss with sym_stack := top) /\
    sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH top = LENGTH cs.as_stack
Proof
  rewrite_tac[GSYM asm_sym_rel_core_own] >>
  MATCH_ACCEPT_TAC sym_prepared_emit_localize_core
QED

Theorem sym_selected_prefix_paired_own:
  code_labels_agree p lo /\ opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded sb ps /\ residual_budget_wf_marked sb [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==> operand_val vs lo op = operand_val vs lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_static_wf p /\ asm_sym_rel_own lo p env own cs ss /\
  cs.as_stack = top ++ rest /\
  venom_asm_rel lo ps vs (cs with as_stack := top) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?mid ready localtop.
    plan_state_residual_wf_marked sb selected (LENGTH selected) arranged /\
    arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (iops ++ rops)))
      (cs with as_stack := top) = AsmOK mid /\
    venom_asm_rel lo arranged vs mid /\
    mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss = SymOK ready /\
    sym_kinds_ok cplan fn ret srest arranged ready /\
    ready.sym_base.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    ready.sym_stack = localtop ++ srest /\
    asm_sym_rel_own lo p env own mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH localtop = LENGTH mid.as_stack
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    (rpt strip_tac >> irule asm_sym_steps_mode_sim >> metis_tac[]) >>
  drule_all (PURE_REWRITE_RULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
      (SPEC_ALL sym_selected_prefix_paired_mode_conditional))) >> simp[]
QED

Theorem sym_frame_selected_prefix_paired_own:
  code_labels_agree p lo /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 ps cs ss /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  inst.inst_opcode <> INVOKE /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
  MEM inst (fn_insts fn) /\ source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  step_inst fuel ctx inst vs = OK vsout /\
  generated_plan_state_wf_marked sb ps /\ fn_shape_ok fn /\
  dfg = dfg_build_function fn /\
  emit_input_plan inst.inst_opcode operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?mid ready localtop m'.
    plan_state_residual_wf_marked sb selected (LENGTH selected) arranged /\
    arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := cs.as_memory) mid /\
    mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss = SymOK ready /\
    sym_kinds_ok cplan fn ret srest arranged ready /\
    ready.sym_base.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    ready.sym_stack = localtop ++ srest /\
    asm_sym_rel_own lo p env own mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH localtop = LENGTH mid.as_stack /\
    step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := cs.as_memory) =
      OK (frame_view fn ra vsout with vs_memory := m') /\
    EVERY (\(off,len). len = 0 \/ off + len <= final.ps_alloc.sa_spill_base \/
      final.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst (frame_view fn ra vs with vs_memory := cs.as_memory))
Proof
  rewrite_tac[sym_frame_inv_own_def] >> strip_tac >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by
    (rpt strip_tac >> irule asm_sym_steps_mode_sim >> metis_tac[]) >>
  drule_all (PURE_REWRITE_RULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
      (SPEC_ALL sym_frame_selected_prefix_paired_mode_conditional))) >> simp[]
QED

(* The saved-label composition does not depend on the bridge's code predicate. *)
Theorem sym_frame_suffix_compose_mode_core:
  sym_steps_mode allow_own p env own n ss = SymOK mid /\
  sym_steps_mode allow_own p env own m mid = SymOK final /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b) ==>
  sym_steps_mode allow_own p env own (n + m) ss = SymOK final /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> conj_tac >- simp[sym_steps_mode_add] >> metis_tac[]
QED

Theorem sym_frame_suffix_compose_own:
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 ps cs ss /\
  sym_steps_mode allow_own p env own n ss = SymOK mid /\
  sym_steps_mode allow_own p env own m mid = SymOK final /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b) ==>
  sym_steps_mode allow_own p env own (n + m) ss = SymOK final /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  rewrite_tac[sym_frame_inv_own_def] >> strip_tac >>
  drule_all sym_frame_suffix_compose_mode_core >> simp[]
QED
