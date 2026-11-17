(* Selected planner prefixes paired at supplied label offsets.
   Run correspondence is an explicit premise, shared by both code modes. *)
Theory symInstPrefixOwn
Ancestors symInstKinds[qualified,ignore_grammar] asmSymBridge[qualified,ignore_grammar]
  symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim symEmitSim fnFrameDeepInst

(* Parser abbreviation for the existing closed structural bridge relation. *)
val prefix_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", prefix_bridge_core_tm);

Theorem sym_prepared_prefix_endpoint_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  bridge_core lo code_ok cs ss /\ cs.as_stack = top ++ rest /\
  asm_steps lo (build_offset_to_pc p) p n
    (cs with as_stack := top) = AsmOK mid /\
  sym_steps_mode allow_own p env own n ss = SymOK prepared ==>
  bridge_core lo code_ok (mid with as_stack := mid.as_stack ++ rest) prepared
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule asmFrameTheory.asm_steps_frame >>
  disch_then (qspec_then `rest` assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  `cs with as_stack := top ++ rest = cs` by
    simp[asmSemTheory.asm_state_component_equality] >> gvs[]
  >> (metis_tac[])
QED

Theorem sym_prepared_emit_localize_core:
  bridge_core lo code_ok (cs with as_stack := cs.as_stack ++ rest) ss /\
  venom_asm_rel lo ps vs cs /\ sym_kinds_ok cplan fn ret srest ps ss ==>
  ?top. ss.sym_stack = top ++ srest /\
    bridge_core lo code_ok cs (ss with sym_stack := top) /\
    sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH top = LENGTH cs.as_stack
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `?top. ss.sym_stack = top ++ srest /\ LENGTH top = LENGTH cs.as_stack` by
    (gvs[sym_kinds_ok_def, codegenRelTheory.venom_asm_rel_def,
         codegenRelTheory.plan_stack_rel_def] >>
     metis_tac[listTheory.LIST_REL_LENGTH, listTheory.LENGTH_REVERSE]) >>
  drule asm_sym_rel_localize_stack_core >>
  disch_then (qspecl_then [`rest`, `cs.as_stack`, `top`, `srest`] mp_tac) >>
  simp[] >> disch_then (qspec_then `code_ok` mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top)` by
    (irule sym_kinds_ok_localize_stack >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem sym_selected_prefix_paired_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  opc <> INVOKE /\
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
  asm_static_wf p /\ bridge_core lo code_ok cs ss /\
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
    bridge_core lo code_ok mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH localtop = LENGTH mid.as_stack
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `asm_block_at p (cs with as_stack := top).as_pc
    (execute_plan initial_fmp (iops ++ rops))` by simp[] >>
  drule_all deepResidualSimTheory.selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `build_offset_to_pc p` mp_tac) >>
  simp[] >> strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by
    (gvs[asmSymBridgeTheory.asm_sym_rel_core_pc]) >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (iops ++ rops))` by
    metis_tac[] >>
  drule_all sym_selected_prefix_sim_marked >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  drule_all sym_prepared_prefix_endpoint_mode_conditional >> disch_then assume_tac >>
  drule_at (Pat `venom_asm_rel _ _ _ _`) sym_prepared_emit_localize_core >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`rest`, `code_ok`] mp_tac) >>
  (impl_tac >- (first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  rename1 `sym_steps p env _ ss = SymOK ready` >>
  rename1 `asm_steps _ _ _ _ _ = AsmOK mid` >>
  rename1 `ready.sym_stack = localtop ++ srest` >>
  qexistsl [`mid`, `ready`, `localtop`] >> simp[] >>
  conj_tac
  >- ((metis_tac[symInstKindsTheory.spill_region_labels_outside_closure])) >>
  gvs[] >> metis_tac[]
QED

(* Frame specialization retains the saved memory labels and return-label clause. *)
Theorem sym_frame_selected_prefix_paired_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  bridge_core lo code_ok cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p) /\
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
    bridge_core lo code_ok mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH localtop = LENGTH mid.as_stack /\
    step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := cs.as_memory) =
      OK (frame_view fn ra vsout with vs_memory := m') /\
    EVERY (\(off,len). len = 0 \/ off + len <= final.ps_alloc.sa_spill_base \/
      final.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst (frame_view fn ra vs with vs_memory := cs.as_memory))
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all frame_inst_local_setup >> strip_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\ plan_slots_bounded sb ps /\
   residual_budget_wf_marked sb [] ps` by
    metis_tac[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
      deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  `ssa_form fn` by metis_tac[stackPlanGenTheory.codegen_ready_fn_def] >>
  drule_at (Pat `emit_input_plan _ _ _ _ = _`) sym_selected_prefix_paired_mode_conditional >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  disch_then (fn th => qpat_assum `!n cs ss ss'. _`
    (resolve_then Any mp_tac th)) >>
  simp[] >> disch_then (qspecl_then [`sb`, `r`, `ctx`] mp_tac) >>
  simp[genFrameSimTheory.operand_val_memory_update] >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
