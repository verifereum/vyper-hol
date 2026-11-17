(* Assertion instruction composition, shared by canonical and own-code runs. *)
Theory symInstAssertOwn
Ancestors symInstPiecesFacts symInstPrefixOwn symEmitOwn symEmitSim
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim fnFrameDeepInst
  asmSymModeOwn

val assert_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", assert_bridge_core_tm);

Theorem sym_assertion_prepared_run_mode_core:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\ step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) localtop cs.as_stack /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  (inst.inst_opcode = ASSERT ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]) /\
  (inst.inst_opcode = ASSERT_UNREACHABLE ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
    INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3)) ==>
  ?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `?w tail. localtop = Val w :: tail /\ w <> 0w` by
    (drule_all (SRULE [] (Q.INST
       [`ss` |-> `ss with sym_stack := localtop`, `srest` |-> `[]`]
       sym_assert_prepared_nonzero_core)) >> simp[]) >>
  `ss.sym_stack = Val w :: (tail ++ srest)` by simp[] >>
  `?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    full.sym_stack = DROP 1 ss.sym_stack` by
    (Cases_on `inst.inst_opcode = ASSERT` >> gvs[]
     >- (drule_all sym_assert_success_run_mode >> simp[] >> metis_tac[]) >>
     drule_all sym_assert_unreachable_success_run_mode >> simp[] >> metis_tac[]) >>
  `1 <= LENGTH ps.ps_stack` by simp[] >>
  qexists `full` >> simp[] >> irule sym_kinds_ok_release_dead_spills >>
  irule sym_emit_kinds_pop >> qexistsl [`1`, `ps`, `ss`] >> simp[]
QED

Theorem sym_assertion_prepared_run_own:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\ step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own lo p env own cs (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  (inst.inst_opcode = ASSERT ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]) /\
  (inst.inst_opcode = ASSERT_UNREACHABLE ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
    INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3)) ==>
  ?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\sv w. sval_conc lo sv = SOME w) localtop cs.as_stack` by
    gvs[asmSymBridgeTheory.asm_sym_rel_own_def] >>
  drule_all sym_assertion_prepared_run_mode_core >> simp[]
QED

Theorem sym_assert_prepared_run_own:
  inst.inst_opcode = ASSERT /\ inst.inst_operands = [cond] /\
  step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own lo p env own cs (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  asm_block_at p ss.sym_base.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] ==>
  ?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  strip_tac >>
  drule_at (Pat `step_inst _ _ _ _ = _`) sym_assertion_prepared_run_own >>
  simp[] >> disch_then irule >> simp[] >>
  qexistsl [`cs`, `lo`, `m`, `ra`] >> gvs[]
QED

Theorem sym_assert_inst_symbolic_run_mode_core:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  inst.inst_opcode = ASSERT /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [cond] <= LENGTH (SND (emit_input_plan ASSERT [cond] nl ps)).ps_stack /\
  (!op. MEM op [cond] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [cond] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ bridge_core lo code_ok cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> drule_all assert_plan_decompose >> strip_tac >>
  rename1 `emit_input_plan ASSERT [cond] nl ps = (iops,prepared)` >>
  rename1 `reorder_plan _ [cond] prepared = (rops,arranged)` >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (gvs[allocMonoTheory.release_dead_spills_spill_base,
      allocMonoTheory.release_dead_spills_next_offset] >>
     metis_tac[allocMonoTheory.emit_input_plan_spill_base,
       allocMonoTheory.reorder_plan_spill_base]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  `emit_input_plan inst.inst_opcode [cond] nl ps = (iops,prepared)` by simp[] >>
  drule (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO))
    (SPEC_ALL sym_frame_selected_prefix_paired_mode_conditional)) >>
  disch_then (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ vs = _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`sb`, `r`, `labs0`, `qs`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `sym_steps_mode allow_own prog env own _ ss = SymOK ready` >>
  rename1 `venom_asm_rel lo arranged _ mid` >>
  rename1 `ready.sym_stack = localtop ++ srest` >>
  `LIST_REL (\sv w. sval_conc lo sv = SOME w) localtop mid.as_stack` by gvs[] >>
  `asm_block_at prog ready.sym_base.as_pc
     [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]` by
    gvs[stackOpSimTheory.execute_plan_append, planExecTheory.execute_plan_def,
      planExecTheory.exec_stack_op_def, stackOpSimTheory.asm_block_at_append] >>
  `?full. sym_steps_mode allow_own prog env own 3 ready = SymOK full /\
    full.sym_mem_labels = ready.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (arranged with ps_stack := stack_pop 1 arranged.ps_stack)) full` by
    (drule_at (Pat `venom_asm_rel _ arranged _ mid`) sym_assertion_prepared_run_mode_core >>
     disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
     disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ ready`)) >>
     disch_then (drule_at (Pat `step_inst _ _ _ vs = _`)) >>
     disch_then irule >> simp[] >>
     gvs[venomMemPropsTheory.eval_operand_with_memory,
       genFrameSimTheory.operand_val_memory_update] >> metis_tac[]) >>
  rename1 `sym_steps_mode allow_own prog env own 3 ready = SymOK full` >>
  qmatch_asmsub_abbrev_tac
    `sym_steps_mode allow_own prog env own npre ss = SymOK ready` >>
  `sym_steps_mode allow_own prog env own (npre + 3) ss = SymOK full` by
    (irule sym_steps_mode_compose >> qexists `ready` >> simp[]) >>
  unabbrev_all_tac >> qexists `full` >>
  conj_tac
  >- (qpat_x_assum `sym_steps_mode _ _ _ _ (_ + 3) ss = SymOK full` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      rewrite_tac[planExecTheory.execute_plan_def, listTheory.MAP_APPEND,
        listTheory.MAP, listTheory.FLAT_APPEND, listTheory.FLAT,
        listTheory.APPEND, listTheory.LENGTH_APPEND, listTheory.LENGTH,
        planExecTheory.exec_stack_op_def, arithmeticTheory.ADD_ASSOC] >>
      simp[]) >>
  conj_tac >- simp[] >> rpt strip_tac >>
  qpat_x_assum `full.sym_mem_labels = _` (fn th => rewrite_tac[th]) >>
  first_x_assum (drule_at Any) >> simp[]
QED

Theorem sym_assert_inst_symbolic_run_own:
  code_labels_agree prog lo /\
  inst.inst_opcode = ASSERT /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [cond] <= LENGTH (SND (emit_input_plan ASSERT [cond] nl ps)).ps_stack /\
  (!op. MEM op [cond] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [cond] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\
  sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss'` by
    (rpt strip_tac >> drule_all asm_sym_steps_mode_sim >> simp[]) >>
  fs[sym_frame_inv_own_def] >>
  drule_at (Pat `step_inst _ _ _ _ = _`)
    (SRULE [asmSymBridgeTheory.asm_sym_rel_core_own]
      (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
        sym_assert_inst_symbolic_run_mode_core)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists `r` >> simp[]
QED

Theorem sym_assert_fresh_release_kinds:
  sym_kinds_ok cplan fn ret srest
    (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) ss /\
  fresh_label prefix (ps with ps_stack := stack_pop 1 ps.ps_stack) = (lbl,qs) ==>
  sym_kinds_ok cplan fn ret srest (release_dead_spills nl qs) ss
Proof
  strip_tac >> gvs[stackPlanTypesTheory.fresh_label_def] >>
  irule sym_kinds_ok_inventory_mono >> goal_assum (drule_at Any) >>
  mp_tac (Q.SPECL
    [`ps with <|ps_stack := stack_pop 1 ps.ps_stack;
       ps_label_counter := ps.ps_label_counter + 1|>`,
     `ps with ps_stack := stack_pop 1 ps.ps_stack`, `nl`]
    (GEN_ALL release_dead_spills_inventory_cong)) >> simp[]
QED

Theorem sym_assert_unreachable_inst_symbolic_run_mode_core:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [cond] <= LENGTH (SND (emit_input_plan ASSERT_UNREACHABLE [cond] nl ps)).ps_stack /\
  (!op. MEM op [cond] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [cond] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\ bridge_core lo code_ok cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp ops) - 1) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> drule_all genBlockSimTheory.assert_unreachable_plan_decompose >> strip_tac >>
  rename1 `emit_input_plan ASSERT_UNREACHABLE [cond] nl ps = (iops,prepared)` >>
  rename1 `reorder_plan _ [cond] prepared = (rops,arranged)` >>
  rename1 `fresh_label "reachable" (arranged with ps_stack := stack_pop 1 arranged.ps_stack) = (lbl,p3)` >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (drule allocMonoTheory.fresh_label_spill_base >> simp[] >> strip_tac >>
     gvs[allocMonoTheory.release_dead_spills_spill_base,
       allocMonoTheory.release_dead_spills_next_offset] >>
     metis_tac[allocMonoTheory.emit_input_plan_spill_base,
       allocMonoTheory.reorder_plan_spill_base]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  `emit_input_plan inst.inst_opcode [cond] nl ps = (iops,prepared)` by simp[] >>
  drule (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO))
    (SPEC_ALL symInstPrefixOwnTheory.sym_frame_selected_prefix_paired_mode_conditional)) >>
  disch_then (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ vs = _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`sb`, `r`, `labs0`, `qs`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `sym_steps_mode allow_own prog env own _ ss = SymOK ready` >>
  rename1 `venom_asm_rel lo arranged _ mid` >>
  rename1 `ready.sym_stack = localtop ++ srest` >>
  `LIST_REL (\sv w. sval_conc lo sv = SOME w) localtop mid.as_stack` by gvs[] >>
  `asm_block_at prog ready.sym_base.as_pc
     [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl]` by
    gvs[stackOpSimTheory.execute_plan_append, planExecTheory.execute_plan_def,
      planExecTheory.exec_stack_op_def, stackOpSimTheory.asm_block_at_append] >>
  `INDEX_OF (AsmLabel lbl) prog = SOME (ready.sym_base.as_pc + 3)` by
    (drule_at (Pat `asm_block_at _ _ _`) symInstPiecesFactsTheory.asm_static_block_label_index >>
     disch_then (qspecl_then [`lbl`, `3`] mp_tac) >> simp[]) >>
  `?full. sym_steps_mode allow_own prog env own 3 ready = SymOK full /\
    full.sym_mem_labels = ready.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (arranged with ps_stack := stack_pop 1 arranged.ps_stack)) full` by
    (drule_at (Pat `venom_asm_rel _ arranged _ mid`) sym_assertion_prepared_run_mode_core >>
     disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
     disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ ready`)) >>
     disch_then (drule_at (Pat `step_inst _ _ _ vs = _`)) >>
     disch_then irule >> simp[] >>
     gvs[venomMemPropsTheory.eval_operand_with_memory,
       genFrameSimTheory.operand_val_memory_update] >> metis_tac[]) >>
  rename1 `sym_steps_mode allow_own prog env own 3 ready = SymOK full` >>
  drule_all sym_assert_fresh_release_kinds >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `sym_steps_mode allow_own prog env own npre ss = SymOK ready` >>
  `sym_steps_mode allow_own prog env own (npre + 3) ss = SymOK full` by
    (irule sym_steps_mode_compose >> qexists `ready` >> simp[]) >>
  unabbrev_all_tac >> qexists `full` >>
  conj_tac
  >- (qpat_x_assum `sym_steps_mode _ _ _ _ (_ + 3) ss = SymOK full` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      rewrite_tac[planExecTheory.execute_plan_def, listTheory.MAP_APPEND,
        listTheory.MAP, listTheory.FLAT_APPEND, listTheory.FLAT,
        listTheory.APPEND, listTheory.LENGTH_APPEND, listTheory.LENGTH,
        planExecTheory.exec_stack_op_def, arithmeticTheory.ADD_ASSOC] >> simp[]) >>
  conj_tac >- simp[] >> rpt strip_tac >>
  qpat_x_assum `full.sym_mem_labels = _` (fn th => rewrite_tac[th]) >>
  first_x_assum (drule_at Any) >> simp[]
QED

Theorem sym_assert_unreachable_inst_symbolic_run_own:
  code_labels_agree prog lo /\
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [cond] <= LENGTH (SND (emit_input_plan ASSERT_UNREACHABLE [cond] nl ps)).ps_stack /\
  (!op. MEM op [cond] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [cond] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\
  sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp ops) - 1) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss'` by
    (rpt strip_tac >> drule_all asmSymModeOwnTheory.asm_sym_steps_mode_sim >> simp[]) >>
  fs[sym_frame_inv_own_def] >>
  drule_at (Pat `step_inst _ _ _ _ = _`)
    (SRULE [asmSymBridgeTheory.asm_sym_rel_core_own]
      (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
        sym_assert_unreachable_inst_symbolic_run_mode_core)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists `r` >> simp[]
QED
