(* Return preparation and exact execution, shared by both symbolic modes.
   The final control join discharges the preparation and run interfaces. *)
Theory symControlRetOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] codegenSymRel codegenSymOwnRel
  symFrameControlFacts symControlPrefixOwn fnFrameDeepRet fnFrameBoundaryGenRet
  asmSymRelocLabelsOwn symPlannerSim symShuffleSim stackPlanGen stackPlanTypes
  planExec asmSem asmSymSem frameRel contextCodegenRel unitShapeDefs dfgDefs
  codegenEncodingWf spillPlanSim reorderStages inputMaterialised mixedPrefixSim
  venomInst symControlRetStackOwn

(* Parser notation for the existing bridge and frame clauses, not definitions. *)
val ret_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", ret_bridge_core_tm);
val _ = Parse.temp_overload_on ("ret_frame", ``\lo code_ok p ctx cp fn ret srest labs0 ps cs ss.
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p)``);

Theorem ret_operand_not_code_end_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = RET /\ MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  Cases_on `allow_own` >> simp[] >> strip_tac >>
  fs[label_flow_ok_def, label_flow_own_ok_def] >>
  first_x_assum (qspecl_then [`fn`, `inst`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ret_payload_var_kind_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = RET /\ inst.inst_operands = front ++ [Var pc] /\
  MEM (Var x) front /\ Var x <> dead_stack_marker /\
  op_kind_ok fn ret (Var x) sv ==> ?w. sv = Val w
Proof
  strip_tac >>
  drule_all_then assume_tac fnFrameBoundaryGenRetTheory.ret_payload_not_retpc >>
  `~code_end_var fn x` by
    (irule ret_operand_not_code_end_mode >> metis_tac[listTheory.MEM_APPEND]) >>
  gvs[op_kind_ok_def]
QED

Theorem ret_payload_op_kind_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  label_positions_ok inst /\ inst.inst_opcode = RET /\
  inst.inst_operands = front ++ [Var pc] /\ MEM op front /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  strip_tac >> Cases_on `op`
  >- gvs[op_kind_ok_def]
  >- metis_tac[ret_payload_var_kind_mode] >>
  gvs[op_kind_ok_def, label_positions_ok_def, listTheory.EVERY_APPEND,
      listTheory.EVERY_MEM, is_label_operand_def] >> metis_tac[is_label_operand_def]
QED

Theorem ret_compute_operands_last_retpc:
  MEM inst (fn_insts (reachable_fn fn)) /\ retpc_shape_ok fn /\
  inst.inst_opcode = RET ==>
  ?front x. compute_operands inst = front ++ [Var x] /\ retpc_var fn x
Proof
  simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  metis_tac[retpc_shape_ok_def, reachable_retpc_var, listTheory.MEM]
QED

Theorem ret_source_op_kinds_mode:
  MEM inst (fn_insts (reachable_fn fn)) /\ codegen_ready_fn fn /\
  opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = RET /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) ==>
  ?front x. compute_operands inst = front ++ [Var x] /\ retpc_var fn x /\
    (!op sv. MEM op front /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w)
Proof
  strip_tac >> drule_all_then strip_assume_tac ret_compute_operands_last_retpc >>
  `MEM inst (fn_insts fn)` by
    (irule reachable_fn_insts_nonphi >> simp[]) >>
  gvs[compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def, fn_shape_ok_def, listTheory.EVERY_MEM] >>
  `label_positions_ok inst` by metis_tac[inst_shape_ok_def] >>
  rpt strip_tac >> `op <> dead_stack_marker` by metis_tac[] >>
  drule_all ret_payload_op_kind_mode >> simp[]
QED


Theorem ret_prepared_symbolic_stack_core:
  !lo code_ok cs ss cp fn ret srest ps front x ra values rest.
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  ps.ps_stack = front ++ [Var x] /\ retpc_var fn x /\
  Var x <> dead_stack_marker /\
  (!op sv. MEM op front /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  cs.as_stack = ra :: values ++ rest /\ LENGTH values = LENGTH front ==>
  ss.sym_stack = Lab ret 0 :: MAP Val values ++ srest
Proof
  rpt gen_tac >> strip_tac >>
  drule sym_kinds_ret_stack_concretization >> disch_then irule >>
  fs[asmSymBridgeTheory.asm_sym_rel_core_stack_pc] >> metis_tac[]
QED

Theorem ret_label_concrete_head_core:
  bridge_core lo code_ok cs ss /\ cs.as_stack = ra :: tail /\
  ss.sym_stack = Lab ret 0 :: stail ==> sval_conc lo (Lab ret 0) = SOME ra
Proof
  strip_tac >> gvs[asmSymBridgeTheory.asm_sym_rel_core_stack_pc]
QED

Theorem ret_label_jump_destination_reloc:
  asm_static_wf p /\ code_labels_agree p lo /\ MEM (AsmLabel ret) p /\
  sval_conc lo (Lab ret 0) = SOME ra /\
  FLOOKUP (build_offset_to_pc p) (w2n ra) = SOME pc ==>
  sym_jump_dest p (Lab ret 0) = SOME pc
Proof
  strip_tac >>
  `?i. INDEX_OF (AsmLabel ret) p = SOME i` by
    metis_tac[listTheory.INDEX_OF_eq_NONE, optionTheory.option_CASES] >>
  `sym_jump_dest p (Lab ret 0) = SOME i` by simp[sym_jump_dest_def] >>
  drule_all sym_jump_dest_conc_reloc >> simp[]
QED

Theorem ret_preparation_arranged_stack:
  !base ps inputs nl iops prepared rops arranged final dfg.
  generated_plan_state_wf_marked base ps /\ LENGTH inputs <= 16 /\
  LENGTH inputs <= LENGTH prepared.ps_stack /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan RET inputs nl ps = (iops,prepared) /\
  reorder_plan dfg inputs prepared = (rops,arranged) /\
  final.ps_stack = stack_pop (LENGTH inputs) arranged.ps_stack /\
  final.ps_stack = [] ==> arranged.ps_stack = inputs
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  `residual_budget_wf_marked spillbase [] ps` by
    metis_tac[deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  `residual_budget_wf_marked spillbase inputs prepared` by
    metis_tac[deepResidualBudgetTheory.emit_input_plan_residual_budget_wf_marked,
              listTheory.APPEND] >>
  `!x. LIST_ELEM_COUNT x inputs <= LIST_ELEM_COUNT x prepared.ps_stack` by
    metis_tac[inputMaterialisedTheory.emit_input_plan_materialised] >>
  drule_all_then strip_assume_tac
    deepResidualBudgetTheory.reorder_plan_materialised_arranged_marked >> gvs[]
QED

Theorem sym_ret_suffix_steps_mode_conditional:
  !allow_own lo code_ok own p env ctx cp fn ret srest labs0 ps cs ss values pc.
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  ret_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc [AsmOp "JUMP"] /\
  ss.sym_stack = Lab ret 0 :: (MAP Val (REVERSE values) ++ srest) /\
  sym_jump_dest p (Lab ret 0) = SOME pc ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p 1 cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    bridge_core lo code_ok cs' ss' /\ cs'.as_pc = pc /\
    ss'.sym_stack = MAP Val (REVERSE values) ++ srest /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "JUMP"]` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `sym_steps p env 1 ss = SymOK
    (ss with <|sym_base := ss.sym_base with as_pc := pc;
      sym_stack := MAP Val (REVERSE values) ++ srest|>)` by
    (rewrite_tac[arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
     gvs[asm_block_at_def, sym_step_def, sym_step_op_def, sym_jump_def]) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _`
    (drule_all_then (qx_choose_then `cs'` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`cs'`, `ss with <|sym_base := ss.sym_base with as_pc := pc;
    sym_stack := MAP Val (REVERSE values) ++ srest|>`] >> asm_rewrite_tac[] >>
  conj_tac >- (drule_all (Q.SPECL [`lo`, `code_ok`]
    asmSymBridgeTheory.asm_sym_rel_core_pc) >> simp[] >> metis_tac[]) >>
  fs[sym_kinds_ok_def]
QED

(* Exact interface supplied by the read-only replay subject at the join. *)
val _ = Parse.temp_overload_on ("ret_readonly_preparation", ``\allow_own lo code_ok own p env.
  !opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp ctx cp srest labs0 cs ss.
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\ FLOOKUP ps.ps_spilled op2 = SOME off2 /\
    op1 <> op2 ==> off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  prefix_wf lo (LENGTH ps.ps_stack) (iops ++ rops) /\
  EVERY is_prefix_op (iops ++ rops) /\
  EVERY (\op. !l d. op <> SOPushOfst l d) (iops ++ rops) /\
  ret_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'. asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    ret_frame lo code_ok p ctx cp fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)``);

Theorem sym_ret_prepare_frame_sim_mode_conditional:
  !allow_own lo code_ok own inputs nl ps iops prepared dfg rops arranged fn ret fmp
    p env ctx cp srest labs0 cs ss base.
  ret_readonly_preparation allow_own lo code_ok own p env /\
  emit_input_plan RET inputs nl ps = (iops,prepared) /\
  reorder_plan dfg inputs prepared = (rops,arranged) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  generated_plan_state_wf_marked base ps /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) inputs ==> IS_SOME (FLOOKUP lo l)) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  ret_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'. asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    ret_frame lo code_ok p ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `prefix_wf lo (LENGTH ps.ps_stack) (iops ++ rops)` by
    (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
     qexistsl [`dfg`, `inputs`, `nl`, `RET`, `prepared`, `arranged`] >> simp[]) >>
  `EVERY is_prefix_op (iops ++ rops)` by
    metis_tac[planWfTheory.prefix_wf_every_prefix_op] >>
  `EVERY (\op. !l d. op <> SOPushOfst l d) (iops ++ rops)` by
    (simp[listTheory.EVERY_MEM, listTheory.MEM_APPEND] >>
     metis_tac[codegenEncodingWfTheory.emit_input_plan_no_push_ofst,
               codegenEncodingWfTheory.reorder_plan_no_push_ofst]) >>
  qpat_x_assum `ret_readonly_preparation _ _ _ _ _ _` irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`inputs`, `nl`, `RET`, `ps`, `prepared`] >> simp[] >>
  fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  metis_tac[doSwapSimTheory.spill_alloc_layout_wf_spilled_separated]
QED

Theorem sym_ret_generated_prepare_frame_sim_mode_conditional:
  !allow_own lo code_ok own p env base cp.
  ret_readonly_preparation allow_own lo code_ok own p env /\
  inst.inst_opcode = RET /\ inst_wf inst /\
  MEM inst (fn_insts (reachable_fn fn)) /\ codegen_ready_fn fn /\ fn_shape_ok fn /\
  generated_plan_state_wf_marked base ps /\ LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  generate_inst_plan lv (dfg_build_function fn) cfg fn inst nl halting term label ps =
    SOME (ops,final) /\ final.ps_stack = [] /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  asm_block_at p cs.as_pc (execute_plan fmp ops) /\ asm_static_wf p /\
  ret_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss ==>
  ?iops prepared rops arranged cs' ss'.
    emit_input_plan RET (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan (dfg_build_function fn) (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "JUMP"] /\
    final.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack /\
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    ret_frame lo code_ok p ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all_then strip_assume_tac fnFrameBoundaryGenRetTheory.ret_plan_decompose >>
  `!off. ~MEM (SOSpill off) ops` by
    (irule fnFrameBoundaryGenRetTheory.ret_plan_no_spill >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by (irule reachable_fn_insts_nonphi >> simp[]) >>
  `label_positions_ok inst /\ ssa_form fn` by
    (fs[fn_shape_ok_def, stackPlanGenTheory.codegen_ready_fn_def, listTheory.EVERY_MEM] >>
     metis_tac[inst_shape_ok_def]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[deepInstSimTheory.marked_operand_owned] >>
  `!l. ~MEM (Label l) (compute_operands inst)` by
    (gvs[label_positions_ok_def, compute_operands_def, python_stack_operands_def,
         ir_specific_operand_order_def, listTheory.EVERY_MEM] >>
     metis_tac[is_label_operand_def]) >>
  `asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops))` by
    fs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  `!off. ~MEM (SOSpill off) (iops ++ rops)` by gvs[listTheory.MEM_APPEND] >>
  `!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)` by
    (fs[listTheory.MEM_APPEND] >> metis_tac[]) >>
  `!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)` by simp[] >>
  qexistsl [`iops`, `prepared`, `rops`, `arranged`] >>
  ntac 4
    (CONV_TAC (QUANT_CONV (HO_REWR_CONV RIGHT_EXISTS_AND_THM) THENC
       HO_REWR_CONV RIGHT_EXISTS_AND_THM) >>
     conj_tac >- first_assum ACCEPT_TAC) >>
  irule sym_ret_prepare_frame_sim_mode_conditional >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem sym_ret_ready_frame_sim_mode_conditional:
  !allow_own code_ok own fuel ctx cp lo prog liveness dfg cfg fn inst nl halting term label
   base ps vs cs ops final ra rest mem0 pc_ret env ret srest labs0 ss rv vs'.
  ret_readonly_preparation allow_own lo code_ok own prog env /\ code_labels_agree prog lo /\
  inst.inst_opcode = RET /\ MEM inst (fn_insts (reachable_fn fn)) /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  generated_plan_state_wf_marked base ps /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) nl ps)).ps_stack /\
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
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  final.ps_stack = [] /\ asm_block_at prog cs.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  ret_frame lo code_ok prog ctx cp fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = IntRet rv vs' ==>
  ?mid smid arranged.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cp.cp_initial_fmp ops) - 1) cs = AsmOK mid /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cp.cp_initial_fmp ops) - 1) ss = SymOK smid /\
    ret_frame lo code_ok prog ctx cp fn ret srest labs0 arranged mid smid /\
    asm_block_at prog mid.as_pc [AsmOp "JUMP"] /\
    smid.sym_stack = Lab ret 0 :: MAP Val (REVERSE rv.iret_values) ++ srest /\
    sym_jump_dest prog (Lab ret 0) = SOME pc_ret /\
    0 < LENGTH (execute_plan cp.cp_initial_fmp ops)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all_then (qspec_then `ra` strip_assume_tac)
    fnFrameBoundaryGenRetTheory.ret_source_frame_boundary >>
  qpat_x_assum `vs' = vs` SUBST_ALL_TAC >>
  `LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack` by simp[] >>
  drule_all_then strip_assume_tac fnFrameDeepRetTheory.ret_frame_prefix_marked_exact >>
  `?iops prepared rops arranged mid smid.
    emit_input_plan RET (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan (dfg_build_function fn) (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "JUMP"] /\
    final.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack /\
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cp'.cp_initial_fmp (iops ++ rops))) cs = AsmOK mid /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cp'.cp_initial_fmp (iops ++ rops))) ss = SymOK smid /\
    ret_frame lo code_ok prog ctx cp' fn ret srest labs0 arranged mid smid /\
    mid.as_pc = cs.as_pc + LENGTH (execute_plan cp'.cp_initial_fmp (iops ++ rops)) /\
    (!b. FLOOKUP smid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)` by
    (irule sym_ret_generated_prepare_frame_sim_mode_conditional >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `ret_readonly_preparation _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!o2pc. ?mid. _` (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  `LENGTH (execute_plan cp'.cp_initial_fmp ops) =
    LENGTH (execute_plan cp'.cp_initial_fmp (iops ++ rops)) + 1` by
    simp[stackOpSimTheory.execute_plan_append, planExecTheory.execute_plan_def,
         planExecTheory.exec_stack_op_def] >>
  gvs[] >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[deepInstSimTheory.marked_operand_owned] >>
  `arranged.ps_stack = compute_operands inst` by
    (irule ret_preparation_arranged_stack >> simp[] >> metis_tac[]) >>
  suspend "typed"
QED

Resume sym_ret_ready_frame_sim_mode_conditional[typed]:
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all_then (qspec_then `ret` strip_assume_tac) ret_source_op_kinds_mode >>
  `LENGTH (REVERSE rv.iret_values) = LENGTH front` by
    (drule fnFrameBoundaryInvokeTheory.eval_operands_some_length >> simp[]) >>
  `Var x <> dead_stack_marker` by gvs[listTheory.EVERY_APPEND] >>
  `smid.sym_stack = Lab ret 0 :: MAP Val (REVERSE rv.iret_values) ++ srest` by
    (qpat_assum `sym_kinds_ok _ _ _ _ arranged smid`
       (mp_then Any mp_tac sym_kinds_ret_stack_concretization) >>
     disch_then irule >> simp[] >> metis_tac[listTheory.LIST_REL_CONS1]) >>
  `sym_jump_dest prog (Lab ret 0) = SOME pc_ret` by
    (irule ret_label_jump_destination_reloc >> simp[] >>
     qexistsl [`lo`, `ra`] >> gvs[]) >>
  qexists_tac `arranged` >> gvs[] >>
  conj_tac >- (qexists_tac `m` >> simp[]) >> metis_tac[]
QED
Finalise sym_ret_ready_frame_sim_mode_conditional

Theorem sym_ret_symbolic_exact_mode_conditional:
  !allow_own code_ok own fuel ctx cp lo prog liveness dfg cfg fn inst nl halting term label
   base ps vs cs ops final ra rest mem0 pc_ret env ret srest labs0 ss rv vs' final_cs.
  ret_readonly_preparation allow_own lo code_ok own prog env /\
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  code_labels_agree prog lo /\
  inst.inst_opcode = RET /\ MEM inst (fn_insts (reachable_fn fn)) /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  generated_plan_state_wf_marked base ps /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) nl ps)).ps_stack /\
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
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  final.ps_stack = [] /\ asm_block_at prog cs.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  ret_frame lo code_ok prog ctx cp fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = IntRet rv vs' /\
  asm_steps lo (build_offset_to_pc prog) prog (LENGTH (execute_plan cp.cp_initial_fmp ops)) cs =
    AsmOK final_cs ==>
  ?ss'. sym_steps_mode allow_own prog env own (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK ss' /\
    bridge_core lo code_ok final_cs ss' /\
    ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `?mid smid arranged.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cp'.cp_initial_fmp ops) - 1) cs = AsmOK mid /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cp'.cp_initial_fmp ops) - 1) ss = SymOK smid /\
    ret_frame lo code_ok prog ctx cp' fn ret srest labs0 arranged mid smid /\
    asm_block_at prog mid.as_pc [AsmOp "JUMP"] /\
    smid.sym_stack = Lab ret 0 :: MAP Val (REVERSE rv.iret_values) ++ srest /\
    sym_jump_dest prog (Lab ret 0) = SOME pc_ret /\
    0 < LENGTH (execute_plan cp'.cp_initial_fmp ops)` by
    (irule sym_ret_ready_frame_sim_mode_conditional >> asm_rewrite_tac[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qpat_x_assum `ret_readonly_preparation _ _ _ _ _ _` kall_tac >>
  `?out sout.
    asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmOK out /\
    sym_steps_mode allow_own prog env own 1 smid = SymOK sout /\
    bridge_core lo code_ok out sout /\ out.as_pc = pc_ret /\
    sout.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
    (!b. context_spill_byte cp' b /\ ~closure_spill_byte ctx cp' fn.fn_name b ==>
      FLOOKUP sout.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM sout.sym_mem_labels ==> context_spill_byte cp' b)` by
    (irule sym_ret_suffix_steps_mode_conditional >> asm_rewrite_tac[] >>
     conj_tac >- (qexists_tac `m` >> simp[]) >>
     qexistsl [`arranged`, `ret`] >> simp[]) >>
  `LENGTH (execute_plan cp'.cp_initial_fmp ops) - 1 + 1 =
    LENGTH (execute_plan cp'.cp_initial_fmp ops)` by decide_tac >>
  `asm_steps lo (build_offset_to_pc prog) prog
    ((LENGTH (execute_plan cp'.cp_initial_fmp ops) - 1) + 1) cs = AsmOK out` by
    (irule blockSimHelpersTheory.asm_steps_compose_ok >> metis_tac[]) >>
  gvs[] >> qexists_tac `sout` >> asm_rewrite_tac[] >>
  qspecl_then [`LENGTH (execute_plan cp'.cp_initial_fmp ops) - 1`, `1`, `ss`]
    mp_tac (Q.INST [`p` |-> `prog`] sym_steps_mode_add) >> simp[] >>
  strip_tac >> qexists_tac `m'` >> simp[]
QED

Theorem sym_ret_frame_sim_deep_mode_conditional:
  !allow_own code_ok own fuel ctx cp lo prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs cs ops final ra rest mem0 pc_ret
   env ret srest labs0 ss.
  ret_readonly_preparation allow_own lo code_ok own prog env /\
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  (!rv vs'. step_inst fuel ctx inst vs = IntRet rv vs' ==>
    ?out. asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cp.cp_initial_fmp ops)) cs = AsmOK out /\
      out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
      context_memory_rel cp vs'.vs_memory out.as_memory /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        read_byte b out.as_memory = read_byte b mem0) /\ shared_state_rel vs' out) /\
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
  ret_frame lo code_ok prog ctx cp fn ret srest labs0 ps cs ss ==>
  !rv vs'. step_inst fuel ctx inst vs = IntRet rv vs' ==>
    ?n out sout.
      asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK out /\
      out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
      context_memory_rel cp vs'.vs_memory out.as_memory /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        read_byte b out.as_memory = read_byte b mem0) /\ shared_state_rel vs' out /\
      sym_steps_mode allow_own prog env own n ss = SymOK sout /\
      bridge_core lo code_ok out sout /\
      sout.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        FLOOKUP sout.sym_mem_labels b = FLOOKUP labs0 b) /\
      (!b. b IN FDOM sout.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!rv vs'. _` (drule_then strip_assume_tac) >>
  `LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) next_liveness ps)).ps_stack` by
    (qpat_x_assum `LENGTH (compute_operands inst) <= LENGTH _` mp_tac >> simp[]) >>
  `?sout. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cp'.cp_initial_fmp ops)) ss = SymOK sout /\
    bridge_core lo code_ok out sout /\
    sout.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
    (!b. context_spill_byte cp' b /\ ~closure_spill_byte ctx cp' fn.fn_name b ==>
      FLOOKUP sout.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM sout.sym_mem_labels ==> context_spill_byte cp' b)` by
    (irule sym_ret_symbolic_exact_mode_conditional >> asm_rewrite_tac[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexistsl [`LENGTH (execute_plan cp'.cp_initial_fmp ops)`, `out`, `sout`] >>
  asm_rewrite_tac[] >> qexists_tac `m` >> simp[]
QED
