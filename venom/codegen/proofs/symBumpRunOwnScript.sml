(* BUMP planner execution with explicit bridge-core correspondence. *)
Theory symBumpRunOwn
Ancestors
  symInstPrefixOwn symInstPieces symPostfixSim symEmitStoreOwn symEmitSim
  deepInstSim deepResidualSim genBlockSim stackPlanGen planExec codegenSymRel
  asmSymBridge asmSymSem fnPlanPrefix genFrameSim allocMono venomWf
  fnBlockPlanStaticRegion

val bump_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", bump_bridge_core_tm);

Theorem bump_plan_decompose:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\
  generate_inst_plan lv dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) ==>
  ?iops prepared rops arranged pops ps8 opts ps9.
    emit_input_plan BUMP [base_op; size_op] nl ps = (iops,prepared) /\
    reorder_plan dfg [base_op; size_op] prepared = (rops,arranged) /\
    popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) [ptr;next]))
       (arranged with ps_stack := stack_push (Var next)
         (stack_push (Var ptr) (stack_pop 2 arranged.ps_stack))) = (pops,ps8) /\
    (if FILTER (\out. MEM out nl) [ptr;next] = [] then ([],ps8)
     else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
    ops = iops ++ rops ++ bump_emit_ops ++ pops ++ opts /\
    qs = release_dead_spills nl ps9
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, venomInstTheory.is_param_opcode_def,
    generate_regular_inst_plan_def, compute_operands_def,
    venomInstTheory.python_stack_operands_def, venomInstTheory.ir_specific_operand_order_def,
    venomEffectsTheory.is_commutative_def, generate_emit_ops_def] >>
  simp[is_pre_codegen_opcode_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem selected_prefix_outputs_absent:
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= LENGTH prepared.ps_stack /\ LENGTH operands <= 17 /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) outputs ==>
  EVERY (\v. ~MEM (Var v) arranged.ps_stack /\ Var v NOTIN FDOM arranged.ps_spilled) outputs
Proof
  strip_tac >> fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all generatedPrefixSimTheory.emit_input_plan_preserves_not_mem >> strip_tac >>
  drule_all generatedPrefixSimTheory.reorder_plan_preserves_not_mem_reachable >> simp[]
QED

Theorem bump_plan_length:
  LENGTH (execute_plan fmp (xs ++ ys ++ bump_emit_ops ++ zs ++ ws)) =
  LENGTH (execute_plan fmp (xs ++ ys)) + (2 + LENGTH (execute_plan fmp (zs ++ ws)))
Proof
  `LENGTH (execute_plan fmp bump_emit_ops) = 2` by
    simp[bump_emit_ops_def, execute_plan_def, exec_stack_op_def] >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem bump_success_operand_values:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [bop;sop] /\
  step_inst fuel ctx inst s = OK t /\
  (!op. MEM op [bop;sop] ==> eval_operand op s = operand_val s lo op) ==>
  ?bv sz. operand_val s lo bop = SOME bv /\ operand_val s lo sop = SOME sz
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def, venomStateTheory.eval_operands_def] >>
  gvs[AllCaseEqs()] >> metis_tac[listTheory.MEM]
QED

Theorem sym_bump_prepared_full_emit_core_mode:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ptr <> next /\
  ssa_form fn /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ bridge_core lo code_ok cs (ss with sym_stack := top) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top) /\
  venom_asm_rel lo ps vs cs /\
  ps.ps_stack = residual ++ [base_op; size_op] /\
  base_op <> dead_stack_marker /\ size_op <> dead_stack_marker /\
  operand_val vs lo base_op = SOME base_val /\
  operand_val vs lo size_op = SOME sz /\
  EVERY (\op. case op of Var x => x <> ptr /\ x <> next | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> ptr /\ x <> next | _ => T) /\
  qs = ps with ps_stack := stack_push (Var next)
    (stack_push (Var ptr) (stack_pop 2 ps.ps_stack)) /\
  ss.sym_stack = top ++ srest /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] ==>
  ?full. sym_steps_mode allow_own p env own 2 ss = SymOK full /\
    full.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs full /\
    qs.ps_stack = residual ++ [Var ptr;Var next]
Proof
  strip_tac >>
  `asm_block_at p cs.as_pc (execute_plan 0 bump_emit_ops)` by
    (gvs[asmSymBridgeTheory.asm_sym_rel_core_pc, stackPlanGenTheory.bump_emit_ops_def,
      planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def,
      planExecTheory.dup_name_def]) >>
  drule_at (Pat `venom_asm_rel _ _ _ _`) emitSimTheory.bump_emit_sim >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`build_offset_to_pc p`, `ptr`, `next`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  `sym_kinds_ok cplan fn ret srest ps ss` by
    (drule sym_kinds_ok_restore_stack >> disch_then (qspec_then `srest` mp_tac) >>
     simp[] >>
     `ss with sym_stack := top ++ srest = ss` by
       simp[asmSymSemTheory.sym_state_component_equality] >> gvs[]) >>
  drule_at (Pat `asm_steps _ _ _ _ _ = _`)
    (Q.INST [`R` |-> `\cs ss. T`] sym_bump_source_emit_core) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ srest _ ss`)) >>
  disch_then (drule_at (Pat `MEM inst (fn_insts fn)`)) >>
  simp[] >> disch_then (qspecl_then [`own`, `env`, `ctx`, `allow_own`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `sym_steps_mode allow_own p env own 2 ss = SymOK full` >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule fnBlockBodyHelpersTheory.label_positions_ok_other >> simp[] >>
     metis_tac[unitShapeDefsTheory.fn_shape_ok_def, listTheory.EVERY_MEM,
       unitShapeDefsTheory.inst_shape_ok_def]) >>
  `2 <= LENGTH ss.sym_stack /\
   EVERY (\sv. ?w. sv = Val w) (TAKE 2 ss.sym_stack)` by
    (`LENGTH inst.inst_operands <= LENGTH ss.sym_stack /\
      EVERY (\sv. ?w. sv = Val w) (TAKE (LENGTH inst.inst_operands) ss.sym_stack)` by
       (irule ordinary_prepared_selected_numeric_mode >>
        qexistsl [`allow_own`, `cplan`, `ctx`, `fn`, `inst`, `ps`, `residual`, `ret`, `srest`] >>
        fs[listTheory.EVERY_MEM]) >> gvs[]) >>
  drule_all numeric_prefix_two >> strip_tac >>
  drule_all (Q.SPECL [`allow_own`, `own`] sym_bump_success_run_mode) >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  qexists `full` >>
  simp[stackModelTheory.stack_push_def, stackModelTheory.stack_pop_def,
    listTheory.SNOC_APPEND, rich_listTheory.BUTLASTN_APPEND2, listTheory.TAKE_APPEND1] >>
  rpt strip_tac >> gvs[]
QED

Theorem sym_bump_endpoint_compose_mode:
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  sym_steps_mode allow_own p env own (LENGTH (execute_plan fmp (xs ++ ys))) ss = SymOK ready /\
  sym_steps_mode allow_own p env own 2 ready = SymOK full /\
  sym_steps_mode allow_own p env own (LENGTH (execute_plan fmp (zs ++ ws))) full = SymOK final /\
  sym_kinds_ok cplan fn ret srest qs final /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  full.sym_mem_labels = ready.sym_mem_labels /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP full.sym_mem_labels b) ==>
  ?last. sym_steps_mode allow_own p env own
      (LENGTH (execute_plan fmp (xs ++ ys ++ bump_emit_ops ++ zs ++ ws))) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest qs last /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  `sym_steps_mode allow_own p env own (2 + LENGTH (execute_plan fmp (zs ++ ws))) ready = SymOK final` by
    (irule sym_steps_mode_compose >> goal_assum (drule_at Any) >> simp[]) >>
  qexists `final` >> pure_rewrite_tac[bump_plan_length] >>
  conj_tac >- (irule sym_steps_mode_compose >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem sym_bump_inst_symbolic_run_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [base_op; size_op] <= LENGTH (SND (emit_input_plan BUMP [base_op; size_op] nl ps)).ps_stack /\
  (!op. MEM op [base_op; size_op] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [base_op; size_op] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [base_op; size_op] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [base_op; size_op] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [base_op; size_op]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [base_op; size_op] /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  bridge_core lo code_ok cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> drule_all bump_plan_decompose >> strip_tac >>
  qmatch_asmsub_abbrev_tac `popmany_plan _ emitted` >>
  `ptr <> next` by metis_tac[genBlockSimTheory.codegen_ready_bump_outputs_distinct] >>
  `EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) [ptr;next]` by
    (gvs[listTheory.EVERY_MEM] >> rpt conj_tac >> strip_tac >>
     FIRST [qpat_assum `!op. MEM op ps.ps_stack ==> _` drule,
       qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _` drule] >> simp[]) >>
  `generated_plan_state_wf_marked sb emitted` by
    (drule_at (Pat `emit_input_plan _ _ _ _ = _`) regional_regular_outputs_marked_wf >>
     disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     disch_then (qspecl_then [`sb`, `[ptr;next]`] mp_tac) >> simp[Abbr `emitted`]) >>
  `(if inst.inst_outputs = [] \/ F then ([],emitted)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) emitted) = (pops,ps8)` by gvs[] >>
  `emitted.ps_stack = stack_pop 2 arranged.ps_stack ++ [Var ptr;Var next]` by
    simp[Abbr `emitted`, stackModelTheory.stack_push_def, listTheory.SNOC_APPEND] >>
  `(if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
    else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9)` by gvs[] >>
  drule_at (Pat `(if _ then _ else _) = (opts,ps9)`) sym_bump_postfix_applicability >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked sb emitted`)) >>
  disch_then (drule_at (Pat `(if _ then _ else _) = (pops,ps8)`)) >>
  disch_then (drule_at (Pat `qs = release_dead_spills _ _`)) >>
  disch_then (drule_at (Pat `MEM r cplan.cp_regions`)) >>
  disch_then (drule_at (Pat `emitted.ps_stack = _`)) >>
  disch_then (qspecl_then [`fn.fn_name`, `ctx`] mp_tac) >> simp[] >> strip_tac >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (gvs[Abbr `emitted`] >> metis_tac[allocMonoTheory.emit_input_plan_spill_base,
       allocMonoTheory.reorder_plan_spill_base]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  `emit_input_plan inst.inst_opcode [base_op; size_op] nl ps = (iops,prepared)` by simp[] >>
  drule (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO))
    (SPEC_ALL sym_frame_selected_prefix_paired_mode_conditional)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`sb`, `r`, `labs0`, `cplan.cp_initial_fmp`, `qs`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `sym_steps_mode allow_own prog env own _ ss = SymOK ready` >>
  rename1 `sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop)` >>
  `asm_block_at prog ready.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"]` by
    gvs[stackOpSimTheory.execute_plan_append, stackPlanGenTheory.bump_emit_ops_def,
      planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def,
      planExecTheory.dup_name_def, stackOpSimTheory.asm_block_at_append] >>
  `?base_val sz.
    operand_val (frame_view fn ra vs with vs_memory := cs.as_memory) lo base_op = SOME base_val /\
    operand_val (frame_view fn ra vs with vs_memory := cs.as_memory) lo size_op = SOME sz` by
    (irule bump_success_operand_values >>
     conj_tac >- simp[venomMemPropsTheory.eval_operand_with_memory,
       genFrameSimTheory.operand_val_memory_update] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `EVERY (\v. ~MEM (Var v) arranged.ps_stack /\ Var v NOTIN FDOM arranged.ps_spilled) [ptr;next]` by
    (drule_at (Pat `reorder_plan _ _ _ = _`) selected_prefix_outputs_absent >>
     disch_then (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     disch_then (qspec_then `[ptr;next]` mp_tac) >> gvs[]) >>
  `EVERY (\op. case op of Var x => x <> ptr /\ x <> next | _ => T) arranged.ps_stack /\
    (!op. op IN FDOM arranged.ps_spilled ==>
      case op of Var x => x <> ptr /\ x <> next | _ => T)` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >> Cases_on `op` >> gvs[] >> metis_tac[]) >>
  drule_at (Pat `venom_asm_rel _ arranged _ mid`) sym_bump_prepared_full_emit_core_mode >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
  disch_then (drule_at (Pat `inst.inst_opcode = BUMP`)) >>
  disch_then (drule_at (Pat `inst.inst_operands = _`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `arranged.ps_stack = _`)) >>
  disch_then (drule_at (Pat `ready.sym_stack = _`)) >>
  disch_then (qspecl_then [`sz`, `emitted`, `prog`, `own`, `env`, `ctx`, `code_ok`, `base_val`, `allow_own`] mp_tac) >> simp[] >>
  (impl_tac >- (gvs[Abbr `emitted`, codegen_ready_fn_def] >> metis_tac[])) >> strip_tac >>
  `asm_block_at prog full.sym_base.as_pc (execute_plan cplan.cp_initial_fmp (pops ++ opts))` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
      bump_emit_ops_def, execute_plan_def, exec_stack_op_def, dup_name_def] >>
  drule_at (Pat `(if _ then _ else _) = (opts,ps9)`) sym_bump_generated_postfix_sim_marked >>
  disch_then (drule_at (Pat `(if _ then _ else _) = (pops,ps8)`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ emitted full`)) >>
  disch_then (drule_at (Pat `emitted.ps_stack = _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ full.sym_base.as_pc _`)) >>
  disch_then (qspecl_then [`qs`, `env`, `closure_spill_byte ctx cplan fn.fn_name`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (rpt strip_tac >> qpat_assum `EVERY _ ops`
        (fn th => mp_tac (REWRITE_RULE [listTheory.EVERY_MEM] th)) >>
        disch_then (qspec_then `SOSpill off` mp_tac) >> simp[])
    >> metis_tac[listTheory.MEM_APPEND])) >> strip_tac >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  drule_all sym_bump_endpoint_compose_mode >> gvs[]
QED
