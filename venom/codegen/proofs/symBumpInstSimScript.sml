Theory symBumpInstSim
Ancestors
  symInstPieces symPostfixSim symEmitSim deepInstSim deepResidualSim symBumpRunOwn
  genBlockSim stackPlanGen planExec codegenSymRel asmSymBridge asmSymSem
  fnPlanPrefix genFrameSim allocMono venomWf fnBlockPlanStaticRegion symBumpOwn

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
  ACCEPT_TAC symBumpRunOwnTheory.bump_plan_decompose
QED

Theorem sym_bump_prepared_full_emit:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ptr <> next /\
  ssa_form fn /\ opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ asm_sym_rel p env cs (ss with sym_stack := top) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top) /\
  venom_asm_rel (SND (compute_label_offsets p)) ps vs cs /\
  ps.ps_stack = residual ++ [base_op; size_op] /\
  base_op <> dead_stack_marker /\ size_op <> dead_stack_marker /\
  operand_val vs (SND (compute_label_offsets p)) base_op = SOME base_val /\
  operand_val vs (SND (compute_label_offsets p)) size_op = SOME sz /\
  EVERY (\op. case op of Var x => x <> ptr /\ x <> next | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> ptr /\ x <> next | _ => T) /\
  qs = ps with ps_stack := stack_push (Var next)
    (stack_push (Var ptr) (stack_pop 2 ps.ps_stack)) /\
  ss.sym_stack = top ++ srest /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] ==>
  ?full. sym_steps p env 2 ss = SymOK full /\
    full.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs full /\
    qs.ps_stack = residual ++ [Var ptr;Var next]
Proof
  strip_tac >>
  drule_all (REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      sym_bump_prepared_full_emit_core_mode)) >> simp[]
QED

Theorem selected_prefix_outputs_absent:
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= LENGTH prepared.ps_stack /\ LENGTH operands <= 17 /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) outputs ==>
  EVERY (\v. ~MEM (Var v) arranged.ps_stack /\ Var v NOTIN FDOM arranged.ps_spilled) outputs
Proof
  ACCEPT_TAC symBumpRunOwnTheory.selected_prefix_outputs_absent
QED

Theorem bump_plan_length[local]:
  LENGTH (execute_plan fmp (xs ++ ys ++ bump_emit_ops ++ zs ++ ws)) =
  LENGTH (execute_plan fmp (xs ++ ys)) + (2 + LENGTH (execute_plan fmp (zs ++ ws)))
Proof
  ACCEPT_TAC symBumpRunOwnTheory.bump_plan_length
QED

Theorem bump_success_operand_values[local]:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [bop;sop] /\
  step_inst fuel ctx inst s = OK t /\
  (!op. MEM op [bop;sop] ==> eval_operand op s = operand_val s lo op) ==>
  ?bv sz. operand_val s lo bop = SOME bv /\ operand_val s lo sop = SOME sz
Proof
  ACCEPT_TAC symBumpRunOwnTheory.bump_success_operand_values
QED

Theorem sym_bump_endpoint_compose[local]:
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  sym_steps p env (LENGTH (execute_plan fmp (xs ++ ys))) ss = SymOK ready /\
  sym_steps p env 2 ready = SymOK full /\
  sym_steps p env (LENGTH (execute_plan fmp (zs ++ ws))) full = SymOK final /\
  sym_kinds_ok cplan fn ret srest qs final /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  full.sym_mem_labels = ready.sym_mem_labels /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP full.sym_mem_labels b) ==>
  ?last. sym_steps p env
      (LENGTH (execute_plan fmp (xs ++ ys ++ bump_emit_ops ++ zs ++ ws))) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest qs last /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [sym_frame_inv_def]) >>
  drule_all (REWRITE_RULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`] sym_bump_endpoint_compose_mode)) >> simp[]
QED

Theorem sym_bump_inst_symbolic_run:
  lo = SND (compute_label_offsets prog) /\
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
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\
    sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by
    (rpt strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [sym_frame_inv_def]) >>
  drule_all (REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      sym_bump_inst_symbolic_run_mode_conditional)) >> simp[]
QED
