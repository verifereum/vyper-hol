(* Discharged BUMP execution over supplied labels and fixed own code. *)
Theory symBumpOwn
Ancestors symBumpRunOwn symEmitOwn asmSymModeOwn codegenSymRel asmSymBridge

Theorem sym_bump_prepared_full_emit_own:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ptr <> next /\
  ssa_form fn /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ asm_sym_rel_own lo p env own cs (ss with sym_stack := top) /\
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
  drule_all (REWRITE_RULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
      sym_bump_prepared_full_emit_core_mode)) >> simp[]
QED

Theorem sym_bump_inst_symbolic_run_own:
  code_labels_agree prog lo /\
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
  sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
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
  qpat_x_assum `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [sym_frame_inv_own_def]) >>
  drule_all (REWRITE_RULE [asm_sym_rel_core_own]
    (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
      sym_bump_inst_symbolic_run_mode_conditional)) >> simp[]
QED
