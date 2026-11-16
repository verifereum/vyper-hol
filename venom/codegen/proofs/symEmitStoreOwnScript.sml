(* Own-relation specializations of the shared BUMP and ISTORE kernels. *)
Theory symEmitStoreOwn
Ancestors symEmitSim asmSymBridge

Theorem sym_bump_source_emit_own_mode_conditional:
  (!n cs ss ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ssa_form fn /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  qs = ps with ps_stack := stack_push (Var next)
    (stack_push (Var ptr) (stack_pop 2 ps.ps_stack)) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] /\
  asm_steps slo (build_offset_to_pc p) p 2 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 2 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    sym_bump_source_emit_mode_conditional)
QED

Theorem sym_istore_prepared_safe_own_mode:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [dst; value] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  context_source_memory_writes_disjoint cplan inst vs ==>
  ?w off tail. ss.sym_stack = Val w :: Val off :: tail /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n off) 32 b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    fs[asm_sym_rel_own_def] >>
  drule_all sym_istore_prepared_safe_core >> simp[]
QED

Theorem sym_istore_source_emit_own_mode_conditional:
  (!n cs ss ss'. asm_sym_rel_own slo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own slo p env own cs' ss') /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [dst; value] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own slo p env own cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  context_source_memory_writes_disjoint cplan inst vs /\
  qs = ps with ps_stack := stack_pop 2 ps.ps_stack /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"] /\
  asm_steps slo (build_offset_to_pc p) p 2 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 2 ss = SymOK ss' /\
    asm_sym_rel_own slo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack` by
    fs[asm_sym_rel_own_def] >>
  drule_all (Q.INST [`R` |-> `asm_sym_rel_own slo p env own`]
    sym_istore_source_emit_mode_conditional) >> simp[]
QED
