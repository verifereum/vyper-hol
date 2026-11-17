(* Subject-facing code-end ADD contracts.  The shared kernels remain in
   symEmitSim because its exact canonical corollaries depend on them. *)
Theory symEmitCodeEndOwn
Ancestors symEmitSim

Theorem sym_code_end_add_prepared_layout_mode:
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [op; Label "code_end"] /\ label_positions_ok inst /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = residual ++ selected /\
  (selected = [op; Label "code_end"] \/ selected = [Label "code_end"; op]) ==>
  ?w tail.
    (selected = [op; Label "code_end"] /\
     ss.sym_stack = Lab "code_end" 0 :: Val w :: tail) \/
    (selected = [Label "code_end"; op] /\
     ss.sym_stack = Val w :: Lab "code_end" 0 :: tail)
Proof
  MATCH_ACCEPT_TAC symEmitSimTheory.sym_code_end_add_prepared_layout_mode
QED

Theorem asm_sym_code_end_add_value_core:
  LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack /\
  ((ss.sym_stack = Lab "code_end" 0 :: Val w :: tail /\
    eval_operands [Label "code_end"; op] vs = SOME (TAKE 2 cs.as_stack)) \/
   (ss.sym_stack = Val w :: Lab "code_end" 0 :: tail /\
    eval_operands [op; Label "code_end"] vs = SOME (TAKE 2 cs.as_stack))) ==>
  eval_operand op vs = SOME w
Proof
  MATCH_ACCEPT_TAC symEmitSimTheory.asm_sym_code_end_add_value_core
QED

Theorem sym_code_end_add_prepared_safe_mode:
  inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ selected /\
  (selected = [op; Label "code_end"] \/ selected = [Label "code_end"; op]) /\
  EVERY (\at. at <> dead_stack_marker) selected /\
  (!at. MEM at selected ==>
    eval_operand at (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo at) ==>
  ?w tail.
    (ss.sym_stack = Lab "code_end" 0 :: Val w :: tail \/
     ss.sym_stack = Val w :: Lab "code_end" 0 :: tail)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all symEmitSimTheory.sym_code_end_add_prepared_safe_mode >> simp[]
QED

Theorem sym_code_end_add_source_emit_mode_conditional:
  (!n cs ss ss'. R cs ss /\ sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\ R cs' ss') /\
  inst.inst_opcode = ADD /\ inst.inst_operands = [op; Label "code_end"] /\
  inst.inst_outputs = [x] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  R cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ selected /\
  (selected = [op; Label "code_end"] \/ selected = [Label "code_end"; op]) /\
  EVERY (\at. at <> dead_stack_marker) selected /\
  (!at. MEM at selected ==>
    eval_operand at (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo at) /\
  sym_data_label p env "code_end" /\
  qs = ps with ps_stack := stack_push (Var x) (stack_pop 2 ps.ps_stack) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "ADD"] /\
  asm_steps slo (build_offset_to_pc p) p 1 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC symEmitSimTheory.sym_code_end_add_source_emit_mode_conditional
QED
