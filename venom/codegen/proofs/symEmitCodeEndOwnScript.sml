(* Subject-facing code-end ADD contracts.  The shared kernels remain in
   symEmitSim because its exact canonical corollaries depend on them. *)
Theory symEmitCodeEndOwn
Ancestors symEmitSim

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
