(* Chronological allocation outputs cannot alias inherited old operands. *)
Theory bodyPtrBytestringBuiltinsAllocationSeparation
Ancestors
  bodyPtrBytestringBuiltinsAllocationOrigins
  bodyPtrBytestringBuiltinsParameterAges exprSafeOperand compileEnv venomInst

Theorem alloca_output_ne_safe_operand:
  safe_operand sa op /\
  alloca_output_interval sa.cs_next_var hi delta /\
  MEM i delta /\ i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs ==>
  op <> Var x
Proof
  rw[alloca_output_interval_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  strip_tac >> gvs[safe_operand_def, not_fresh_at_def] >>
  metis_tac[]
QED

Theorem alloca_output_ne_env_operand:
  env_operand_age ce sa /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar op (sz:num)) /\
  alloca_output_interval sa.cs_next_var hi delta /\
  MEM i delta /\ i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs ==>
  op <> Var x
Proof
  rpt strip_tac >>
  `safe_operand sa op` by metis_tac[env_operand_age_def] >>
  metis_tac[alloca_output_ne_safe_operand]
QED
