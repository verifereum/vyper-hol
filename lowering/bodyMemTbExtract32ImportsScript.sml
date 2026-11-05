(* Entry-reserved imports cannot name a newly emitted temporary. *)
Theory bodyMemTbExtract32Imports
Ancestors
  bodyMemTbExtract32Origin exprOperandVar emitHelper compileEnv exprLoweringProps

Theorem extract32_emit_reserved_local_exclusion:
  local_ptrs_reserved env sa /\ emit_op opc args sa = (Var v,sb) ==>
  !name sz. FLOOKUP env.ce_vars name <> SOME (PtrVar (Var v) sz)
Proof
  rpt strip_tac >> drule_all environment_var_not_fresh >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, not_fresh_at_def]
QED

Theorem extract32_emit_reserved_immutable_exclusion:
  local_ptrs_reserved env sa /\ emit_op opc args sa = (Var v,sb) ==>
  env.ce_imm_alloca <> SOME (Var v)
Proof
  rpt strip_tac >> drule_all local_ptrs_reserved_imm_base >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, not_fresh_at_def]
QED
