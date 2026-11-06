(* Entry-reserved imports cannot name a newly emitted temporary. *)
Theory bodyMemTbExtract32Imports
Ancestors
  bodyMemTbExtract32Origin exprOperandVar emitHelper compileEnv exprLoweringProps exprLowering context

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

Theorem extract32_compare_old_register_exclusion:
  compile_compare cmp x y ty sa = (r,sb) /\
  not_fresh_at sa v /\ x <> Var v /\ y <> Var v ==>
  ?delta. sb.cs_current_insts = sa.cs_current_insts ++ delta /\
          EVERY (\i. ~MEM v i.inst_outputs) delta /\
          r <> Var v /\ EVERY (\i. ~MEM (Var v) i.inst_operands) delta
Proof
  Cases_on `cmp` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_inst_def, fresh_id_def,
       fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
                                arithmeticTheory.LESS_EQ_ADD]
QED

(* Module lookup accepts static locations only; PtrVar falls through to INVALID. *)
Theorem extract32_toplevel_operand_literal:
  ?w. vv_operand (FST (compile_expr env ty (TopLevelName ann nsid) sa)) = Lit w
Proof
  simp[Once compile_expr_def] >>
  Cases_on `FLOOKUP env.ce_module_vars nsid` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_inst_def,
      fresh_id_def, emit_def, vv_operand_def, mk_ptr_def] >>
  Cases_on `x` >>
  simp[vv_operand_def, mk_ptr_def, emit_inst_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def]
QED

Theorem extract32_module_target_base_literal:
  ?w. compile_target_base env (TopLevelNameTarget nsid) = Lit w
Proof
  simp[compile_target_base_def] >>
  Cases_on `FLOOKUP env.ce_module_vars nsid` >> simp[] >>
  Cases_on `x` >> simp[]
QED
