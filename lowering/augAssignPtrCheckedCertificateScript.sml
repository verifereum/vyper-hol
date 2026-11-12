Theory augAssignPtrCheckedCertificate
Ancestors augAssignPtrScalarCertificate exprLowering exprLoweringProps
  emitHelper compileEnv venomInst list rich_list pred_set

Theorem compile_safe_add_sub_scalar_code:
  (compile_safe_add x y ty st = (op, st') \/
   compile_safe_sub x y ty st = (op, st')) /\
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A (emitted_insts st st') /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) (emitted_insts st st')))) op
Proof
  Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_add_def, compile_safe_sub_def, clamp_and_return_def, compile_clamp_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def,
       emitted_insts_def, DROP_LENGTH_APPEND, scalar_code_def,
       scalar_shape_def, scalar_binary_def, scalar_unary_def,
       scalar_available_def, mk_inst_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, scalar_code_def,
       scalar_shape_def, scalar_binary_def, scalar_unary_def,
       scalar_available_def] >> metis_tac[IN_SING]
QED

(* Fresh output and compiler-state frames are already exported by
   straight_fresh_checked (exprSimArith) and straight_fresh_def.  The same
   emitted_insts st st' list is used by compile_safe_add_run and
   compile_safe_sub_run; no alternate numeric execution is needed. *)
