Theory bodyFullExtCallSavedOperand
Ancestors
  exprOperandVar exprLowering exprLoweringProps context emitHelper venomInst compileEnv

(* Retagging preserves the operand. The word snapshot can instead allocate a
   new variable, so use the unwrap counter at the snapshot endpoint. *)
Theorem extcall_saved_operand_not_fresh:
  compile_expr ce et e si = (vv,sm) /\ local_ptrs_reserved ce si /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) ==>
  !x. vv_operand saved = Var x ==> not_fresh_at ss x
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `vv_operand (ext_call_arg_value ty vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def, vv_operand_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def] >> IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> fs[comp_return_def] >>
      strip_tac >> gvs[vv_operand_def] >>
      `case ext_call_arg_value ty vv of
         StackValue tag op0 => (!x. op0 = Var x ==> not_fresh_at sm x)
       | LocatedValue tag p => (!x. p.ptr_operand = Var x ==> not_fresh_at sm x)` by
        (Cases_on `ext_call_arg_value ty vv` >> gvs[vv_operand_def]) >>
      metis_tac[compiler_unwrap_value_var]) >>
  Cases_on `copy` >> simp[comp_bind_def, comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
      metis_tac[compiler_materialize_vv_var]) >>
  strip_tac >> gvs[]
QED
