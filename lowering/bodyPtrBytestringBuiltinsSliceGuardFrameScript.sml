Theory bodyPtrBytestringBuiltinsSliceGuardFrame
Ancestors
  bodyPtrBytestringBuiltinsSliceGuardFixture bodyPtrBytestringBuiltinsPtrFrame
  bodyPtrPreds bodyPtrDefs exprSimHypsDefs bodyPtrBytestringBuiltinsSourceFrame

(* AST abbreviation only, to keep the same closed fixture visible at each boundary. *)
Definition slice_guard_expr_def:
  slice_guard_expr = Builtin (BaseT (BytesT (Dynamic 1))) (Slice 1)
    [slice_guard_source; Literal (BaseT (UintT 256)) (IntL 0);
     Literal (BaseT (UintT 256)) (IntL 1)]
End

Theorem slice_guard_head_ptr_ok:
  !cx. body_expr_ptr_ok cx slice_guard_source
Proof
  simp[body_expr_ptr_ok_def, slice_guard_source_no_body_pre]
QED

Theorem slice_guard_args_ptr_ok:
  !cx tail. body_exprs_ptr_ok cx (slice_guard_source::tail)
Proof
  simp[body_exprs_ptr_ok_def, slice_guard_head_ptr_ok, slice_guard_no_success]
QED

Theorem slice_guard_arity:
  builtin_args_length_ok (Slice 1) 3
Proof
  EVAL_TAC
QED

Theorem slice_guard_body_pre:
  expr_body_pre order_ptr_env order_ptr_cx order_ptr_tenv
    slice_guard_expr order_ptr_source
Proof
  `int_calls_expr slice_guard_expr = [] /\
   byte_widths_expr slice_guard_expr /\ ~expr_has_evm_run slice_guard_expr` by EVAL_TAC >>
  simp[expr_body_pre_def, order_ptr_sim_inv, order_ptr_call_safety] >>
  simp[slice_guard_expr_def, slice_guard_slice_typed, slice_guard_slice_alloc_limits] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[order_ptr_cx_def, order_frame_cx_def,
       gasContextTheory.cx_tops_def, vyperContextTheory.get_tenv_def,
       vyperContextTheory.get_module_code_def] >>
  EVAL_TAC >> simp[]
QED

Theorem slice_guard_frame_obligation:
  body_expr_ptr_ok order_ptr_cx slice_guard_expr ==>
  !d PG func ty.
    expr_sim_ptr d order_frame_unit.cu_context PG func order_ptr_env
      order_ptr_cx ty slice_guard_expr order_ptr_source /\
    expr_vv_sim_ptr d order_frame_unit.cu_context PG func order_ptr_env
      order_ptr_cx ty slice_guard_expr order_ptr_source
Proof
  simp[body_expr_ptr_ok_def] >>
  metis_tac[order_ptr_body_inv, slice_guard_body_pre]
QED
