(* Support/layout probe only: no actual execution or target counterexample. *)
Theory bodyPtrMakeArrayScalarReturnProbe
Ancestors
  supportedProgram supportedExprs compileVyper exprLowering
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset
val B32 = ``BaseT (BytesT (Dynamic 32))``
val B64 = ``BaseT (BytesT (Dynamic 64))``
val W = ``TupleT [^B64; ^B32]``
val N = ``TupleT [^B32; ^B32]``
val emptyW = ``Builtin ^W (MakeArray NONE (Fixed 2))
  [Literal ^B64 (BytesL []); Literal ^B32 (BytesL [])]``
val callN = ``Call ^N (IntCall (NONE,"empty_wide")) [] NONE``
val tops = ``[
  FunctionDecl Internal Pure F F "empty_wide" [] ([] : expr list) ^W
    [Return (SOME ^emptyW)];
  FunctionDecl External Pure F F "read_empty" [] ([] : expr list) ^N
    [Return (SOME ^callN)]]``

Theorem scalar_return_support_gates:
  supported_value_type ^tops ^W /\
  supported_value_type ^tops ^N /\
  IS_SOME (supported_function_decl ^tops (NONE,"empty_wide") Internal) /\
  supported_function_return ^tops Internal ^W /\
  supported_return_layout ^W (Return (SOME ^emptyW)) /\
  supported_return_layout ^N (Return (SOME ^callN))
Proof
  EVAL_TAC
QED

Theorem scalar_return_supported_program:
  supported_program ^tops
Proof
  EVAL_TAC
QED

val pkg = ``package_external_fn ^tops F (assign_nkeys ^tops 0)
  (Pure,F,F,"read_empty",[],([] : expr list),^N,
   [Return (SOME ^callN)])``

Theorem scalar_return_call_annotation:
  expr_type ^callN = ^N
Proof
  EVAL_TAC
QED

Theorem scalar_return_packaged_call_layout:
  lowered_value_type (FST (SND ^pkg)) ^callN = ^W
Proof
  simp[lowered_value_type_def, package_external_fn_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_ce_func_return_type]
  >> EVAL_TAC
QED
