(* The pure suffix disables composite copies, not word unwrapping. *)
Theory bodyFullExtCallRequestSnapshot
Ancestors
  exprLowering

Theorem extcall_snapshot_no_copy:
  ~exprs_can_mutate cenv tail ==>
  compile_snapshot_vv cenv (exprs_can_mutate cenv tail)
    (ext_call_arg_value ty vv) =
  (if is_word_type (vv_type (ext_call_arg_value ty vv)) then
     comp_bind (unwrap_value cenv (ext_call_arg_value ty vv))
       (\op. comp_return (StackValue (vv_type (ext_call_arg_value ty vv)) op))
   else comp_return (ext_call_arg_value ty vv))
Proof
  simp[compile_snapshot_vv_def]
QED
