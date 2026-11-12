Theory bodyPtrIfExpCallShape
Ancestors intCallStep

(* Branch projections retain the allocation before argument staging.  The
   return descriptor is the function's physical return type, not ty. *)
Theorem compile_call_intcall_stack_shape:
  !cfn cenv ret_ty ty func_id args dret st v st' ret_count rbs pvs.
    compile_call cfn cenv ret_ty ty (IntCall func_id) args dret st = (v,st') /\
    cenv.ce_func_info (nsid_to_string func_id) = (ret_count,rbs,pvs) /\
    0 < ret_count ==>
    ?arg_vals st1 st2 invoke_args st3 rbuf results st4 u.
      compile_multi_vvs cfn cenv args st = (arg_vals,st1) /\
      compile_stage_intcall_args cenv arg_vals pvs (MAP expr_type args) st2 =
        (invoke_args,st3) /\
      compile_alloc_buffer (32 * ret_count) st1 = (rbuf,st2) /\
      emit_multi_op INVOKE
        (Label (internal_fn_label
          (cenv.ce_func_ids (nsid_to_string func_id))
          (nsid_to_string func_id)
          (cenv.ce_func_param_types (nsid_to_string func_id))
          cenv.ce_is_ctor) :: invoke_args) ret_count st3 = (results,st4) /\
      store_multi_results rbuf.buf_operand results 0 st4 = (u,st') /\
      v = LocatedValue (cenv.ce_func_return_type (nsid_to_string func_id))
                       (base_ptr rbuf)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_call_intcall_shape >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem compile_call_intcall_buffer_shape:
  !cfn cenv ret_ty ty func_id args dret st v st' rbs pvs.
    compile_call cfn cenv ret_ty ty (IntCall func_id) args dret st = (v,st') /\
    cenv.ce_func_info (nsid_to_string func_id) = (0,rbs,pvs) /\
    0 < rbs ==>
    ?arg_vals st1 st2 invoke_args st3 rbuf u.
      compile_multi_vvs cfn cenv args st = (arg_vals,st1) /\
      compile_stage_intcall_args cenv arg_vals pvs (MAP expr_type args) st2 =
        (invoke_args,st3) /\
      compile_alloc_buffer rbs st1 = (rbuf,st2) /\
      emit_void INVOKE
        (Label (internal_fn_label
          (cenv.ce_func_ids (nsid_to_string func_id))
          (nsid_to_string func_id)
          (cenv.ce_func_param_types (nsid_to_string func_id))
          cenv.ce_is_ctor) :: rbuf.buf_operand :: invoke_args) st3 = (u,st') /\
      v = LocatedValue (cenv.ce_func_return_type (nsid_to_string func_id))
                       (base_ptr rbuf)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_call_intcall_shape >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem compile_call_intcall_zero_shape:
  !cfn cenv ret_ty ty func_id args dret st v st' pvs.
    compile_call cfn cenv ret_ty ty (IntCall func_id) args dret st = (v,st') /\
    cenv.ce_func_info (nsid_to_string func_id) = (0,0,pvs) ==>
    ?arg_vals st1 invoke_args st3 u.
      compile_multi_vvs cfn cenv args st = (arg_vals,st1) /\
      compile_stage_intcall_args cenv arg_vals pvs (MAP expr_type args) st1 =
        (invoke_args,st3) /\
      emit_void INVOKE
        (Label (internal_fn_label
          (cenv.ce_func_ids (nsid_to_string func_id))
          (nsid_to_string func_id)
          (cenv.ce_func_param_types (nsid_to_string func_id))
          cenv.ce_is_ctor) :: invoke_args) st3 = (u,st') /\
      v = StackValue (cenv.ce_func_return_type (nsid_to_string func_id)) (Lit 0w)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_call_intcall_shape >>
  strip_tac >> gvs[] >> metis_tac[]
QED
