(* Reading GAS changes only the source gas observations. *)
Theory s1PrefixMsgGas
Ancestors
  s1PrefixFrame s1PrefixDefs vyperStorageTrace vyperInterpreter
  vyperState vyperContext list

Theorem compile_msg_gas_sim_prefix:
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  rw[expr_sim_prefix_def, expr_vv_sim_prefix_def,
     expr_sim_full_pre_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  rpt gen_tac >> Cases_on `gobs` >>
  simp[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
       check_def, assert_def, bind_def, ignore_bind_def, next_gas_reading_def,
       read_result_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED
