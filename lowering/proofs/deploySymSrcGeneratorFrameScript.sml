Theory deploySymSrcGeneratorFrame
Ancestors
  deploySymSrcFrameContext deploySymSrcFrameABI deploySymSrcFrameExprHelpers
  deploySymSrcFrameExpr deploySymSrcFrameStmtModule runtimeSymSrcInternalFunction
  deploySymSrcBlockFrame loweringShapeDefs compileEnv list

val _ = augment_srw_ss [rewrites [
  deploy_blocks_frame_binop, deploy_blocks_frame_unwrap_value,
  deploy_blocks_frame_lower_value, deploy_blocks_frame_materialize_vv,
  deploy_blocks_frame_snapshot_vv, deploy_blocks_frame_ifexp_arm,
  deploy_blocks_frame_addmod_names, deploy_blocks_frame_mulmod_names,
  deploy_blocks_frame_powmod256_names, deploy_blocks_frame_dynarray_pop,
  deploy_blocks_frame_dynarray_append, deploy_blocks_frame_multi_exprs,
  deploy_blocks_frame_acc, deploy_blocks_frame_var_array_membership,
  deploy_blocks_frame_array_membership_loop, deploy_blocks_frame_builtin_len,
  deploy_blocks_frame_concat, deploy_blocks_frame_make_tuple,
  deploy_blocks_frame_make_array, deploy_blocks_frame_make_array_elems,
  deploy_blocks_frame_bytestring_widen_copy, deploy_blocks_frame_store_abi_tuple,
  deploy_blocks_frame_abi_encode_args, deploy_blocks_frame_subscript,
  deploy_blocks_frame_attribute, deploy_blocks_frame_struct_lit,
  deploy_blocks_frame_get_target_ptr,
  deploy_blocks_frame_call, deploy_blocks_frame_call_internal,
  deploy_blocks_frame_call_external, deploy_blocks_frame_call_send,
  deploy_blocks_frame_call_raw_revert, deploy_blocks_frame_call_selfdestruct,
  deploy_blocks_frame_call_raw, deploy_blocks_frame_call_raw_calldata,
  deploy_blocks_frame_call_raw_log, deploy_blocks_frame_call_raw_log_pair,
  deploy_blocks_frame_create_call, deploy_blocks_frame_raw_create,
  deploy_blocks_frame_create_snapshot, deploy_blocks_frame_create_blueprint_args,
  deploy_blocks_frame_create_ctor_tuple, deploy_blocks_frame_ext_call_args,
  deploy_blocks_frame_extcall_store_args, deploy_blocks_frame_ext_call_kwargs,
  deploy_blocks_frame_ext_call_kwarg, deploy_blocks_frame_create_salt,
  deploy_blocks_frame_array_subscript, deploy_blocks_frame_stage_intcall_args,
  deploy_blocks_frame_external_call_kwargs, deploy_blocks_frame_default_return_path,
  deploy_blocks_frame_extcall_store_values, deploy_blocks_frame_multi_vvs,
  deploy_blocks_frame_return_value_decode,
  deploy_blocks_frame_create_copy, deploy_blocks_frame_create_blueprint,
  deploy_blocks_frame_create_blueprint_append, deploy_blocks_frame_msg_data_to_memory,
  deploy_blocks_frame_as_stack_val, deploy_blocks_frame_as_ptr_val]];

Theorem deploy_blocks_frame_create_call_closed:
  (!ty e. deploy_blocks_frame (cf ce ty e)) ==>
  deploy_blocks_frame (compile_create_call cf ce ck salt rof args)
Proof
  strip_tac >> irule deploy_blocks_frame_create_call >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> simp[]
QED

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_create_call_closed]];

Theorem deploy_blocks_frame_lower_contracts:
  !ce. deploy_expr_lower_contract ce /\ deploy_builtin_lower_contract ce /\
       deploy_type_lower_contract ce
Proof
  gen_tac >> pure_rewrite_tac[deploy_expr_lower_contract_def,
                 deploy_builtin_lower_contract_def,
                 deploy_type_lower_contract_def] >>
  rpt conj_tac >> gen_tac >> strip_tac >> rpt conj_tac >> rpt gen_tac >> simp[] >>
  irule deploy_blocks_frame_call >> simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >> simp[]
QED

Theorem deploy_blocks_frame_compile_expr[simp]:
  deploy_blocks_frame (compile_expr ce ty e)
Proof
  irule deploy_blocks_frame_compile_expr_cond >>
  simp[deploy_blocks_frame_lower_contracts]
QED

val _ = augment_srw_ss [rewrites [
  deploy_blocks_frame_load_tuple_elements, deploy_blocks_frame_declare_local,
  deploy_blocks_frame_declare_stmt_local, deploy_blocks_frame_return_unlock,
  deploy_blocks_frame_internal_return, deploy_blocks_frame_external_return,
  deploy_blocks_frame_internal_return_from_env,
  deploy_blocks_frame_revert_with_reason, deploy_blocks_frame_reason_message,
  deploy_blocks_frame_log_save_arg, deploy_blocks_frame_log_eval_all,
  deploy_blocks_frame_log_topic_ops, deploy_blocks_frame_log_store_data,
  deploy_blocks_frame_tuple_load_all, deploy_blocks_frame_store_at_loc,
  deploy_blocks_frame_assign_value, deploy_blocks_frame_tuple_store_all,
  deploy_blocks_frame_tuple_unpack, deploy_blocks_frame_iter_elem_copy]];

Theorem deploy_blocks_frame_stmts_mutual:
  (!ce lc ty st. deploy_blocks_frame (compile_stmt ce lc ty st)) /\
  (!ce lc ty ss. deploy_blocks_frame (compile_stmts ce lc ty ss))
Proof
  irule deploy_blocks_frame_stmt_cond >> rpt conj_tac >> rpt gen_tac >> simp[]
QED

Theorem deploy_blocks_frame_compile_stmts[simp]:
  deploy_blocks_frame (compile_stmts ce lc ty ss)
Proof
  simp[deploy_blocks_frame_stmts_mutual]
QED

Theorem deploy_blocks_frame_internal_function[simp]:
  deploy_blocks_frame (compile_internal_function ce params has_buf nr key trans view
                                               ctor len ss ret)
Proof
  irule deploy_blocks_frame_internal_function_cond >> simp[]
QED

Theorem deploy_sym_internal_function:
  !ce tops bindings ss ret params has_buf nr key trans view ctor len s u s'.
  runtime_sym_env ce /\ supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists is_self_code ss /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop
     (case ret of SOME ty => ty | NONE => BaseT BoolT) ss) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_alloc_buffer n s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s')) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_fixed_region_with_id n s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\
     ~is_label_operand (SND v).buf_operand) /\
  EVERY deploy_sym_inst (state_insts s) /\ s.cs_current_insts = [] /\
  compile_internal_function ce params has_buf nr key trans view ctor len
    ss ret s = (u,s') ==>
  EVERY deploy_sym_inst (state_insts s')
Proof
  rpt strip_tac >>
  qabbrev_tac `s0 = s with cs_blocks := []` >>
  Cases_on `compile_internal_function ce params has_buf nr key trans view ctor len ss ret s0` >>
  rename1 `_ = (v,t)` >>
  `EVERY runtime_sym_inst (state_insts s0)` by
    simp[Abbr `s0`, state_insts_def, all_blocks_def] >>
  `EVERY runtime_sym_inst (state_insts t)` by
    (drule_all runtime_sym_internal_function >> simp[]) >>
  `EVERY (\bb. EVERY deploy_sym_inst bb.bb_instructions) s.cs_blocks` by
    gvs[state_insts_def, all_blocks_def, EVERY_APPEND, EVERY_FLAT, EVERY_MAP] >>
  `s0.cs_blocks = []` by simp[Abbr `s0`] >>
  `s0 with cs_blocks := s.cs_blocks = s` by simp[Abbr `s0`] >>
  drule_at (Pat `m s = (x,t)`) deploy_blocks_frame_transfer >>
  disch_then (qspec_then `s.cs_blocks` mp_tac) >> simp[]
QED
