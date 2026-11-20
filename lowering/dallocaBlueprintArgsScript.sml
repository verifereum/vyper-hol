Theory dallocaBlueprintArgs
Ancestors
  dallocaCreateBlueprint builtinCreate context exprLowering exprLoweringProps
  emitHelper emitHelperProps compileEnv loweringStateRelDefs loweringPosts
  createMemoryInterface valueEncodingProps vyperTyping vyperValue exprBopSimProps
  vyperTypeExtCallSoundness vyperTypeSystem exprSimHyps
  exprSimAbiEncodeArgsPhysicalCapacity abiEncodeValuesPhases
  venomExecSemantics venomInst venomState list rich_list words finite_map

Theorem create_blueprint_check_operand:
  compile_create_blueprint_check is_lit target offset ca = (code_op,cb) ==>
  code_op = Var ("%" ++ toString (ca.cs_next_var + (if is_lit then 1 else 2))) /\
  cb.cs_next_var = ca.cs_next_var + 3 /\
  (!x. code_op = Var x ==> not_fresh_at cb x)
Proof
  Cases_on `is_lit` >>
  simp[compile_create_blueprint_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> rw[not_fresh_at_def] >>
  irule fresh_var_distinct >> decide_tac
QED

Theorem create_blueprint_empty_args_prefix:
  compile_create_blueprint_args cfn ce F later_es [] cb = ((args_ptr,args_len),sa) ==>
  sa = cb /\ args_ptr = Lit 0w /\ args_len = Lit 0w /\
  eval_operand args_len s = SOME 0w /\ w2n (0w:bytes32) < 2 ** 64
Proof
  simp[compile_create_blueprint_args_def, comp_return_def, eval_operand_def]
QED

Theorem create_blueprint_encoded_args_compile:
  args <> [] /\
  compile_create_blueprint_args cfn ce F later_es args cb = ((args_ptr,args_len),sa) ==>
  ?vals c1 buf c2.
    compile_create_ctor_args cfn ce args cb = (vals,c1) /\
    compile_alloc_buffer
      (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) c1 =
      (buf,c2) /\
    compile_abi_encode_values_to_buf ce buf.buf_operand
      (ZIP (vals,MAP (lowered_value_type ce) args)) c2 = (args_len,sa) /\
    args_ptr = buf.buf_operand
Proof
  Cases_on `args` >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum $ drule_at Any)
QED

(* Allocation is checked against annotations, while saved rows have their
   physical types. The child expression preconditions provide the widening. *)
Theorem create_ctor_args_abi_bound:
  EVERY (\e. expr_body_pre ce cx env e es) args ==>
  abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) <=
  abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))
Proof
  strip_tac >> irule (cj 2 abi_args_fits_size_bound) >>
  pop_assum mp_tac >> Induct_on `args` >> simp[arg_type_fits_def] >>
  metis_tac[expr_body_pre_lowered_fits]
QED

Theorem raw_create_bytecode_bound:
  expr_body_pre ce cx env bytecode es /\
  expr_type bytecode = BaseT (BytesT (Dynamic bound)) ==>
  bytelike_type_bound (lowered_value_type ce bytecode) <= bound
Proof
  strip_tac >> drule expr_body_pre_lowered_fits >> asm_rewrite_tac[] >>
  Cases_on `lowered_value_type ce bytecode` >> simp[arg_type_fits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[arg_type_fits_def, bytelike_type_bound_def, vyperASTTheory.bound_length_def]
QED

(* RawCreate writes the ABI suffix at the runtime end of the copied
   initcode. Both windows are inside the same registered allocation. *)
Theorem raw_create_initcode_prefix_frame:
  window_phase ctx func st en ids [(b+len,n)] s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas owner = SOME (b,cap) /\ owner NOTIN ids /\
  len + n <= cap ==>
  FLOOKUP t.vs_allocas owner = SOME (b,cap) /\
  mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory
Proof
  strip_tac >>
  mp_tac (Q.INST [`q` |-> `b`, `n` |-> `len`, `sz` |-> `cap`,
    `outs` |-> `[(b+len,n)]`, `tn'` |-> `tn`]
    abi_encode_values_registered_window) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[]
QED

Theorem create_blueprint_raw_args_prefix:
  compile_create_blueprint_check is_lit target offset ca = (code_op,cb) /\
  run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
  cfn ce (expr_type e) e cb = (arg_vv,c_arg) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later_es) arg_vv c_arg =
    (saved_vv,c_snap) /\
  unwrap_value ce saved_vv c_snap = (raw_ptr,cm) /\
  compile_create_blueprint_args cfn ce T later_es [e] cb = ((args_ptr,args_len),sa) /\
  cb.cs_next_var <= cm.cs_next_var /\
  expr_post H ctx func ce cx e es cb cm s1 es' v raw_ptr sv /\
  expr_type e = BaseT (BytesT (Dynamic maxlen)) /\
  value_has_type (BaseTV (BytesT (Dynamic maxlen))) v /\
  maxlen < 2 ** 64 /\
  run_inst_seq (emitted_insts cm sa) sv = OK s2 ==>
  eval_operand code_op s2 = eval_operand code_op s1 /\
  ?args. eval_operand args_len s2 = SOME args /\ w2n args < 2 ** 64
Proof
  Cases_on `is_lit` >> strip_tac >> drule_all create_blueprint_check_frame >>
  disch_then (qx_choose_then `code` strip_assume_tac) >>
  drule create_blueprint_check_operand >> strip_tac >>
  `eval_operand code_op sv = SOME code` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`cb`, `s1`] >>
     fs[expr_post_def]) >>
  `!x. code_op = Var x ==> not_fresh_at cm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `cb` >> simp[]) >>
  `?bs. v = BytesV bs /\ LENGTH bs <= maxlen` by
    (Cases_on `v` >> fs[value_has_type_def]) >> gvs[] >>
  `maxlen < dimword (:256)` by
    (fs[dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  drule raw_call_bytes_slot_size_bound >> strip_tac >>
  `?p. eval_operand raw_ptr sv = SOME p /\
       mload (w2n p) sv = n2w (LENGTH bs)` by
    (fs[expr_post_def, expr_val_rel_def, is_bytestring_type_def,
        is_word_type_def, evaluate_type_def, valueEncodingDefsTheory.val_in_memory_def,
        mem_word_at_eq_mload]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `w2n (n2w (LENGTH bs) : bytes32) < 2 ** 64` by
    (simp[w2n_n2w] >> decide_tac) >>
  qpat_x_assum `compile_create_blueprint_args _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_return_def] >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ sv = _` mp_tac >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[] >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read1_def, exec_pure2_def, bind_outputs_def, eval_operand_def,
      lookup_var_update_var, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, fresh_var_distinct, AllCaseEqs()] >>
  fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem create_blueprint_raw_size_prefix:
  compile_create_blueprint_check T target offset ca = (code_op,cb) /\
  run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
  cfn ce (expr_type e) e cb = (arg_vv,c_arg) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later_es) arg_vv c_arg =
    (saved_vv,c_snap) /\
  unwrap_value ce saved_vv c_snap = (raw_ptr,cm) /\
  compile_create_blueprint_args cfn ce T later_es [e] cb = ((args_ptr,args_len),sa) /\
  cb.cs_next_var <= cm.cs_next_var /\
  expr_post H ctx func ce cx e es cb cm s1 es' v raw_ptr sv /\
  expr_type e = BaseT (BytesT (Dynamic maxlen)) /\
  value_has_type (BaseTV (BytesT (Dynamic maxlen))) v /\ maxlen < 2 ** 64 /\
  run_inst_seq (emitted_insts cm sa) sv = OK s2 /\
  emit_op ADD [code_op;args_len] sa = (size_op,sb) /\
  run_inst_seq (emitted_insts sa sb) s2 = OK t ==>
  ?size.
    eval_operand size_op t = SOME size /\
    w2n size <= 2 ** 255 + 2 ** 64 /\
    venomLayout$ceil32 (w2n size) <= 2 ** 255 + 2 ** 64 /\
    t.vs_accounts = s2.vs_accounts /\
    t.vs_call_ctx = s2.vs_call_ctx /\ t.vs_fmp = s2.vs_fmp
Proof
  strip_tac >> drule_all create_blueprint_raw_args_prefix >> strip_tac >>
  irule create_blueprint_prefix >> rpt (goal_assum $ drule_at Any)
QED

Theorem create_blueprint_empty_size_prefix:
  compile_create_blueprint_check T target offset ca = (code_op,cb) /\
  run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
  compile_create_blueprint_args cfn ce F later_es [] cb = ((args_ptr,args_len),sa) /\
  emit_op ADD [code_op;args_len] sa = (size_op,sb) /\
  run_inst_seq (emitted_insts sa sb) s1 = OK t ==>
  ?size.
    eval_operand size_op t = SOME size /\
    w2n size <= 2 ** 255 + 2 ** 64 /\
    venomLayout$ceil32 (w2n size) <= 2 ** 255 + 2 ** 64 /\
    t.vs_accounts = s1.vs_accounts /\
    t.vs_call_ctx = s1.vs_call_ctx /\ t.vs_fmp = s1.vs_fmp
Proof
  strip_tac >> drule create_blueprint_empty_args_prefix >>
  disch_then (qspec_then `s1` strip_assume_tac) >>
  mp_tac (Q.SPECL [`target`, `offset`, `ca`, `code_op`, `cb`,
    `s0`, `s1`, `s1`, `args_len`, `0w:bytes32`, `sa`, `size_op`, `sb`, `t`]
    create_blueprint_prefix) >>
  asm_simp_tac bool_ss []
QED
