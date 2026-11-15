Theory dallocaBlueprintArgs
Ancestors
  dallocaCreateBlueprint builtinCreate context exprLowering exprLoweringProps
  emitHelper emitHelperProps compileEnv loweringStateRelDefs loweringPosts
  createMemoryInterface valueEncodingProps vyperTyping vyperValue exprBopSimProps
  vyperTypeExtCallSoundness
  abiEncoderWindowRun abiEncoderWindowContract abiTypeBoundProps
  venomExecSemantics venomInst venomState list rich_list words finite_map

Theorem create_blueprint_check_operand:
  compile_create_blueprint_check target offset ca = (code_op,cb) ==>
  code_op = Var ("%" ++ toString (ca.cs_next_var + 1)) /\
  cb.cs_next_var = ca.cs_next_var + 3 /\
  (!x. code_op = Var x ==> not_fresh_at cb x)
Proof
  simp[compile_create_blueprint_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> rw[not_fresh_at_def] >>
  irule fresh_var_distinct >> decide_tac
QED

Theorem create_blueprint_empty_args_prefix:
  compile_create_blueprint_args cfn ce F [] cb = ((args_ptr,args_len),sa) ==>
  sa = cb /\ args_ptr = Lit 0w /\ args_len = Lit 0w /\
  eval_operand args_len s = SOME 0w /\ w2n (0w:bytes32) < 2 ** 64
Proof
  simp[compile_create_blueprint_args_def, comp_return_def, eval_operand_def]
QED

Theorem create_blueprint_encoded_args_compile:
  args <> [] /\
  compile_create_blueprint_args cfn ce F args cb = ((args_ptr,args_len),sa) ==>
  ?buf c1 src c2.
    compile_alloc_buffer
      (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) cb =
      (buf,c1) /\
    compile_create_ctor_tuple cfn ce args c1 = (src,c2) /\
    compile_abi_encode_to_buf buf.buf_operand src
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
      c2 = (args_len,sa) /\ args_ptr = buf.buf_operand
Proof
  Cases_on `args` >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum $ drule_at Any)
QED

Theorem create_blueprint_encoded_check_operand:
  compile_create_blueprint_check target offset ca = (Var code_name,cb) /\
  compile_alloc_buffer capacity cb = (buf,c1) /\
  compile_create_ctor_tuple cfn ce args c1 = (src,c2) /\
  (!ce' ty e st. ci_mono st (SND (cfn ce' ty e st))) ==>
  not_fresh_at c2 code_name
Proof
  strip_tac >> drule create_blueprint_check_operand >> strip_tac >>
  `ci_mono cb c1` by
    (mp_tac (Q.SPECL [`capacity`, `cb`] ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono c1 c2` by
    (mp_tac (Q.SPECL [`cfn`, `ce`, `args`, `c1`]
       ci_mono_compile_create_ctor_tuple) >> simp[]) >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `cb` >>
  fs[ci_mono_def] >> decide_tac
QED

(* The constructor-tuple producer supplies the typed input window and the
   captured register at s_tup. This theorem executes the encoder stage. *)
Theorem create_blueprint_encoded_args_prefix:
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
    c2 = (args_len,sa) /\
  abi_encoder_window_pre ctx func c2 sa dst src
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
    (vyper_to_abi_type tenv (TupleT (MAP (lowered_value_type ce) args))) av
    source_base source_cap dest_base s_tup /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  evaluate_type tenv (TupleT (MAP (lowered_value_type ce) args)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi tenv (TupleT (MAP (lowered_value_type ce) args)) v = SOME av /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) < 2 ** 64 /\
  compile_create_blueprint_check target offset ca = (Var code_name,cb) /\
  compile_alloc_buffer capacity cb = (buf,c1) /\
  compile_create_ctor_tuple cfn ce args c1 = (src,c2) /\
  (!ce' ty e st. ci_mono st (SND (cfn ce' ty e st))) /\
  lookup_var code_name s_tup = SOME captured ==>
  ?s2.
    window_strong_result ctx func c2 sa args_len
      (vyper_to_abi_type tenv (TupleT (MAP (lowered_value_type ce) args))) av
      dest_base s_tup s2 /\
    eval_operand (Var code_name) s2 = SOME captured /\
    eval_operand args_len s2 =
      SOME (n2w (LENGTH (enc (vyper_to_abi_type tenv
        (TupleT (MAP (lowered_value_type ce) args))) av))) /\
    w2n (n2w (LENGTH (enc (vyper_to_abi_type tenv
      (TupleT (MAP (lowered_value_type ce) args))) av)) : bytes32) < 2 ** 64
Proof
  strip_tac >> drule_all create_blueprint_encoded_check_operand >> strip_tac >>
  drule_all create_ctor_encoding_bound >> strip_tac >>
  drule_all abi_props_vyper_typed >> strip_tac >>
  `LENGTH (enc (vyper_to_abi_type tenv
     (TupleT (MAP (lowered_value_type ce) args))) av) < 2 ** 64` by
    metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS] >>
  `LENGTH (enc (vyper_to_abi_type tenv
     (TupleT (MAP (lowered_value_type ce) args))) av) < dimword (:256)` by
    (fs[dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  drule_all compile_abi_encode_to_buf_window_strong_run >>
  disch_then (qx_choose_then `s2` assume_tac) >>
  drule window_strong_result_public >> strip_tac >>
  drule abi_encoder_window_result_output >> strip_tac >>
  drule_all abi_encoder_window_result_vars >> strip_tac >>
  qexists_tac `s2` >>
  asm_simp_tac bool_ss [eval_operand_def, w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem window_strong_result_enc_cong[local]:
  enc at av = enc bt bv /\
  window_strong_result ctx func st st' out at av d s t ==>
  window_strong_result ctx func st st' out bt bv d s t
Proof
  strip_tac >> gvs[window_strong_result_def, abi_encoder_window_result_def] >>
  metis_tac[]
QED

(* Equal representative bytes retain the canonical encoder result. *)
Theorem create_blueprint_encoded_args_representative_prefix:
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
    c2 = (args_len,sa) /\
  abi_encoder_window_pre ctx func c2 sa dst src
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
    ct rv source_base source_cap dest_base s_tup /\
  enc ct rv = enc (vyper_to_abi_type tenv
    (TupleT (MAP (lowered_value_type ce) args))) av /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  evaluate_type tenv (TupleT (MAP (lowered_value_type ce) args)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi tenv (TupleT (MAP (lowered_value_type ce) args)) v = SOME av /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) < 2 ** 64 /\
  compile_create_blueprint_check target offset ca = (Var code_name,cb) /\
  compile_alloc_buffer capacity cb = (buf,c1) /\
  compile_create_ctor_tuple cfn ce args c1 = (src,c2) /\
  (!ce' ty e st. ci_mono st (SND (cfn ce' ty e st))) /\
  lookup_var code_name s_tup = SOME captured ==>
  ?s2.
    window_strong_result ctx func c2 sa args_len
      (vyper_to_abi_type tenv (TupleT (MAP (lowered_value_type ce) args))) av
      dest_base s_tup s2 /\
    eval_operand (Var code_name) s2 = SOME captured /\
    eval_operand args_len s2 =
      SOME (n2w (LENGTH (enc (vyper_to_abi_type tenv
        (TupleT (MAP (lowered_value_type ce) args))) av))) /\
    w2n (n2w (LENGTH (enc (vyper_to_abi_type tenv
      (TupleT (MAP (lowered_value_type ce) args))) av)) : bytes32) < 2 ** 64
Proof
  strip_tac >> drule_all create_blueprint_encoded_check_operand >> strip_tac >>
  drule_all create_ctor_encoding_bound >> strip_tac >>
  drule_all abi_props_vyper_typed >> strip_tac >>
  `LENGTH (enc (vyper_to_abi_type tenv
     (TupleT (MAP (lowered_value_type ce) args))) av) < 2 ** 64` by
    metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS] >>
  `LENGTH (enc (vyper_to_abi_type tenv
     (TupleT (MAP (lowered_value_type ce) args))) av) < dimword (:256)` by
    (fs[dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  drule_all compile_abi_encode_to_buf_window_strong_run >>
  disch_then (qx_choose_then `s2` assume_tac) >>
  drule_all window_strong_result_enc_cong >> strip_tac >>
  drule window_strong_result_public >> strip_tac >>
  drule abi_encoder_window_result_output >> strip_tac >>
  drule_all abi_encoder_window_result_vars >> strip_tac >>
  qexists_tac `s2` >>
  asm_simp_tac bool_ss [eval_operand_def, w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem create_blueprint_raw_args_prefix:
  compile_create_blueprint_check target offset ca = (code_op,cb) /\
  run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
  lower_value cfn ce (expr_type e) e cb = (raw_ptr,cm) /\
  compile_create_blueprint_args cfn ce T [e] cb = ((args_ptr,args_len),sa) /\
  cb.cs_next_var <= cm.cs_next_var /\
  expr_post H ctx func ce cx e es cb cm s1 es' v raw_ptr sv /\
  expr_type e = BaseT (BytesT (Dynamic maxlen)) /\
  value_has_type (BaseTV (BytesT (Dynamic maxlen))) v /\
  maxlen < 2 ** 64 /\
  run_inst_seq (emitted_insts cm sa) sv = OK s2 ==>
  eval_operand code_op s2 = eval_operand code_op s1 /\
  ?args. eval_operand args_len s2 = SOME args /\ w2n args < 2 ** 64
Proof
  strip_tac >> drule_all create_blueprint_check_prefix >>
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
  qpat_x_assum `compile_create_blueprint_args _ _ _ _ _ = _` mp_tac >>
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
  compile_create_blueprint_check target offset ca = (code_op,cb) /\
  run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
  lower_value cfn ce (expr_type e) e cb = (raw_ptr,cm) /\
  compile_create_blueprint_args cfn ce T [e] cb = ((args_ptr,args_len),sa) /\
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
  compile_create_blueprint_check target offset ca = (code_op,cb) /\
  run_inst_seq (emitted_insts ca cb) s0 = OK s1 /\
  compile_create_blueprint_args cfn ce F [] cb = ((args_ptr,args_len),sa) /\
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
