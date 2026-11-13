(* Mutual expression recursion join for constructor opcode exclusion. *)
Theory ctorCallFreeExpr
Ancestors
  list pair vyperAST venomInst loweringShapeDefs loweringShapeProps exprLowering
  exprCallBounds supportedExprTraverse e2eDeployDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeMemory ctorCallFreeABI
  ctorCallFreeOps ctorCallFreeCallbacks ctorCallFreeBodies ctorCallFreeMembership
  ctorCallFreeExprBody ctorCallFreeBuiltinBody ctorCallFreeTypeBuiltinBody

Theorem call_free_expr_child[local]:
  (!e ce ty st. expr_size e < bound ==>
    ~supported_expr_exists R e /\ ~supported_expr_exists Q e /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn ce ty e st)))) ==>
  !e ce ty st. ~supported_expr_exists R e /\ ~supported_expr_exists Q e /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (expr_child_callback bound cfn ce ty e st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[expr_child_callback_def] >> IF_CASES_TAC >- (first_x_assum irule >> simp[]) >>
  simp[invalid_expr_call_def] >> pairarg_tac >> gvs[] >>
  metis_tac[SRULE [] (Q.INST [`opc` |-> `INVALID`] call_free_emit_inst), SND]
QED

Theorem call_free_builtin_join[local]:
  (!e ce ty st. ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn ce ty e st)))) ==>
  builtin_arity bi <= LENGTH args /\ ~constructor_call_root (Builtin rt bi args) /\
  ~supported_exprs_exists constructor_call_root args /\
  ~supported_exprs_exists expr_shape_root args /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_builtin_dispatch_body cfn ce rt ty bi args st)))
Proof
  ntac 2 strip_tac >>
  irule (Q.INST [`root2` |-> `expr_shape_root`] call_free_builtin_dispatch_body) >>
  simp[call_free_binop, call_free_calldatasize,
    call_free_env_var, call_free_alloc_buffer, call_free_slice_out_buf,
    call_free_blobhash, call_free_blockhash, call_free_builtin_abs,
    call_free_invert, call_free_neg, call_free_rounding, call_free_modular,
    call_free_as_wei_value, call_free_builtin_len, call_free_keccak,
    call_free_bytestring_src, call_free_slice_data, call_free_slice_adhoc,
    call_free_uint2str, call_free_unwrap_value, call_free_method_id_runtime,
    call_free_compare, call_free_ptr_load, call_free_ensure_in_memory,
    call_free_list_membership_in, call_free_list_membership_notin,
    call_free_var_array_membership, call_free_literal_vv, constructor_call_root_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> strip_tac >>
    irule call_free_acc >> simp[] >>
    ho_match_mp_tac every_state_insts_lower_value >> simp[call_free_unwrap_value] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule call_free_make_tuple >>
    simp[call_free_store_memory, call_free_unwrap_value] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule call_free_concat >>
    simp[call_free_unwrap_value] >> rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule call_free_make_array >>
    simp[call_free_store_memory, call_free_unwrap_value] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  reverse conj_tac >- gvs[constructor_call_root_def] >>
  rpt strip_tac >> irule call_free_multi_exprs >> simp[call_free_unwrap_value] >>
  rpt strip_tac >> first_assum irule >>
  `~supported_expr_exists constructor_call_root (Builtin ann (MakeArray ety bnd) es) /\
   ~supported_expr_exists expr_shape_root (Builtin ann (MakeArray ety bnd) es)` by
    metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
  gvs[supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]
QED

Theorem call_free_type_join[local]:
  (!e ce ty st. ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn ce ty e st)))) ==>
  type_builtin_arity tb <= LENGTH args /\
  ~supported_exprs_exists constructor_call_root args /\
  ~supported_exprs_exists expr_shape_root args /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args st)))
Proof
  ntac 2 strip_tac >> irule call_free_type_builtin_dispatch_body >>
  simp[call_free_unwrap_value, call_free_alloc_buffer, call_free_type_convert,
    call_free_bytestring_widen_copy, call_free_empty_complex, call_free_bytestring_src,
    call_free_extract32_load, call_free_clamp_basetype, call_free_lower_abi_encode,
    call_free_lower_abi_decode, call_free_store_abi_tuple, call_free_materialize_vv]
QED

Theorem call_free_expr_join[local]:
  (!child ce ty st. ~supported_expr_exists constructor_call_root child /\
    ~supported_expr_exists expr_shape_root child /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn ce ty child st)))) /\
  (!ann bi args st. e = Builtin ann bi args ==>
    builtin_arity bi <= LENGTH args /\ ~constructor_call_root (Builtin ann bi args) /\
    ~supported_exprs_exists constructor_call_root args /\ ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (bfn ce ann ty bi args st)))) /\
  (!ann tb rty args st. e = TypeBuiltin ann tb rty args ==>
    type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists constructor_call_root args /\ ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (tfn ce ann ty tb rty args st)))) ==>
  ~supported_expr_exists constructor_call_root e /\ ~supported_expr_exists expr_shape_root e /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_expr_body cfn bfn tfn ce ty e st)))
Proof
  ntac 2 strip_tac >>
  irule (Q.INST [`root2` |-> `expr_shape_root`] call_free_expr_body) >>
  simp[call_free_literal_vv, call_free_name_vv, call_free_unwrap_value,
    call_free_alloc_buffer, call_free_ifexp_arm, call_free_dynarray_pop,
    every_state_insts_addmod_names, every_state_insts_mulmod_names,
    every_state_insts_powmod256_names, call_free_modular] >>
  conj_tac >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule (Q.INST [`R` |-> `constructor_call_root`, `root2` |-> `expr_shape_root`]
      every_state_insts_get_target_ptr) >>
    gvs[supported_expr_exists_def, call_free_keccak256_key,
      call_free_mapping_subscript, call_free_alloc_buffer, call_free_emit_op,
      call_free_array_subscript, call_free_ptr_load] >>
    rpt gen_tac >> strip_tac >>
    simp[every_state_insts_lower_value, call_free_unwrap_value]) >>
  conj_tac >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
    gvs[supported_expr_exists_def, expr_shape_root_def] >> rpt strip_tac >>
    first_assum irule >> simp[]) >>
  conj_tac >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule every_state_insts_subscript >>
    gvs[supported_expr_exists_def, call_free_keccak256_key,
      call_free_mapping_subscript, call_free_alloc_buffer,
      call_free_tuple_subscript, call_free_array_subscript, call_free_ptr_load] >>
    simp[every_state_insts_lower_value, call_free_unwrap_value]) >>
  conj_tac >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule call_free_attribute >> gvs[supported_expr_exists_def]) >>
  conj_tac >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule call_free_struct_lit >> simp[call_free_store_memory, call_free_unwrap_value] >>
    rpt strip_tac >> gvs[supported_expr_exists_def,
      supported_fields_exists_every, EXISTS_MEM] >>
    first_assum irule >> metis_tac[SND]) >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  gvs[supported_expr_exists_def, expr_shape_root_def] >>
  rpt strip_tac >> first_assum irule >> simp[]
QED

Theorem compile_expr_call_free_mutual[local]:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) /\
  (!ce rt ty bi args st.
    builtin_arity bi <= LENGTH args /\
    ~constructor_call_root (Builtin rt bi args) /\
    ~supported_exprs_exists constructor_call_root args /\
    ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_builtin_dispatch ce rt ty bi args st)))) /\
  (!ce vt ty tb rt args st.
    type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists constructor_call_root args /\
    ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_type_builtin_dispatch ce vt ty tb rt args st))))
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (strip_tac >> drule call_free_expr_child >> strip_tac >>
      simp[Once compile_expr_raw_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule call_free_expr_join >> simp[Excl "expr_child_callback_def"])
  >- (strip_tac >> drule call_free_expr_child >> strip_tac >>
   simp[Once compile_expr_raw_def] >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >>
   irule call_free_builtin_join >> simp[Excl "expr_child_callback_def"])
  >> gvs[] >> strip_tac >> drule call_free_expr_child >> strip_tac >>
  simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule call_free_type_join >> simp[Excl "expr_child_callback_def"]
QED

Theorem compile_expr_call_free:
  !e cenv ret_ty st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr cenv ret_ty e st)))
Proof
  metis_tac[compile_expr_call_free_mutual]
QED

Theorem compile_get_target_ptr_call_free:
  !target cenv st.
    ~supported_target_exists constructor_call_root target /\
    ~supported_target_exists expr_shape_root target /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_get_target_ptr compile_expr cenv target st)))
Proof
  rpt gen_tac >> strip_tac >>
  irule (Q.INST [`R` |-> `constructor_call_root`, `root2` |-> `expr_shape_root`]
    every_state_insts_get_target_ptr) >>
  simp[call_free_keccak256_key, call_free_mapping_subscript, call_free_alloc_buffer,
    call_free_emit_op, call_free_array_subscript, call_free_ptr_load] >>
  rpt gen_tac >> strip_tac >>
  simp[every_state_insts_lower_value, compile_expr_call_free, call_free_unwrap_value]
QED

Theorem compile_multi_exprs_call_free:
  !es cenv st.
    ~supported_exprs_exists constructor_call_root es /\
    ~supported_exprs_exists expr_shape_root es /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_multi_exprs compile_expr cenv es st)))
Proof
  rpt gen_tac >> strip_tac >> irule call_free_multi_exprs >>
  simp[call_free_unwrap_value] >> rpt strip_tac >> irule compile_expr_call_free >>
  metis_tac[supported_exprs_exists_every, EXISTS_MEM]
QED

Theorem compile_struct_lit_call_free:
  !fields cenv ty buf off st.
    ~supported_fields_exists constructor_call_root fields /\
    ~supported_fields_exists expr_shape_root fields /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_struct_lit compile_expr cenv ty fields buf off st)))
Proof
  rpt gen_tac >> strip_tac >> irule call_free_struct_lit >>
  simp[call_free_store_memory, call_free_unwrap_value] >>
  rpt strip_tac >> irule compile_expr_call_free >>
  gvs[supported_fields_exists_every, EXISTS_MEM] >> metis_tac[SND]
QED
