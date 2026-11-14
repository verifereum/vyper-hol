(* Mutual expression recursion join for constructor opcode exclusion. *)
Theory ctorCallFreeExpr
Ancestors
  list pair vyperAST venomInst loweringShapeDefs loweringShapeProps exprLowering
  exprCallBounds supportedExprTraverse e2eDeployDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeMemory ctorCallFreeABI
  ctorCallFreeOps ctorCallFreeCallbacks ctorCallFreeBodies ctorCallFreeMembership
  loweringCallOpcodes ctorCallFreeExprBody ctorCallFreeBuiltinBody ctorCallFreeTypeBuiltinBody

Theorem opcode_every_expr_child[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!e ce ty st. expr_size e < bound ==>
    ~supported_expr_exists R e /\ ~supported_expr_exists Q e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty e st)))) ==>
  !e ce ty st. ~supported_expr_exists R e /\ ~supported_expr_exists Q e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (expr_child_callback bound cfn ce ty e st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[expr_child_callback_def] >> IF_CASES_TAC >- (first_x_assum irule >> simp[]) >>
  simp[invalid_expr_call_def] >> pairarg_tac >> gvs[] >>
  `P INVALID` by simp[] >>
  metis_tac[SRULE [] (Q.INST [`opc` |-> `INVALID`] opcode_every_emit_inst), SND]
QED

Theorem opcode_every_builtin_join[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!e ce ty st. ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty e st)))) ==>
  builtin_arity bi <= LENGTH args /\
  ~supported_exprs_exists R args /\
  ~supported_exprs_exists expr_shape_root args /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_builtin_dispatch_body cfn ce rt ty bi args st)))
  )
Proof
  strip_tac >>
  ntac 2 strip_tac >>
  irule (Q.INST [`root2` |-> `expr_shape_root`] (UNDISCH opcode_every_builtin_dispatch_body)) >>
  simp[(UNDISCH opcode_every_binop), (UNDISCH opcode_every_calldatasize),
    (UNDISCH opcode_every_env_var), (UNDISCH opcode_every_alloc_buffer), (UNDISCH opcode_every_slice_out_buf),
    (UNDISCH opcode_every_blobhash), (UNDISCH opcode_every_blockhash), (UNDISCH opcode_every_builtin_abs),
    (UNDISCH opcode_every_invert), (UNDISCH opcode_every_neg), (UNDISCH opcode_every_rounding), (UNDISCH opcode_every_modular),
    (UNDISCH opcode_every_as_wei_value), (UNDISCH opcode_every_builtin_len), (UNDISCH opcode_every_keccak),
    (UNDISCH opcode_every_bytestring_src), (UNDISCH opcode_every_slice_data), (UNDISCH opcode_every_slice_adhoc),
    (UNDISCH opcode_every_uint2str), (UNDISCH opcode_every_unwrap_value), (UNDISCH opcode_every_method_id_runtime),
    (UNDISCH opcode_every_compare), (UNDISCH opcode_every_ptr_load), (UNDISCH opcode_every_ensure_in_memory),
    (UNDISCH opcode_every_list_membership_in), (UNDISCH opcode_every_list_membership_notin),
    (UNDISCH opcode_every_var_array_membership), (UNDISCH opcode_every_literal_vv), expr_call_root_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> strip_tac >>
    irule (UNDISCH opcode_every_acc) >> simp[] >>
    ho_match_mp_tac every_state_insts_lower_value >> simp[(UNDISCH opcode_every_unwrap_value)] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule (UNDISCH opcode_every_make_tuple) >>
    simp[(UNDISCH opcode_every_store_memory), (UNDISCH opcode_every_unwrap_value)] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule (UNDISCH opcode_every_concat) >>
    simp[(UNDISCH opcode_every_unwrap_value)] >> rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule (UNDISCH opcode_every_make_array) >>
    simp[(UNDISCH opcode_every_store_memory), (UNDISCH opcode_every_unwrap_value)] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >>
    irule (Q.SPECL [`es`, `cfn`, `ce`]
      (MATCH_MP (UNDISCH opcode_every_multi_exprs)
        (Q.GENL [`ce`, `vv`, `st`] (UNDISCH opcode_every_unwrap_value)))) >>
    simp[] >> rpt strip_tac >> first_assum irule >>
    `~supported_expr_exists R (Builtin ann (MakeArray ety bnd) es) /\
     ~supported_expr_exists expr_shape_root (Builtin ann (MakeArray ety bnd) es)` by
      metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
    gvs[supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
    metis_tac[]) >>
  qexists_tac `R` >> simp[]

QED

Theorem opcode_every_type_join[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!e ce ty st. ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty e st)))) ==>
  type_builtin_arity tb <= LENGTH args /\
  ~supported_exprs_exists R args /\
  ~supported_exprs_exists expr_shape_root args /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args st)))
  )
Proof
  strip_tac >>
  ntac 2 strip_tac >> irule (UNDISCH opcode_every_type_builtin_dispatch_body) >>
  simp[(UNDISCH opcode_every_unwrap_value), (UNDISCH opcode_every_alloc_buffer), (UNDISCH opcode_every_type_convert),
    (UNDISCH opcode_every_bytestring_widen_copy), (UNDISCH opcode_every_empty_complex), (UNDISCH opcode_every_bytestring_src),
    (UNDISCH opcode_every_extract32_load), (UNDISCH opcode_every_clamp_basetype), (UNDISCH opcode_every_lower_abi_encode),
    (UNDISCH opcode_every_lower_abi_decode), (UNDISCH opcode_every_store_abi_tuple), (UNDISCH opcode_every_materialize_vv)] >>
  qexists_tac `R` >> simp[]
QED

Theorem opcode_every_expr_join[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P INVOKE /\ P RETURNDATACOPY) ==>
  (
  (!child ce ty st. ~supported_expr_exists R child /\
    ~supported_expr_exists expr_shape_root child /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty child st)))) /\
  (!ann bi args st. e = Builtin ann bi args ==>
    builtin_arity bi <= LENGTH args /\ ~R (Builtin ann bi args) /\
    ~supported_exprs_exists R args /\ ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (bfn ce ann ty bi args st)))) /\
  (!ann tb rty args st. e = TypeBuiltin ann tb rty args ==>
    type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists R args /\ ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (tfn ce ann ty tb rty args st)))) ==>
  ~supported_expr_exists R e /\ ~supported_expr_exists expr_shape_root e /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_expr_body cfn bfn tfn ce ty e st)))
  )
Proof
  strip_tac >> strip_tac >>
  ntac 2 strip_tac >>
  irule (Q.INST [`root2` |-> `expr_shape_root`] (UNDISCH opcode_every_expr_body)) >>
  simp[(UNDISCH opcode_every_literal_vv), (UNDISCH opcode_every_name_vv), (UNDISCH opcode_every_unwrap_value),
    (UNDISCH opcode_every_alloc_buffer), (UNDISCH opcode_every_ifexp_arm), (UNDISCH opcode_every_dynarray_pop),
    every_state_insts_addmod_names, every_state_insts_mulmod_names,
    every_state_insts_powmod256_names, (UNDISCH opcode_every_modular)] >>
  rpt conj_tac >>
  all_tac >~ [`compile_get_target_ptr _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule (Q.INST [`R` |-> `R`, `root2` |-> `expr_shape_root`]
      every_state_insts_get_target_ptr) >>
    gvs[supported_expr_exists_def, (UNDISCH opcode_every_keccak256_key),
      (UNDISCH opcode_every_mapping_subscript), (UNDISCH opcode_every_alloc_buffer), opcode_every_emit_op,
      (UNDISCH opcode_every_array_subscript), (UNDISCH opcode_every_ptr_load)] >>
    qexists_tac `R` >> simp[] >>
    rpt gen_tac >> strip_tac >>
    simp[every_state_insts_lower_value, (UNDISCH opcode_every_unwrap_value)]) >>
  all_tac >~ [`Builtin _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
    gvs[supported_expr_exists_def, expr_shape_root_def] >> rpt strip_tac >>
    first_assum irule >> simp[]) >>
  all_tac >~ [`compile_subscript _ _ _ _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule every_state_insts_subscript >>
    gvs[supported_expr_exists_def, (UNDISCH opcode_every_keccak256_key), (UNDISCH opcode_every_snapshot_vv),
      (UNDISCH opcode_every_mapping_subscript), (UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_tuple_subscript), (UNDISCH opcode_every_array_subscript), (UNDISCH opcode_every_ptr_load)] >>
    simp[every_state_insts_lower_value, (UNDISCH opcode_every_unwrap_value)]) >>
  all_tac >~ [`compile_attribute _ _ _ _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule (UNDISCH opcode_every_attribute) >> gvs[supported_expr_exists_def]) >>
  all_tac >~ [`compile_struct_lit _ _ _ _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule (UNDISCH opcode_every_struct_lit) >> simp[(UNDISCH opcode_every_store_memory), (UNDISCH opcode_every_unwrap_value)] >>
    rpt strip_tac >> gvs[supported_expr_exists_def,
      supported_fields_exists_every, EXISTS_MEM] >>
    first_assum irule >> metis_tac[SND]) >>
  all_tac >~ [`TypeBuiltin _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
    gvs[supported_expr_exists_def, expr_shape_root_def] >>
    rpt strip_tac >> first_assum irule >> simp[]) >>
  all_tac >~ [`compile_call _ _ _ _ _ _ _ _ (* sg *)`] >- (map_every qx_gen_tac [`ann`, `target`, `args`, `d`, `call_st`] >>
    disch_then SUBST_ALL_TAC >> qid_spec_tac `call_st` >>
    `P INVOKE /\ P RETURNDATACOPY` by metis_tac[supported_expr_exists_root] >>
    `~expr_shape_root (Call ann target args d)` by
      metis_tac[supported_expr_exists_root] >>
    ho_match_mp_tac opcode_every_call >> simp[] >> rpt strip_tac >>
    first_assum irule >> metis_tac[call_callback_child_supported]) >>
  qexists_tac `R` >> simp[]
QED

Theorem compile_expr_opcode_every_mutual[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P INVOKE /\ P RETURNDATACOPY) ==>
  (
  (!ce ty e st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) /\
  (!ce rt ty bi args st.
    builtin_arity bi <= LENGTH args /\
    ~R (Builtin rt bi args) /\
    ~supported_exprs_exists R args /\
    ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_builtin_dispatch ce rt ty bi args st)))) /\
  (!ce vt ty tb rt args st.
    type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists R args /\
    ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_type_builtin_dispatch ce vt ty tb rt args st))))
  )
Proof
  strip_tac >> strip_tac >>
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (strip_tac >> drule (UNDISCH opcode_every_expr_child) >> strip_tac >>
      simp[Once compile_expr_raw_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule (UNDISCH (UNDISCH opcode_every_expr_join)) >> simp[Excl "expr_child_callback_def"])
  >- (strip_tac >> drule (UNDISCH opcode_every_expr_child) >> strip_tac >>
   simp[Once compile_expr_raw_def] >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >>
   qpat_assum `!e ce ty st. _ ==> _ (state_insts (SND (expr_child_callback _ _ ce ty e st)))`
     (fn cb => irule (MATCH_MP (UNDISCH opcode_every_builtin_join) cb)) >> simp[Excl "expr_child_callback_def"])
  >> gvs[] >> strip_tac >> drule (UNDISCH opcode_every_expr_child) >> strip_tac >>
  simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qpat_assum `!e ce ty st. _ ==> _ (state_insts (SND (expr_child_callback _ _ ce ty e st)))`
     (fn cb => irule (MATCH_MP (UNDISCH opcode_every_type_join) cb)) >> simp[Excl "expr_child_callback_def"]
QED

Theorem compile_expr_opcode_every:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P INVOKE /\ P RETURNDATACOPY) ==>
  (
  !e cenv ret_ty st.
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr cenv ret_ty e st)))
  )
Proof
  strip_tac >> strip_tac >>
  metis_tac[(UNDISCH (UNDISCH compile_expr_opcode_every_mutual))]
QED

Theorem compile_expr_call_free:
  !e cenv ret_ty st.
    ~supported_expr_exists expr_call_root e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr cenv ret_ty e st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] compile_expr_opcode_every) >> simp[expr_call_root_def]
QED

Theorem compile_get_target_ptr_opcode_every:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P INVOKE /\ P RETURNDATACOPY) ==>
  (
  !target cenv st.
    ~supported_target_exists R target /\
    ~supported_target_exists expr_shape_root target /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_get_target_ptr compile_expr cenv target st)))
  )
Proof
  strip_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule (Q.INST [`R` |-> `R`, `root2` |-> `expr_shape_root`]
    every_state_insts_get_target_ptr) >>
  simp[(UNDISCH opcode_every_keccak256_key), (UNDISCH opcode_every_mapping_subscript), (UNDISCH opcode_every_alloc_buffer),
    opcode_every_emit_op, (UNDISCH opcode_every_array_subscript), (UNDISCH opcode_every_ptr_load)] >>
  qexists_tac `R` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[every_state_insts_lower_value, (UNDISCH (UNDISCH compile_expr_opcode_every)), (UNDISCH opcode_every_unwrap_value)]
QED

Theorem compile_get_target_ptr_call_free:
  !target cenv st.
    ~supported_target_exists expr_call_root target /\
    ~supported_target_exists expr_shape_root target /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_get_target_ptr compile_expr cenv target st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] compile_get_target_ptr_opcode_every) >> simp[expr_call_root_def]
QED

Theorem compile_multi_exprs_opcode_every:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P INVOKE /\ P RETURNDATACOPY) ==>
  (
  !es cenv st.
    ~supported_exprs_exists R es /\
    ~supported_exprs_exists expr_shape_root es /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_multi_exprs compile_expr cenv es st)))
  )
Proof
  strip_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule (Q.SPECL [`es`, `compile_expr`, `cenv`]
    (MATCH_MP (UNDISCH opcode_every_multi_exprs)
      (Q.GENL [`ce`, `vv`, `st`] (UNDISCH opcode_every_unwrap_value)))) >>
  simp[(UNDISCH opcode_every_unwrap_value)] >> rpt strip_tac >> irule (UNDISCH (UNDISCH compile_expr_opcode_every)) >>
  metis_tac[supported_exprs_exists_every, EXISTS_MEM]
QED

Theorem compile_multi_exprs_call_free:
  !es cenv st.
    ~supported_exprs_exists expr_call_root es /\
    ~supported_exprs_exists expr_shape_root es /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_multi_exprs compile_expr cenv es st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] compile_multi_exprs_opcode_every) >> simp[expr_call_root_def]
QED

Theorem compile_struct_lit_opcode_every:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P INVOKE /\ P RETURNDATACOPY) ==>
  (
  !fields cenv ty buf off st.
    ~supported_fields_exists R fields /\
    ~supported_fields_exists expr_shape_root fields /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_struct_lit compile_expr cenv ty fields buf off st)))
  )
Proof
  strip_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> irule (UNDISCH opcode_every_struct_lit) >>
  simp[(UNDISCH opcode_every_store_memory), (UNDISCH opcode_every_unwrap_value)] >>
  rpt strip_tac >> irule (UNDISCH (UNDISCH compile_expr_opcode_every)) >>
  gvs[supported_fields_exists_every, EXISTS_MEM] >> metis_tac[SND]
QED

Theorem compile_struct_lit_call_free:
  !fields cenv ty buf off st.
    ~supported_fields_exists expr_call_root fields /\
    ~supported_fields_exists expr_shape_root fields /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_struct_lit compile_expr cenv ty fields buf off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`, `R` |-> `expr_call_root`] compile_struct_lit_opcode_every) >> simp[expr_call_root_def]
QED
