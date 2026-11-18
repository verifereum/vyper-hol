(* Mutual expression recursion join for constructor opcode exclusion. *)
Theory ctorCallFreeExpr
Ancestors
  list pair vyperAST venomInst loweringShapeDefs loweringShapeProps exprLowering
  exprCallBounds supportedExprTraverse e2eDeployDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeMemory ctorCallFreeABI
  ctorCallFreeOps ctorCallFreeCallbacks ctorCallFreeBodies ctorCallFreeMembership
  loweringCallOpcodes ctorCallFreeExprBody ctorCallFreeBuiltinBody ctorCallFreeTypeBuiltinBody

(* Discharge a precise lemma's opcode facts from the complement-of-seven premise. *)
val base7_tm = ``!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
  opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
  opc <> RETURNDATACOPY ==> (P:opcode -> bool) opc``;
fun b7 th = SIMP_RULE (srw_ss()) [ASSUME base7_tm, DISJ_IMP_THM, FORALL_AND_THM] th;

Theorem opcode_defaults_without[local]:
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) ==>
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd))
      (cenv_without_defaults ce name).ce_func_defaults)
Proof
  simp[cenv_without_defaults_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem opcode_omitted_default_supported[local]:
  EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
               ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults /\
  MEM e (omitted_defaults ce name n) ==>
  ~supported_expr_exists R e /\ ~supported_expr_exists expr_shape_root e
Proof
  rw[omitted_defaults_def] >>
  Cases_on `ALOOKUP ce.ce_func_defaults name` >> gvs[] >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  gvs[EVERY_MEM, supported_exprs_exists_every, EXISTS_MEM] >>
  metis_tac[rich_listTheory.MEM_DROP_IMP, SND]
QED

Theorem outcomes_free_expr_child[local]:
  P INVALID ==>
  (
  (!e ce ty st. expr_size e + cenv_defaults_size ce < bound ==>
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\ ~supported_expr_exists Q e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty e st)))) ==>
  !e ce ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\ ~supported_expr_exists Q e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (expr_child_callback bound cfn ce ty e st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[expr_child_callback_def] >> IF_CASES_TAC >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[invalid_expr_call_def] >> pairarg_tac >> gvs[] >>
  metis_tac[SRULE [] (Q.INST [`opc` |-> `INVALID`] opcode_every_emit_inst), SND]
QED

Theorem outcomes_free_builtin_join[local]:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!e ce ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty e st)))) ==>
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  (precompile_builtin bi ==> P STATICCALL) /\
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
  irule (Q.INST [`root2` |-> `expr_shape_root`] outcomes_free_builtin_dispatch_body) >>
  simp[(b7 outcomes_free_binop), (b7 outcomes_free_compile_builtin_calldatasize),
    (b7 outcomes_free_compile_env_var), (b7 outcomes_free_alloc_buffer), (b7 outcomes_free_compile_slice_out_buf),
    (b7 outcomes_free_compile_blobhash), (b7 outcomes_free_compile_blockhash), (b7 outcomes_free_compile_builtin_abs),
    (b7 outcomes_free_compile_invert), (b7 outcomes_free_compile_neg), (b7 outcomes_free_compile_floor), (b7 outcomes_free_compile_ceil), (b7 outcomes_free_compile_addmod), (b7 outcomes_free_compile_mulmod), (b7 outcomes_free_compile_pow_mod256),
    (b7 outcomes_free_compile_as_wei_value_int), (b7 outcomes_free_compile_as_wei_value_decimal), (b7 outcomes_free_compile_builtin_len), (b7 outcomes_free_compile_keccak256_word), (b7 outcomes_free_compile_keccak256_bytesm), (b7 outcomes_free_compile_keccak256_bytes), (b7 outcomes_free_compile_bytestring_hash),
    (b7 outcomes_free_compile_bytestring_src), (b7 outcomes_free_compile_slice_data), (b7 outcomes_free_compile_slice_calldata), (b7 outcomes_free_compile_slice_code), (b7 outcomes_free_compile_slice_extcode),
    (b7 outcomes_free_compile_uint2str), (b7 outcomes_free_unwrap_value), (b7 outcomes_free_compile_method_id_runtime),
    (b7 outcomes_free_compare), (b7 outcomes_free_ptr_load), (b7 outcomes_free_ensure_memory),
    (b7 outcomes_free_compile_list_membership_in), (b7 outcomes_free_compile_list_membership_notin),
    (b7 outcomes_free_compile_var_array_membership), (b7 outcomes_free_literal_vv), expr_call_root_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> strip_tac >>
    irule (b7 outcomes_free_acc) >> simp[] >>
    ho_match_mp_tac every_state_insts_lower_value >> simp[(b7 outcomes_free_unwrap_value)] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule (b7 outcomes_free_make_tuple) >>
    simp[(b7 outcomes_free_store_memory), (b7 outcomes_free_unwrap_value)] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule (b7 outcomes_free_concat) >>
    simp[(b7 outcomes_free_unwrap_value)] >> rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >> irule (b7 outcomes_free_make_array) >>
    simp[(b7 outcomes_free_store_memory), (b7 outcomes_free_unwrap_value)] >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  conj_tac >- (rpt strip_tac >>
    irule (b7 outcomes_free_multi_exprs) >>
    simp[] >> rpt strip_tac >> first_assum irule >>
    `~supported_expr_exists R (Builtin ann (MakeArray ety bnd) es) /\
     ~supported_expr_exists expr_shape_root (Builtin ann (MakeArray ety bnd) es)` by
      metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
    gvs[supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
    metis_tac[]) >>
  qexists_tac `R` >> simp[] >> metis_tac[]

QED

Theorem outcomes_free_type_join[local]:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!e ce ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty e st)))) ==>
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  type_builtin_arity tb <= LENGTH args /\
  ~supported_exprs_exists R args /\
  ~supported_exprs_exists expr_shape_root args /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args st)))
  )
Proof
  strip_tac >>
  ntac 2 strip_tac >>
  `!e ty st. MEM e args ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[supported_exprs_exists_every, EXISTS_MEM]) >>
  `P MSTORE` by simp[] >>
  irule (UNDISCH outcomes_free_type_builtin_dispatch_body) >>
  simp[(b7 outcomes_free_unwrap_value), (b7 outcomes_free_alloc_buffer), (b7 outcomes_free_type_convert),
    (b7 outcomes_free_bytestring_widen_copy), (b7 outcomes_free_builtin_empty_complex), (b7 outcomes_free_compile_bytestring_src),
    (b7 outcomes_free_extract32_load), (b7 outcomes_free_clamp_basetype), (b7 outcomes_free_lower_abi_encode),
    (b7 outcomes_free_lower_abi_decode), (b7 outcomes_free_store_abi_tuple), outcomes_free_materialize_vv, (b7 outcomes_free_store_memory),
    (b7 outcomes_free_abi_encode_args)] >>
  qexists_tac `R` >> simp[] >> metis_tac[]
QED

val snapshot7 = SIMP_RULE (srw_ss())
  [b7 outcomes_free_unwrap_value, b7 outcomes_free_alloc_buffer,
   b7 outcomes_free_store_memory] outcomes_free_snapshot;

Theorem outcomes_free_expr_join[local]:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P CALL /\ P STATICCALL /\ P DELEGATECALL /\ P INVOKE /\ P RETURNDATACOPY) ==>
  (
  (!child ce ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R child /\
    ~supported_expr_exists expr_shape_root child /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn ce ty child st)))) /\
  (!ann bi args st. e = Builtin ann bi args ==>
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    builtin_arity bi <= LENGTH args /\ ~R (Builtin ann bi args) /\
    ~supported_exprs_exists R args /\ ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (bfn ce ann ty bi args st)))) /\
  (!ann tb rty args st. e = TypeBuiltin ann tb rty args ==>
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists R args /\ ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (tfn ce ann ty tb rty args st)))) ==>
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_expr_exists R e /\ ~supported_expr_exists expr_shape_root e /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_expr_body cfn bfn tfn ce ty e st)))
  )
Proof
  strip_tac >> strip_tac >>
  ntac 2 strip_tac >>
  `!child ty st. ~supported_expr_exists R child /\
    ~supported_expr_exists expr_shape_root child /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty child st)))` by
    metis_tac[] >>
  irule (Q.INST [`root2` |-> `expr_shape_root`] outcomes_free_expr_body) >>
  simp[(b7 outcomes_free_literal_vv), (b7 outcomes_free_name_vv), (b7 outcomes_free_unwrap_value),
    (b7 outcomes_free_alloc_buffer), (b7 outcomes_free_ifexp_arm), (b7 outcomes_free_dynarray_pop),
    every_state_insts_addmod_names, every_state_insts_mulmod_names,
    every_state_insts_powmod256_names, (b7 outcomes_free_compile_addmod), (b7 outcomes_free_compile_mulmod), (b7 outcomes_free_compile_pow_mod256)] >>
  rpt conj_tac >>
  all_tac >~ [`compile_get_target_ptr _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule (Q.INST [`R` |-> `R`, `root2` |-> `expr_shape_root`]
      every_state_insts_get_target_ptr) >>
    gvs[supported_expr_exists_def, (b7 outcomes_free_keccak256_key),
      (b7 outcomes_free_mapping_subscript), (b7 outcomes_free_alloc_buffer), opcode_every_emit_op,
      (b7 outcomes_free_array_subscript), (b7 outcomes_free_ptr_load)] >>
    qexists_tac `R` >> simp[] >>
    rpt gen_tac >> strip_tac >>
    simp[every_state_insts_lower_value, (b7 outcomes_free_unwrap_value)]) >>
  all_tac >~ [`Builtin _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
    gvs[supported_expr_exists_def, expr_shape_root_def] >> rpt strip_tac >>
    first_assum irule >> simp[] >> metis_tac[]) >>
  all_tac >~ [`compile_subscript _ _ _ _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule every_state_insts_subscript >>
    gvs[supported_expr_exists_def, (b7 outcomes_free_keccak256_key), snapshot7, (b7 outcomes_free_store_memory),
      (b7 outcomes_free_mapping_subscript), (b7 outcomes_free_alloc_buffer),
      (b7 outcomes_free_tuple_subscript), (b7 outcomes_free_array_subscript), (b7 outcomes_free_ptr_load)] >>
    simp[every_state_insts_lower_value, (b7 outcomes_free_unwrap_value)]) >>
  all_tac >~ [`compile_attribute _ _ _ _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule (b7 outcomes_free_attribute) >> gvs[supported_expr_exists_def]) >>
  all_tac >~ [`compile_struct_lit _ _ _ _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
    irule (b7 outcomes_free_struct_lit) >> simp[(b7 outcomes_free_store_memory), (b7 outcomes_free_unwrap_value)] >>
    rpt strip_tac >> gvs[supported_expr_exists_def,
      supported_fields_exists_every, EXISTS_MEM] >>
    first_assum irule >> metis_tac[SND]) >>
  all_tac >~ [`TypeBuiltin _ _ _ _ (* sg *)`] >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
    gvs[supported_expr_exists_def, expr_shape_root_def] >>
    rpt strip_tac >> first_assum irule >> simp[] >> metis_tac[]) >>
  all_tac >~ [`compile_call _ _ _ _ _ _ _ _ (* sg *)`] >- (map_every qx_gen_tac [`ann`, `target`, `args`, `d`, `call_st`] >>
    disch_then SUBST_ALL_TAC >> qid_spec_tac `call_st` >>
    `P CALL /\ P STATICCALL /\ P DELEGATECALL /\ P INVOKE /\ P RETURNDATACOPY` by
      metis_tac[supported_expr_exists_root] >>
    `!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
           opc <> CREATE /\ opc <> CREATE2 ==> P opc` by
      (rpt strip_tac >> Cases_on `opc = CALL` >> gvs[] >>
       Cases_on `opc = STATICCALL` >> gvs[] >> Cases_on `opc = DELEGATECALL` >> gvs[]) >>
    `~expr_shape_root (Call ann target args d)` by
      metis_tac[supported_expr_exists_root] >>
    ho_match_mp_tac opcode_every_call >> simp[] >> conj_tac
    >- (rpt strip_tac >> first_assum irule >> simp[] >>
        conj_tac >- metis_tac[opcode_defaults_without] >>
        `~R (Call ann (IntCall id) args d)` by
          metis_tac[supported_expr_exists_root] >>
        metis_tac[opcode_omitted_default_supported]) >>
    rpt strip_tac >> first_assum irule >>
    metis_tac[call_callback_child_supported]) >>
  qexists_tac `R` >> simp[] >> metis_tac[]
QED

Theorem outcomes_free_compile_expr_mutual[local]:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P CALL /\ P STATICCALL /\ P DELEGATECALL /\ P INVOKE /\ P RETURNDATACOPY) ==>
  (!ann bi args. ~R (Builtin ann bi args) /\ precompile_builtin bi ==>
    P STATICCALL) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) /\
  (!ce rt ty bi args st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    builtin_arity bi <= LENGTH args /\
    ~R (Builtin rt bi args) /\
    ~supported_exprs_exists R args /\
    ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_builtin_dispatch ce rt ty bi args st)))) /\
  (!ce vt ty tb rt args st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd)) ce.ce_func_defaults) /\
    type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists R args /\
    ~supported_exprs_exists expr_shape_root args /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_type_builtin_dispatch ce vt ty tb rt args st))))
  )
Proof
  ntac 3 strip_tac >>
  `P INVALID` by simp[] >>
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (strip_tac >> drule (UNDISCH outcomes_free_expr_child) >> strip_tac >>
      simp[Once compile_expr_raw_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule (UNDISCH (UNDISCH outcomes_free_expr_join)) >>
      fs[Excl "expr_child_callback_def"] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
        first_assum irule >> simp[expr_size_def] >> metis_tac[]) >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> disch_then SUBST_ALL_TAC >> strip_tac >>
      first_assum irule >> simp[expr_size_def] >> metis_tac[])
  >- (strip_tac >> drule (UNDISCH outcomes_free_expr_child) >> strip_tac >>
   simp[Once compile_expr_raw_def] >>
   CONV_TAC (DEPTH_CONV ETA_CONV) >>
   irule (UNDISCH outcomes_free_builtin_join) >>
   fs[Excl "expr_child_callback_def"] >> metis_tac[])
  >> rule_assum_tac (REWRITE_RULE []) >> strip_tac >>
  drule (UNDISCH outcomes_free_expr_child) >> strip_tac >>
  simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule (UNDISCH outcomes_free_type_join) >>
  fs[Excl "expr_child_callback_def"] >> metis_tac[]
QED

Theorem outcomes_free_compile_expr:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P CALL /\ P STATICCALL /\ P DELEGATECALL /\ P INVOKE /\ P RETURNDATACOPY) ==>
  (!ann bi args. ~R (Builtin ann bi args) /\ precompile_builtin bi ==>
    P STATICCALL) ==>
  (
  !e cenv ret_ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd))
        cenv.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr cenv ret_ty e st)))
  )
Proof
  ntac 3 strip_tac >>
  metis_tac[(UNDISCH_ALL outcomes_free_compile_expr_mutual)]
QED

Theorem outcomes_free_compile_get_target_ptr:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P CALL /\ P STATICCALL /\ P DELEGATECALL /\ P INVOKE /\ P RETURNDATACOPY) ==>
  (!ann bi args. ~R (Builtin ann bi args) /\ precompile_builtin bi ==>
    P STATICCALL) ==>
  (
  !target cenv st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd))
        cenv.ce_func_defaults) /\
    ~supported_target_exists R target /\
    ~supported_target_exists expr_shape_root target /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_get_target_ptr compile_expr cenv target st)))
  )
Proof
  ntac 3 strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule (Q.INST [`R` |-> `R`, `root2` |-> `expr_shape_root`]
    every_state_insts_get_target_ptr) >>
  simp[(b7 outcomes_free_keccak256_key), (b7 outcomes_free_mapping_subscript), (b7 outcomes_free_alloc_buffer),
    opcode_every_emit_op, (b7 outcomes_free_array_subscript), (b7 outcomes_free_ptr_load)] >>
  qexists_tac `R` >> simp[] >>
  map_every qx_gen_tac [`child`, `child_ty`, `child_st`] >> strip_tac >>
  qid_spec_tac `child_st` >> ho_match_mp_tac every_state_insts_lower_value >>
  simp[b7 outcomes_free_unwrap_value] >> rpt strip_tac >>
  irule (UNDISCH_ALL outcomes_free_compile_expr) >> metis_tac[]
QED

Theorem compile_expr_opcode_every:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ann target args d. ~R (Call ann target args d) ==>
    P INVOKE /\ P RETURNDATACOPY) ==>
  (
  !e cenv ret_ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd))
        cenv.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists expr_shape_root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr cenv ret_ty e st)))
  )
Proof
  ntac 2 strip_tac >>
  `!ann target args d. ~R (Call ann target args d) ==>
    P CALL /\ P STATICCALL /\ P DELEGATECALL /\ P INVOKE /\ P RETURNDATACOPY` by
    (rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  `!ann bi args. ~R (Builtin ann bi args) /\ precompile_builtin bi ==>
    P STATICCALL` by simp[] >>
  `!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc` by simp[] >>
  rpt strip_tac >> irule (UNDISCH_ALL outcomes_free_compile_expr) >> simp[] >> first_assum ACCEPT_TAC
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
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd))
        cenv.ce_func_defaults) /\
    ~supported_target_exists R target /\
    ~supported_target_exists expr_shape_root target /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_get_target_ptr compile_expr cenv target st)))
  )
Proof
  ntac 2 strip_tac >>
  `!ann target args d. ~R (Call ann target args d) ==>
    P CALL /\ P STATICCALL /\ P DELEGATECALL /\ P INVOKE /\ P RETURNDATACOPY` by
    (rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  `!ann bi args. ~R (Builtin ann bi args) /\ precompile_builtin bi ==>
    P STATICCALL` by simp[] >>
  `!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc` by simp[] >>
  rpt strip_tac >> irule (UNDISCH_ALL outcomes_free_compile_get_target_ptr) >> simp[] >> first_assum ACCEPT_TAC
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
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd))
        cenv.ce_func_defaults) /\
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
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists expr_shape_root (SND nd))
        cenv.ce_func_defaults) /\
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
