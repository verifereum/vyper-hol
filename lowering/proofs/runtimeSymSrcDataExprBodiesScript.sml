Theory runtimeSymSrcDataExprBodies
Ancestors
  runtimeSymSrcDataFrame exprLowering emitHelper compileEnv builtinAbi builtinBytes context exprCallBounds

Theorem runtime_data_frame_type_builtin_dispatch_body:
  (!ty e. runtime_data_frame (lower_value cfn cenv ty e)) /\
  (!ty e. runtime_data_frame (cfn cenv ty e)) /\
  (!n v k. runtime_data_frame (compile_bytestring_widen_copy n v k)) /\
  (!v conv. runtime_data_frame (compile_type_convert v conv)) /\
  (!n z. runtime_data_frame (compile_builtin_empty_complex n z)) /\
  (!v. runtime_data_frame (compile_bytestring_src v)) /\
  (!a b c. runtime_data_frame (compile_extract32_load a b c)) /\
  (!v ty. runtime_data_frame (compile_clamp_basetype v ty)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!v. runtime_data_frame (unwrap_value cenv v)) /\
  (!a:bool. !b c d e. runtime_data_frame (builtinAbi$lower_abi_encode a b c d e)) /\
  (!args. runtime_data_frame (compile_abi_encode_args cfn cenv args)) /\
  (!buf off vs. runtime_data_frame (compile_store_abi_tuple cenv buf off vs)) /\
  (!a b c d e. runtime_data_frame (lower_abi_decode a b c d e)) ==>
  runtime_data_frame (compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty args)
Proof
  simp[runtime_data_frame_def] >> strip_tac >>
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, pairTheory.pair_CASE_def, pairTheory.ELIM_UNCURRY,
       oneline as_stack_val_def, oneline as_ptr_val_def] >>
  rpt gen_tac >> rpt IF_CASES_TAC >>
  simp[pairTheory.pair_CASE_def, pairTheory.ELIM_UNCURRY, oneline as_stack_val_def, oneline as_ptr_val_def,
       emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  Cases_on `ret_ty` >>
  simp[as_stack_val_def, pairTheory.pair_CASE_def, pairTheory.ELIM_UNCURRY]
QED

Theorem runtime_data_frame_expr_child_callback_bounded:
  (!ty e. expr_size e < n ==> runtime_data_frame (f cenv ty e)) ==>
  !ty e. runtime_data_frame (expr_child_callback n f cenv ty e)
Proof
  rw[runtime_data_frame_def, expr_child_callback_def] >>
  IF_CASES_TAC >> simp[REWRITE_RULE [runtime_data_frame_def]
    runtime_data_frame_invalid_expr_call]
QED

Theorem runtime_data_frame_builtin_child_callback_bounded:
  (!rt ty bi args. list_size expr_size args < n ==>
    runtime_data_frame (f cenv rt ty bi args)) ==>
  !rt ty bi args. runtime_data_frame (builtin_child_callback n f cenv rt ty bi args)
Proof
  rw[runtime_data_frame_def, builtin_child_callback_def] >>
  IF_CASES_TAC >> simp[REWRITE_RULE [runtime_data_frame_def]
    runtime_data_frame_invalid_expr_call]
QED

Theorem runtime_data_frame_type_child_callback_bounded:
  (!vt ty tb rt args. list_size expr_size args < n ==>
    runtime_data_frame (f cenv vt ty tb rt args)) ==>
  !vt ty tb rt args. runtime_data_frame (type_child_callback n f cenv vt ty tb rt args)
Proof
  rw[runtime_data_frame_def, type_child_callback_def] >>
  IF_CASES_TAC >> simp[REWRITE_RULE [runtime_data_frame_def]
    runtime_data_frame_invalid_expr_call]
QED

Theorem runtime_expr_body_builtin_fallback[local]:
  ~(bi = AddMod /\ ?a b c d f g. args = [Name a b; Name c d; Name f g]) /\
  ~(bi = MulMod /\ ?a b c d f g. args = [Name a b; Name c d; Name f g]) /\
  ~(bi = PowMod256 /\ ?a b c d. args = [Name a b; Name c d]) ==>
  compile_expr_body cfn bfn tfn cenv ty (Builtin t bi args) st =
    bfn cenv (expr_type (Builtin t bi args)) ty bi args st
Proof
  strip_tac >> Cases_on `args` >- simp[compile_expr_body_def] >>
  rename1 `h::tl` >> Cases_on `h` >> simp[compile_expr_body_def] >>
  Cases_on `tl` >- simp[compile_expr_body_def] >>
  rename1 `h2::tl2` >> Cases_on `h2` >> simp[compile_expr_body_def] >>
  Cases_on `tl2`
  >- (Cases_on `bi` >> gvs[compile_expr_body_def]) >>
  rename1 `h3::tl3` >> Cases_on `h3` >> simp[compile_expr_body_def] >>
  Cases_on `tl3` >> Cases_on `bi` >> gvs[compile_expr_body_def]
QED

Theorem runtime_data_frame_expr_body:
  (!t l. runtime_data_frame (compile_literal_vv t l)) /\
  (!t id. runtime_data_frame (compile_name_vv cenv t id)) /\
  (!t e. runtime_data_frame (lower_value cfn cenv t e)) /\
  (!t e. runtime_data_frame (cfn cenv t e)) /\
  (!t at v. runtime_data_frame (compile_ifexp_arm cenv t at v)) /\
  (!t a b c d f g. runtime_data_frame (compile_addmod_names cenv t a b c d f g)) /\
  (!t a b c d f g. runtime_data_frame (compile_mulmod_names cenv t a b c d f g)) /\
  (!t a b c d. runtime_data_frame (compile_powmod256_names cenv t a b c d)) /\
  (!t ty bi args. runtime_data_frame (bfn cenv t ty bi args)) /\
  (!t ty tb rt args. runtime_data_frame (tfn cenv t ty tb rt args)) /\
  (!t ty a b. runtime_data_frame (compile_subscript cfn cenv t ty a b)) /\
  (!t ty a b. runtime_data_frame (compile_attribute cfn cenv t ty a b)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!t fs buf off. runtime_data_frame (compile_struct_lit cfn cenv t fs buf off)) /\
  (!t (ty:vyperAST$type) target args (dr:expr option). runtime_data_frame (compile_call cfn cenv t ty target args dr)) /\
  (!target. runtime_data_frame (compile_get_target_ptr cfn cenv target)) /\
  (!a b c d f g. runtime_data_frame (compile_dynarray_pop a b c d f g)) ==>
  runtime_data_frame (compile_expr_body cfn bfn tfn cenv ty e)
Proof
  simp[runtime_data_frame_def] >> strip_tac >>
  Cases_on `e`
  >~ [`Builtin t bi args`]
  >- (Cases_on `bi = AddMod /\ ?a b c d f g. args = [Name a b; Name c d; Name f g]`
      >- gvs[compile_expr_body_def] >>
      Cases_on `bi = MulMod /\ ?a b c d f g. args = [Name a b; Name c d; Name f g]`
      >- gvs[compile_expr_body_def] >>
      Cases_on `bi = PowMod256 /\ ?a b c d. args = [Name a b; Name c d]`
      >- gvs[compile_expr_body_def] >>
      drule_all runtime_expr_body_builtin_fallback >> simp[]) >>
  pure_rewrite_tac[compile_expr_body_def] >>
  simp[pairTheory.pair_CASE_def, pairTheory.ELIM_UNCURRY]
  >~ [`FLOOKUP cenv.ce_module_vars p`]
  >- (Cases_on `FLOOKUP cenv.ce_module_vars p`
      >- simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
      rename1 `SOME loc` >> Cases_on `loc` >>
      simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def])
  >~ [`is_word_type (expr_type (IfExp _ _ _ _))`]
  >- (gen_tac >> IF_CASES_TAC >>
      simp[REWRITE_RULE [runtime_data_frame_def] runtime_data_frame_new_block,
           REWRITE_RULE [runtime_data_frame_def] runtime_data_frame_emit_inst,
           REWRITE_RULE [runtime_data_frame_def] runtime_data_frame_fresh_var,
           REWRITE_RULE [runtime_data_frame_def] runtime_data_frame_fresh_label])
QED

Theorem runtime_data_frame_builtin_dispatch_body:
  (!t e. runtime_data_frame (lower_value cfn cenv t e)) /\
  (!t e. runtime_data_frame (cfn cenv t e)) /\
  (!es. runtime_data_frame (compile_multi_exprs cfn cenv es)) /\
  (!a b. runtime_data_frame (compile_list_membership_in a b)) /\
  (!a b. runtime_data_frame (compile_list_membership_notin a b)) /\
  (!a b c d. runtime_data_frame (compile_var_array_membership cenv a b c d)) /\
  (!v. runtime_data_frame (compile_bytestring_hash v)) /\
  (!a b c d e f. runtime_data_frame (compile_binop a b c d e f)) /\
  (!v t. runtime_data_frame (compile_invert v t cenv)) /\
  (!v t. runtime_data_frame (compile_neg v t)) /\
  (!v. runtime_data_frame (compile_builtin_abs v)) /\
  (!i. runtime_data_frame (compile_env_var i)) /\
  (!e i. runtime_data_frame (compile_acc cfn cenv e i)) /\
  (!v. runtime_data_frame (compile_keccak256_bytes v)) /\
  (!v m. runtime_data_frame (compile_keccak256_bytesm v m)) /\
  (!v. runtime_data_frame (compile_keccak256_word v)) /\
  (!v. runtime_data_frame (compile_sha256_bytes v)) /\
  (!v m. runtime_data_frame (compile_sha256_bytesm v m)) /\
  (!v. runtime_data_frame (compile_sha256_word v)) /\
  runtime_data_frame compile_builtin_calldatasize /\
  (!a b c. runtime_data_frame (compile_slice_calldata a b c)) /\
  (!a b c d. runtime_data_frame (compile_builtin_len a b c d)) /\
  (!v. runtime_data_frame (compile_blockhash v)) /\
  (!v. runtime_data_frame (compile_blobhash v)) /\
  (!a b c. runtime_data_frame (compile_addmod a b c)) /\
  (!a b c. runtime_data_frame (compile_mulmod a b c)) /\
  (!a b. runtime_data_frame (compile_ceil a b)) /\
  (!a b. runtime_data_frame (compile_floor a b)) /\
  (!a b. runtime_data_frame (compile_pow_mod256 a b)) /\
  (!a b c d. runtime_data_frame (compile_ecrecover a b c d)) /\
  (!v. runtime_data_frame (unwrap_value cenv v)) /\
  (!a b. runtime_data_frame (compile_ecadd_points a b)) /\
  (!a b. runtime_data_frame (compile_ecmul_point a b)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!a b c d. runtime_data_frame (compile_concat cfn cenv a b c d)) /\
  (!a b c. runtime_data_frame (compile_slice_code a b c)) /\
  (!n. runtime_data_frame (compile_slice_out_buf n)) /\
  (!a b c d e. runtime_data_frame (compile_slice_extcode a b c d e)) /\
  (!v. runtime_data_frame (compile_bytestring_src v)) /\
  (!a b c d e. runtime_data_frame (compile_slice_data a b c d e)) /\
  (!a b c. runtime_data_frame (compile_uint2str a b c)) /\
  (!a b c. runtime_data_frame (compile_as_wei_value_decimal a b c)) /\
  (!a b c. runtime_data_frame (compile_as_wei_value_int a b c)) /\
  (!t l. runtime_data_frame (compile_literal_vv t l)) /\
  (!a b c. runtime_data_frame (compile_method_id_runtime a b c)) /\
  (!a b c. runtime_data_frame (compile_make_tuple cfn cenv a b c)) /\
  (!a b c d e. runtime_data_frame (compile_make_array cfn cenv a b c d e)) ==>
  runtime_data_frame (compile_builtin_dispatch_body cfn cenv ret_ty ty bi args)
Proof
  simp[runtime_data_frame_def] >> strip_tac >> Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, pairTheory.pair_CASE_def,
       pairTheory.ELIM_UNCURRY, oneline as_stack_val_def, oneline as_ptr_val_def] >>
  rpt gen_tac >> rpt IF_CASES_TAC >>
  simp[pairTheory.pair_CASE_def, pairTheory.ELIM_UNCURRY,
       oneline as_stack_val_def, oneline as_ptr_val_def,
       REWRITE_RULE [runtime_data_frame_def] runtime_data_frame_emit_inst,
       REWRITE_RULE [runtime_data_frame_def] runtime_data_frame_emit_op,
       REWRITE_RULE [runtime_data_frame_def] runtime_data_frame_emit_void] >>
  all_tac
  >~ [`compile_keccak256_word`]
  >- (Cases_on `expr_type (HD args)` >> simp[] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[])
  >~ [`compile_sha256_word`]
  >- (Cases_on `expr_type (HD args)` >> simp[] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[])
  >~ [`compile_make_tuple`]
  >- (Cases_on `o'` >> simp[])
  >~ [`compile_var_array_membership`]
  >- (Cases_on `HD (TL args)` >> simp[] >>
      rename1 `Builtin t bb es` >> Cases_on `bb` >> simp[] >>
      IF_CASES_TAC >> simp[])
  >>~- ([`bytestring_literal_hash`],
        Cases_on `bytestring_literal_hash (HD args)` >>
        Cases_on `bytestring_literal_hash (HD (TL args))` >> simp[]) >>
  Cases_on `method_id_literal (HD args)` >> simp[]
QED
