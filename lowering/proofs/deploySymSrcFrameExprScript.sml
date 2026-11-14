Theory deploySymSrcFrameExpr
Ancestors
  deploySymSrcBlockFrame deploySymSrcFrameExprHelpers exprLowering exprCallBounds
  emitHelper compileEnv builtinAbi builtinBytes context

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

Theorem deploy_blocks_frame_type_builtin_dispatch_body:
  (!ty e. deploy_blocks_frame (lower_value cfn cenv ty e)) /\
  (!ty e. deploy_blocks_frame (cfn cenv ty e)) /\
  (!n v k. deploy_blocks_frame (compile_bytestring_widen_copy n v k)) /\
  (!v conv. deploy_blocks_frame (compile_type_convert v conv)) /\
  (!n z. deploy_blocks_frame (compile_builtin_empty_complex n z)) /\
  (!v. deploy_blocks_frame (compile_bytestring_src v)) /\
  (!a b c. deploy_blocks_frame (compile_extract32_load a b c)) /\
  (!v ty. deploy_blocks_frame (compile_clamp_basetype v ty)) /\
  (!v. deploy_blocks_frame (unwrap_value cenv v)) /\
  (!a:bool. !b c d e. deploy_blocks_frame (builtinAbi$lower_abi_encode a b c d e)) /\
  (!args. deploy_blocks_frame (compile_abi_encode_args cfn cenv args)) /\
  (!buf off vs. deploy_blocks_frame (compile_store_abi_tuple cenv buf off vs)) /\
  (!a b c d e. deploy_blocks_frame (lower_abi_decode a b c d e)) ==>
  deploy_blocks_frame (compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty args)
Proof
  strip_tac >> Cases_on `tb` >>
  simp[deploy_blocks_frame_def, compile_type_builtin_dispatch_body_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  simp[deploy_blocks_frame_equation,
       oneline as_stack_val_def, oneline as_ptr_val_def] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation,
       oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()]) >>
  Cases_on `ret_ty` >> gvs[deploy_blocks_frame_equation,
    oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()]
QED

Theorem deploy_blocks_frame_expr_body:
  (!t e. deploy_blocks_frame (lower_value cfn cenv t e)) /\
  (!t e. deploy_blocks_frame (cfn cenv t e)) /\
  (!t at v. deploy_blocks_frame (compile_ifexp_arm cenv t at v)) /\
  (!t a b c d f g. deploy_blocks_frame (compile_addmod_names cenv t a b c d f g)) /\
  (!t a b c d f g. deploy_blocks_frame (compile_mulmod_names cenv t a b c d f g)) /\
  (!t a b c d. deploy_blocks_frame (compile_powmod256_names cenv t a b c d)) /\
  (!t ty bi args. deploy_blocks_frame (bfn cenv t ty bi args)) /\
  (!t ty tb rt args. deploy_blocks_frame (tfn cenv t ty tb rt args)) /\
  (!t ty a b. deploy_blocks_frame (compile_subscript cfn cenv t ty a b)) /\
  (!t ty a b. deploy_blocks_frame (compile_attribute cfn cenv t ty a b)) /\
  (!t fs buf off. deploy_blocks_frame (compile_struct_lit cfn cenv t fs buf off)) /\
  (!t (ty:vyperAST$type) target args (dr:expr option).
    deploy_blocks_frame (compile_call cfn cenv t ty target args dr)) /\
  (!target. deploy_blocks_frame (compile_get_target_ptr cfn cenv target)) /\
  (!a b c d f g. deploy_blocks_frame (compile_dynarray_pop a b c d f g)) ==>
  deploy_blocks_frame (compile_expr_body cfn bfn tfn cenv ty e)
Proof
  strip_tac >> Cases_on `e` >>
  simp[deploy_blocks_frame_def, oneline compile_expr_body_def] >>
  rpt strip_tac >> simp[deploy_blocks_frame_equation] >>
  all_tac
  >~ [`FLOOKUP cenv.ce_module_vars p`]
  >- (Cases_on `FLOOKUP cenv.ce_module_vars p` >> gvs[] >>
      TRY (rename1 `SOME loc` >> Cases_on `loc` >> gvs[]) >>
      rpt (pairarg_tac >> gvs[])) >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation]) >>
  all_tac
  >~ [`is_word_type (expr_type (IfExp _ _ _ _))`]
  >- (IF_CASES_TAC >> gvs[]) >>
  namedCases_on `l` ["", "e1 es1"] >> gvs[deploy_blocks_frame_equation] >>
  Cases_on `e1` >> gvs[deploy_blocks_frame_equation] >>
  namedCases_on `es1` ["", "e2 es2"] >> gvs[deploy_blocks_frame_equation] >>
  Cases_on `e2` >> gvs[deploy_blocks_frame_equation] >>
  namedCases_on `es2` ["", "e3 es3"]
  >- (Cases_on `b` >> gvs[deploy_blocks_frame_equation]) >>
  Cases_on `e3` >> gvs[deploy_blocks_frame_equation] >>
  Cases_on `es3` >> Cases_on `b` >> gvs[deploy_blocks_frame_equation]
QED

Theorem deploy_blocks_frame_builtin_dispatch_body:
  (!t e. deploy_blocks_frame (lower_value cfn cenv t e)) /\
  (!t e. deploy_blocks_frame (cfn cenv t e)) /\
  (!es. deploy_blocks_frame (compile_multi_exprs cfn cenv es)) /\
  (!a b c d. deploy_blocks_frame (compile_var_array_membership cenv a b c d)) /\
  (!a b c d e f. deploy_blocks_frame (compile_binop a b c d e f)) /\
  (!v. deploy_blocks_frame (compile_builtin_abs v)) /\
  (!e i. deploy_blocks_frame (compile_acc cfn cenv e i)) /\
  (!v. deploy_blocks_frame (compile_keccak256_bytes v)) /\
  (!v m. deploy_blocks_frame (compile_keccak256_bytesm v m)) /\
  (!v. deploy_blocks_frame (compile_keccak256_word v)) /\
  (!v. deploy_blocks_frame (compile_sha256_bytes v)) /\
  (!v m. deploy_blocks_frame (compile_sha256_bytesm v m)) /\
  (!v. deploy_blocks_frame (compile_sha256_word v)) /\
  deploy_blocks_frame compile_builtin_calldatasize /\
  (!a b c. deploy_blocks_frame (compile_slice_calldata a b c)) /\
  (!a b c d. deploy_blocks_frame (compile_builtin_len a b c d)) /\
  (!v. deploy_blocks_frame (compile_blockhash v)) /\
  (!v. deploy_blocks_frame (compile_blobhash v)) /\
  (!a b c. deploy_blocks_frame (compile_addmod a b c)) /\
  (!a b c. deploy_blocks_frame (compile_mulmod a b c)) /\
  (!a b. deploy_blocks_frame (compile_ceil a b)) /\
  (!a b. deploy_blocks_frame (compile_floor a b)) /\
  (!a b. deploy_blocks_frame (compile_pow_mod256 a b)) /\
  (!a b c d. deploy_blocks_frame (compile_ecrecover a b c d)) /\
  (!v. deploy_blocks_frame (unwrap_value cenv v)) /\
  (!a b. deploy_blocks_frame (compile_ecadd_points a b)) /\
  (!a b. deploy_blocks_frame (compile_ecmul_point a b)) /\
  (!a b c d. deploy_blocks_frame (compile_concat cfn cenv a b c d)) /\
  (!a b c. deploy_blocks_frame (compile_slice_code a b c)) /\
  (!n. deploy_blocks_frame (compile_slice_out_buf n)) /\
  (!a b c d. deploy_blocks_frame (compile_slice_extcode a b c d)) /\
  (!v. deploy_blocks_frame (compile_bytestring_src v)) /\
  (!a b c d e. deploy_blocks_frame (compile_slice_data a b c d e)) /\
  (!a b c. deploy_blocks_frame (compile_uint2str a b c)) /\
  (!a b c. deploy_blocks_frame (compile_as_wei_value_decimal a b c)) /\
  (!a b c. deploy_blocks_frame (compile_as_wei_value_int a b c)) /\
  (!a b c. deploy_blocks_frame (compile_method_id_runtime a b c)) /\
  (!a b c d. deploy_blocks_frame (compile_make_tuple cfn cenv a b c d)) /\
  (!a b c d e. deploy_blocks_frame (compile_make_array cfn cenv a b c d e)) ==>
  deploy_blocks_frame (compile_builtin_dispatch_body cfn cenv ret_ty ty bi args)
Proof
  strip_tac >> Cases_on `bi` >>
  simp[deploy_blocks_frame_def, compile_builtin_dispatch_body_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  simp[deploy_blocks_frame_equation,
       oneline as_stack_val_def, oneline as_ptr_val_def] >>
  qpat_x_assum `_ = (x,t)` mp_tac >>
  simp[pairTheory.pair_CASE_def, pairTheory.ELIM_UNCURRY,
       oneline as_stack_val_def, oneline as_ptr_val_def] >>
  strip_tac >> rpt IF_CASES_TAC >> gvs[deploy_blocks_frame_equation] >>
  all_tac
  >~ [`compile_keccak256_word`]
  >- (Cases_on `expr_type (HD args)` >> gvs[deploy_blocks_frame_equation] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> gvs[deploy_blocks_frame_equation] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> gvs[deploy_blocks_frame_equation])
  >~ [`compile_sha256_word`]
  >- (Cases_on `expr_type (HD args)` >> gvs[deploy_blocks_frame_equation] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> gvs[deploy_blocks_frame_equation] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> gvs[deploy_blocks_frame_equation])
  >~ [`compile_make_tuple`]
  >- (Cases_on `o'` >> gvs[deploy_blocks_frame_equation])
  >>~- ([`bytestring_literal_hash`],
        Cases_on `bytestring_literal_hash (HD args)` >>
        Cases_on `bytestring_literal_hash (HD (TL args))` >>
        gvs[deploy_blocks_frame_equation]) >>
  TRY (Cases_on `HD (TL args)` >> gvs[deploy_blocks_frame_equation] >>
       rename1 `Builtin et bb es` >> Cases_on `bb` >>
       gvs[deploy_blocks_frame_equation] >> rpt IF_CASES_TAC >>
       gvs[deploy_blocks_frame_equation] >> NO_TAC) >>
  Cases_on `method_id_literal (HD args)` >> gvs[deploy_blocks_frame_equation]
QED

Theorem deploy_blocks_frame_invalid_expr_call[simp]:
  deploy_blocks_frame (invalid_expr_call ty)
Proof
  simp[deploy_blocks_frame_def, invalid_expr_call_def] >>
  rpt strip_tac >> simp[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_blocks_frame_expr_child_callback_bounded:
  (!ty e. expr_size e < n ==> deploy_blocks_frame (f cenv ty e)) ==>
  !ty e. deploy_blocks_frame (expr_child_callback n f cenv ty e)
Proof
  strip_tac >> rpt gen_tac >>
  simp[deploy_blocks_frame_def, expr_child_callback_def] >>
  rpt strip_tac >> IF_CASES_TAC >>
  metis_tac[deploy_blocks_frame_def, deploy_blocks_frame_invalid_expr_call]
QED

Theorem deploy_blocks_frame_builtin_child_callback_bounded:
  (!rt ty bi args. list_size expr_size args < n ==>
    deploy_blocks_frame (f cenv rt ty bi args)) ==>
  !rt ty bi args. deploy_blocks_frame (builtin_child_callback n f cenv rt ty bi args)
Proof
  strip_tac >> rpt gen_tac >>
  simp[deploy_blocks_frame_def, builtin_child_callback_def] >>
  rpt strip_tac >> IF_CASES_TAC >>
  metis_tac[deploy_blocks_frame_def, deploy_blocks_frame_invalid_expr_call]
QED

Theorem deploy_blocks_frame_type_child_callback_bounded:
  (!vt ty tb rt args. list_size expr_size args < n ==>
    deploy_blocks_frame (f cenv vt ty tb rt args)) ==>
  !vt ty tb rt args. deploy_blocks_frame (type_child_callback n f cenv vt ty tb rt args)
Proof
  strip_tac >> rpt gen_tac >>
  simp[deploy_blocks_frame_def, type_child_callback_def] >>
  rpt strip_tac >> IF_CASES_TAC >>
  metis_tac[deploy_blocks_frame_def, deploy_blocks_frame_invalid_expr_call]
QED

(* Transparent lower-helper conjunctions.  The final generator assembly
   discharges these from the context, ABI, builtin and expression helper
   families.  No recursive compiler or body-frame fact is assumed here. *)
Definition deploy_expr_lower_contract_def:
  deploy_expr_lower_contract cenv <=>
  !cfn. (!t e. deploy_blocks_frame (cfn cenv t e)) ==>
  (!t e. deploy_blocks_frame (lower_value cfn cenv t e)) /\
  (!t at v. deploy_blocks_frame (compile_ifexp_arm cenv t at v)) /\
  (!t a b c d f g. deploy_blocks_frame (compile_addmod_names cenv t a b c d f g)) /\
  (!t a b c d f g. deploy_blocks_frame (compile_mulmod_names cenv t a b c d f g)) /\
  (!t a b c d. deploy_blocks_frame (compile_powmod256_names cenv t a b c d)) /\
  (!t ty a b. deploy_blocks_frame (compile_subscript cfn cenv t ty a b)) /\
  (!t ty a b. deploy_blocks_frame (compile_attribute cfn cenv t ty a b)) /\
  (!t fs buf off. deploy_blocks_frame (compile_struct_lit cfn cenv t fs buf off)) /\
  (!t (ty:vyperAST$type) target args (dr:expr option).
    deploy_blocks_frame (compile_call cfn cenv t ty target args dr)) /\
  (!target. deploy_blocks_frame (compile_get_target_ptr cfn cenv target)) /\
  (!a b c d f g. deploy_blocks_frame (compile_dynarray_pop a b c d f g))
End

Definition deploy_builtin_lower_contract_def:
  deploy_builtin_lower_contract cenv <=>
  !cfn. (!t e. deploy_blocks_frame (cfn cenv t e)) ==>
  (!t e. deploy_blocks_frame (lower_value cfn cenv t e)) /\
  (!es. deploy_blocks_frame (compile_multi_exprs cfn cenv es)) /\
  (!a b c d. deploy_blocks_frame (compile_var_array_membership cenv a b c d)) /\
  (!a b c d e f. deploy_blocks_frame (compile_binop a b c d e f)) /\
  (!v. deploy_blocks_frame (compile_builtin_abs v)) /\
  (!e i. deploy_blocks_frame (compile_acc cfn cenv e i)) /\
  (!v. deploy_blocks_frame (compile_keccak256_bytes v)) /\
  (!v m. deploy_blocks_frame (compile_keccak256_bytesm v m)) /\
  (!v. deploy_blocks_frame (compile_keccak256_word v)) /\
  (!v. deploy_blocks_frame (compile_sha256_bytes v)) /\
  (!v m. deploy_blocks_frame (compile_sha256_bytesm v m)) /\
  (!v. deploy_blocks_frame (compile_sha256_word v)) /\
  deploy_blocks_frame compile_builtin_calldatasize /\
  (!a b c. deploy_blocks_frame (compile_slice_calldata a b c)) /\
  (!a b c d. deploy_blocks_frame (compile_builtin_len a b c d)) /\
  (!v. deploy_blocks_frame (compile_blockhash v)) /\
  (!v. deploy_blocks_frame (compile_blobhash v)) /\
  (!a b c. deploy_blocks_frame (compile_addmod a b c)) /\
  (!a b c. deploy_blocks_frame (compile_mulmod a b c)) /\
  (!a b. deploy_blocks_frame (compile_ceil a b)) /\
  (!a b. deploy_blocks_frame (compile_floor a b)) /\
  (!a b. deploy_blocks_frame (compile_pow_mod256 a b)) /\
  (!a b c d. deploy_blocks_frame (compile_ecrecover a b c d)) /\
  (!v. deploy_blocks_frame (unwrap_value cenv v)) /\
  (!a b. deploy_blocks_frame (compile_ecadd_points a b)) /\
  (!a b. deploy_blocks_frame (compile_ecmul_point a b)) /\
  (!a b c d. deploy_blocks_frame (compile_concat cfn cenv a b c d)) /\
  (!a b c. deploy_blocks_frame (compile_slice_code a b c)) /\
  (!n. deploy_blocks_frame (compile_slice_out_buf n)) /\
  (!a b c d. deploy_blocks_frame (compile_slice_extcode a b c d)) /\
  (!v. deploy_blocks_frame (compile_bytestring_src v)) /\
  (!a b c d e. deploy_blocks_frame (compile_slice_data a b c d e)) /\
  (!a b c. deploy_blocks_frame (compile_uint2str a b c)) /\
  (!a b c. deploy_blocks_frame (compile_as_wei_value_decimal a b c)) /\
  (!a b c. deploy_blocks_frame (compile_as_wei_value_int a b c)) /\
  (!a b c. deploy_blocks_frame (compile_method_id_runtime a b c)) /\
  (!a b c d. deploy_blocks_frame (compile_make_tuple cfn cenv a b c d)) /\
  (!a b c d e. deploy_blocks_frame (compile_make_array cfn cenv a b c d e))
End

Definition deploy_type_lower_contract_def:
  deploy_type_lower_contract cenv <=>
  !cfn. (!t e. deploy_blocks_frame (cfn cenv t e)) ==>
  (!ty e. deploy_blocks_frame (lower_value cfn cenv ty e)) /\
  (!n v k. deploy_blocks_frame (compile_bytestring_widen_copy n v k)) /\
  (!v conv. deploy_blocks_frame (compile_type_convert v conv)) /\
  (!n z. deploy_blocks_frame (compile_builtin_empty_complex n z)) /\
  (!v. deploy_blocks_frame (compile_bytestring_src v)) /\
  (!a b c. deploy_blocks_frame (compile_extract32_load a b c)) /\
  (!v ty. deploy_blocks_frame (compile_clamp_basetype v ty)) /\
  (!v. deploy_blocks_frame (unwrap_value cenv v)) /\
  (!a:bool. !b c d e. deploy_blocks_frame (builtinAbi$lower_abi_encode a b c d e)) /\
  (!args. deploy_blocks_frame (compile_abi_encode_args cfn cenv args)) /\
  (!buf off vs. deploy_blocks_frame (compile_store_abi_tuple cenv buf off vs)) /\
  (!a b c d e. deploy_blocks_frame (lower_abi_decode a b c d e))
End

Theorem deploy_blocks_frame_expr_body_assembled:
  deploy_expr_lower_contract cenv /\
  (!t e. deploy_blocks_frame (cfn cenv t e)) /\
  (!t ty bi args. deploy_blocks_frame (bfn cenv t ty bi args)) /\
  (!t ty tb rt args. deploy_blocks_frame (tfn cenv t ty tb rt args)) ==>
  deploy_blocks_frame (compile_expr_body cfn bfn tfn cenv ty e)
Proof
  strip_tac >>
  qpat_x_assum `deploy_expr_lower_contract _` mp_tac >>
  simp[deploy_expr_lower_contract_def] >>
  disch_then (qspec_then `cfn` mp_tac) >> simp[] >> strip_tac >>
  irule deploy_blocks_frame_expr_body >> simp[]
QED

Theorem deploy_blocks_frame_builtin_body_assembled:
  deploy_builtin_lower_contract cenv /\
  (!t e. deploy_blocks_frame (cfn cenv t e)) ==>
  deploy_blocks_frame (compile_builtin_dispatch_body cfn cenv rt ty bi args)
Proof
  strip_tac >>
  qpat_x_assum `deploy_builtin_lower_contract _` mp_tac >>
  simp[deploy_builtin_lower_contract_def] >>
  disch_then (qspec_then `cfn` mp_tac) >> simp[] >> strip_tac >>
  irule deploy_blocks_frame_builtin_dispatch_body >> simp[]
QED

Theorem deploy_blocks_frame_type_body_assembled:
  deploy_type_lower_contract cenv /\
  (!t e. deploy_blocks_frame (cfn cenv t e)) ==>
  deploy_blocks_frame (compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args)
Proof
  strip_tac >>
  qpat_x_assum `deploy_type_lower_contract _` mp_tac >>
  simp[deploy_type_lower_contract_def] >>
  disch_then (qspec_then `cfn` mp_tac) >> simp[] >> strip_tac >>
  irule deploy_blocks_frame_type_builtin_dispatch_body >> simp[]
QED

Theorem deploy_blocks_frame_expr_mutual_cond:
  (!ce. deploy_expr_lower_contract ce /\ deploy_builtin_lower_contract ce /\
        deploy_type_lower_contract ce) ==>
  (!ce ty e. deploy_blocks_frame (compile_expr ce ty e)) /\
  (!ce rt ty bi args. deploy_blocks_frame (compile_builtin_dispatch ce rt ty bi args)) /\
  (!ce vt ty tb rt args. deploy_blocks_frame (compile_type_builtin_dispatch ce vt ty tb rt args))
Proof
  strip_tac >> rewrite_tac[deploy_blocks_frame_def] >>
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> BETA_TAC >>
  rpt gen_tac >> strip_tac
  >~ [`compile_expr_body`]
  >- (irule (REWRITE_RULE [deploy_blocks_frame_def]
         deploy_blocks_frame_expr_body_assembled) >>
      rpt conj_tac >> simp[] >> rpt gen_tac >>
      rewrite_tac[expr_child_callback_def, builtin_child_callback_def,
                  type_child_callback_def] >> BETA_TAC >> IF_CASES_TAC >>
      simp[REWRITE_RULE [deploy_blocks_frame_def]
        deploy_blocks_frame_invalid_expr_call])
  >~ [`compile_builtin_dispatch_body`]
  >- (irule (REWRITE_RULE [deploy_blocks_frame_def]
         deploy_blocks_frame_builtin_body_assembled) >>
      rpt conj_tac >> simp[] >> rpt gen_tac >>
      rewrite_tac[expr_child_callback_def] >> BETA_TAC >> IF_CASES_TAC >>
      simp[REWRITE_RULE [deploy_blocks_frame_def]
        deploy_blocks_frame_invalid_expr_call]) >>
  gvs[] >> irule (REWRITE_RULE [deploy_blocks_frame_def]
       deploy_blocks_frame_type_body_assembled) >>
  rpt conj_tac >> simp[] >> rpt gen_tac >>
  rewrite_tac[expr_child_callback_def] >> BETA_TAC >> IF_CASES_TAC >>
  simp[REWRITE_RULE [deploy_blocks_frame_def]
    deploy_blocks_frame_invalid_expr_call]
QED

Theorem deploy_blocks_frame_compile_expr_cond:
  (!ce. deploy_expr_lower_contract ce /\ deploy_builtin_lower_contract ce /\
        deploy_type_lower_contract ce) ==>
  deploy_blocks_frame (compile_expr cenv ty e)
Proof
  metis_tac[deploy_blocks_frame_expr_mutual_cond]
QED

Theorem deploy_blocks_frame_compile_builtin_dispatch_cond:
  (!ce. deploy_expr_lower_contract ce /\ deploy_builtin_lower_contract ce /\
        deploy_type_lower_contract ce) ==>
  deploy_blocks_frame (compile_builtin_dispatch cenv rt ty bi args)
Proof
  metis_tac[deploy_blocks_frame_expr_mutual_cond]
QED

Theorem deploy_blocks_frame_compile_type_builtin_dispatch_cond:
  (!ce. deploy_expr_lower_contract ce /\ deploy_builtin_lower_contract ce /\
        deploy_type_lower_contract ce) ==>
  deploy_blocks_frame (compile_type_builtin_dispatch cenv vt ty tb rt args)
Proof
  metis_tac[deploy_blocks_frame_expr_mutual_cond]
QED
