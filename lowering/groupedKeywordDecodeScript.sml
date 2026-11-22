(* The positional and supplied keyword parts share the calldata head. *)
Theory groupedKeywordDecode
Ancestors moduleLowering abiEncoder compileEnv emitHelper exprLowering vyperCalldata list arithmetic

Theorem calldata_decode_args_split:
  !pos kw vals cd off.
    calldata_decode_args cd (pos ++ kw) off = SOME vals ==>
    calldata_decode_args cd pos off = SOME (TAKE (LENGTH pos) vals) /\
    calldata_decode_args cd kw (off + SUM (MAP tv_abi_size pos)) =
      SOME (DROP (LENGTH pos) vals)
Proof
  Induct >- simp[calldata_decode_args_def] >>
  rpt gen_tac >> simp[Once calldata_decode_args_def, LET_THM] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC [calldata_decode_args_def] >> simp_tac std_ss [LET_THM] >>
      `4 + off = off + 4` by decide_tac >>
      `4 + w2n (cd_word cd (off + 4)) = w2n (cd_word cd (off + 4)) + 4` by decide_tac >>
      ASM_REWRITE_TAC [] >>
      simp_tac (srw_ss()) []) >>
  `off + (SUM (MAP tv_abi_size pos) + tv_abi_size h) =
     off + tv_abi_size h + SUM (MAP tv_abi_size pos)` by decide_tac >>
  ASM_REWRITE_TAC []
QED

Theorem compile_init_kwargs_supplied_parts:
  0 < k /\
  compile_init_kwargs ce ((name,dst,ty,default_e)::vars) off k hi sa = ((),sb) ==>
  ?src mid first last.
    compile_getelemptr_abi (Lit 4w) (is_abi_dynamic ce.ce_struct_fields ty)
      (off - 4) CALLDATALOAD (Lit 0w) (Lit 0w) sa = (src,mid) /\
    (if is_abi_dynamic ce.ce_struct_fields ty then
       compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) mid = ((),first)
     else first = mid) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last) /\
    compile_init_kwargs ce vars (off + abi_embedded_static_size ce.ce_struct_fields ty)
      (k - 1) hi last = ((),sb)
Proof
  strip_tac >> `k > 0` by decide_tac >>
  qpat_x_assum `compile_init_kwargs _ _ _ _ _ _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [compile_init_kwargs_def]) >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >>
  simp[compile_getelemptr_abi_def,
       compile_abi_dec_addr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> metis_tac[]
QED

Theorem compile_init_kwargs_omitted_parts:
  compile_init_kwargs ce ((name,dst,ty,default_e)::vars) off 0 hi sa = ((),sb) ==>
  ?value mid last.
    lower_value compile_expr ce ty default_e sa = (value,mid) /\
    (if is_word_type ty then emit_void MSTORE [dst; value]
     else if is_bytestring_type ty then compile_store_bytestring value dst
     else emit_void MCOPY [dst; value; Lit (n2w (type_memory_bytes ce ty))]) mid =
    ((),last) /\
    compile_init_kwargs ce vars off 0 hi last = ((),sb)
Proof
  simp[Once compile_init_kwargs_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> metis_tac[]
QED

Theorem compile_create_kwarg_allocas_preserves_specs:
  !specs ce sa vars sb.
    compile_create_kwarg_allocas ce specs sa = (vars,sb) ==>
    MAP (\(name,_,ty,e). (name,ty,e)) vars = specs
Proof
  Induct >- simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  qx_gen_tac `item` >> PairCases_on `item` >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  metis_tac[]
QED
