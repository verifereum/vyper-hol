(* The positional and supplied keyword parts share the calldata head. *)
Theory groupedKeywordDecode
Ancestors moduleLowering abiEncoder compileEnv emitHelper exprLowering vyperCalldata list arithmetic

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
