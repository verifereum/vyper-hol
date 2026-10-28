(* TOP-LEVEL: the actual static child wrapper is its destination ADD and a
   recursive encoder call, including when that call generates new blocks. *)
Theory abiStaticChildCode
Ancestors
  abiComplexCode abiComplexStructure abiEncoder abiEncoderStructure abiStaticLoopCode
  exprLowering compileEnv fragExec list pair arithmetic

Theorem type_to_abi_enc_info_static_base:
  !sfields cenv base_ty.
    ~is_abi_dynamic cenv.ce_struct_fields (BaseT base_ty) ==>
    type_to_abi_enc_info sfields cenv (BaseT base_ty) = AbiCopy (type_memory_bytes cenv (BaseT base_ty))
Proof
  rpt gen_tac >> Cases_on `base_ty` >>
  FIRST [simp_tac (srw_ss()) [Once is_abi_dynamic_def, Once type_to_abi_enc_info_def] >> NO_TAC, ALL_TAC] >>
  rename1 `~is_abi_dynamic _ (BaseT (BytesT byte_bound)) ==> _` >>
  Cases_on `byte_bound` >> simp[Once is_abi_dynamic_def, Once type_to_abi_enc_info_def]
QED

Theorem type_to_abi_enc_info_static:
  !sfields cenv ty.
    ~is_abi_dynamic cenv.ce_struct_fields ty ==>
    type_to_abi_enc_info sfields cenv ty =
      if ty = NoneT then AbiComplex [] else AbiCopy (type_memory_bytes cenv ty)
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `ty` >> simp_tac (srw_ss()) [] >>
  FIRST [irule type_to_abi_enc_info_static_base >> first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def] >> NO_TAC, ALL_TAC] >>
  rename1 `type_to_abi_enc_info _ _ (ArrayT elem bound) = _` >> Cases_on `bound` >>
  gvs[Once is_abi_dynamic_def, Once type_to_abi_enc_info_def] >>
  simp[Once is_abi_dynamic_def]
QED

Theorem compile_abi_child_static_cuts:
  !dst src info head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_child dst src info F head_offset dyn_ptr cs = (ret,cs') <=>
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 0)) src info
      (abi_complex_field_cut dst head_offset cs) = (ret,cs')
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_encode_child_def])) >>
  simp[comp_bind_def, emit_abi_complex_field_address]
QED

Theorem abi_child_static_contains:
  !dst src info head_offset dyn_ptr cs ret cs' func.
    compile_abi_encode_child dst src info F head_offset dyn_ptr cs = (ret,cs') /\
    fn_has_code cs cs' func ==>
    fn_has_code cs (abi_complex_field_cut dst head_offset cs) func /\
    fn_has_code (abi_complex_field_cut dst head_offset cs) cs' func
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_abi_child_static_cuts] >> strip_tac >>
  `cs_extends cs (abi_complex_field_cut dst head_offset cs)` by simp[abi_complex_field_extends] >>
  `cs_extends (abi_complex_field_cut dst head_offset cs) cs'` by
    (drule_all compile_abi_encode_extends >> simp[]) >>
  irule fn_has_code_split >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed static ABI child code cuts: " ^ name)
  end) (DB.thms "abiStaticChildCode")
