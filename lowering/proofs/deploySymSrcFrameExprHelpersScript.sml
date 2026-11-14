Theory deploySymSrcFrameExprHelpers
Ancestors
  deploySymSrcBlockFrame exprLowering compileEnv
  targetPlaceLive targetPlaceSimCasesBase

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

(* Match_mp_tac retains the source order of the two closure premises. *)
fun frame_tac g =
  (simp[comp_ignore_bind_def] >>
   rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
     >- (simp[] >> frame_tac) >> gen_tac >> BETA_TAC) >> simp[]) g;

Theorem deploy_blocks_frame_compile_clamp[simp]:
  deploy_blocks_frame (compile_clamp v ty)
Proof
  simp[compile_clamp_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >> frame_tac
QED

Theorem deploy_blocks_frame_clamp_and_return[simp]:
  deploy_blocks_frame (clamp_and_return v ty)
Proof simp[clamp_and_return_def]
QED

Theorem deploy_blocks_frame_clamp_basetype[simp]:
  deploy_blocks_frame (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[compile_clamp_basetype_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[compile_clamp_basetype_def]) >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem deploy_blocks_frame_safe_add[simp]:
  deploy_blocks_frame (compile_safe_add x y ty)
Proof
  simp[compile_safe_add_def] >> irule deploy_blocks_frame_bind >> simp[] >>
  gen_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem deploy_blocks_frame_safe_sub[simp]:
  deploy_blocks_frame (compile_safe_sub x y ty)
Proof
  simp[compile_safe_sub_def] >> irule deploy_blocks_frame_bind >> simp[] >>
  gen_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem deploy_blocks_frame_mul_overflow[simp]:
  deploy_blocks_frame (compile_mul_overflow_check x y res sg bits)
Proof
  simp[compile_mul_overflow_check_def] >>
  Cases_on `sg /\ bits = 256` >> simp[] >> frame_tac
QED

Theorem deploy_blocks_frame_safe_mul[simp]:
  deploy_blocks_frame (compile_safe_mul x y ty)
Proof
  simp[compile_safe_mul_def] >>
  Cases_on `type_bits ty > 128` >>
  Cases_on `is_decimal_type ty` >>
  Cases_on `type_bits ty < 256` >> simp[]
QED

Theorem deploy_blocks_frame_safe_div[simp]:
  deploy_blocks_frame (compile_safe_div x y ty)
Proof
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >> simp[compile_safe_div_def] >> frame_tac
QED

Theorem deploy_blocks_frame_safe_decimal_div[simp]:
  deploy_blocks_frame (compile_safe_decimal_div x y divisor ty)
Proof simp[compile_safe_decimal_div_def] >> frame_tac
QED

Theorem deploy_blocks_frame_safe_mod[simp]:
  deploy_blocks_frame (compile_safe_mod x y ty)
Proof Cases_on `is_signed_type ty` >> simp[compile_safe_mod_def]
QED

Theorem deploy_blocks_frame_safe_pow[simp]:
  deploy_blocks_frame (compile_safe_pow x y ty bl el)
Proof
  Cases_on `bl` >> Cases_on `el` >> simp[compile_safe_pow_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem deploy_blocks_frame_compare[simp]:
  deploy_blocks_frame (compile_compare op x y ty)
Proof
  Cases_on `op` >> simp[compile_compare_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem deploy_blocks_frame_wrap_truncate[simp]:
  deploy_blocks_frame (wrap_truncate v ty)
Proof simp[wrap_truncate_def] >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem deploy_blocks_frame_binop:
  (!c x y. deploy_blocks_frame (compile_select c x y)) ==>
  deploy_blocks_frame (compile_binop op x y ty bl el)
Proof
  strip_tac >> Cases_on `op` >> simp[compile_binop_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem deploy_blocks_frame_bytestring_hash[simp]:
  deploy_blocks_frame (compile_bytestring_hash p)
Proof simp[compile_bytestring_hash_def] >> frame_tac
QED

Theorem deploy_blocks_frame_membership_eqs[simp]:
  !es n. deploy_blocks_frame (emit_membership_eqs n es)
Proof Induct >> simp[emit_membership_eqs_def] >> frame_tac
QED

Theorem deploy_blocks_frame_membership_or[simp]:
  !es acc. deploy_blocks_frame (fold_membership_or acc es)
Proof Induct >> simp[fold_membership_or_def] >> frame_tac
QED

Theorem deploy_blocks_frame_membership_and[simp]:
  !es acc. deploy_blocks_frame (fold_membership_and acc es)
Proof Induct >> simp[fold_membership_and_def] >> frame_tac
QED

Theorem deploy_blocks_frame_list_membership_in[simp]:
  deploy_blocks_frame (compile_list_membership_in n es)
Proof
  simp[compile_list_membership_in_def] >>
  match_mp_tac deploy_blocks_frame_bind >> simp[] >> Cases >> simp[]
QED

Theorem deploy_blocks_frame_list_membership_notin[simp]:
  deploy_blocks_frame (compile_list_membership_notin n es)
Proof
  simp[compile_list_membership_notin_def] >>
  match_mp_tac deploy_blocks_frame_bind >> simp[] >> Cases >> simp[] >> frame_tac
QED

Theorem deploy_blocks_frame_array_membership_loop:
  (!p. deploy_blocks_frame (loader p)) ==>
  deploy_blocks_frame (compile_array_membership_loop n arr len sz off loader bd isin)
Proof
  strip_tac >> Cases_on `bd` >> Cases_on `off > 0` >> Cases_on `isin` >>
  simp[compile_array_membership_loop_def] >> frame_tac
QED

Theorem deploy_blocks_frame_var_array_membership:
  (!ctor imm loc off. deploy_blocks_frame (compile_ptr_load ctor imm loc off)) ==>
  deploy_blocks_frame (compile_var_array_membership cenv n vv ty isin)
Proof
  strip_tac >> Cases_on `ty` >>
  TRY (rename1 `ArrayT t bd` >> Cases_on `bd`) >>
  simp[compile_var_array_membership_def] >>
  simp[deploy_blocks_frame_array_membership_loop] >>
  frame_tac >> irule deploy_blocks_frame_array_membership_loop >> simp[]
QED

Theorem deploy_blocks_frame_mapping_subscript[simp]:
  deploy_blocks_frame (compile_mapping_subscript slot key)
Proof simp[compile_mapping_subscript_def] >> frame_tac
QED

Theorem deploy_blocks_frame_keccak256_key[simp]:
  deploy_blocks_frame (compile_keccak256_key key bs32)
Proof Cases_on `bs32` >> simp[compile_keccak256_key_def] >> frame_tac
QED

Theorem deploy_blocks_frame_extcodesize_check[simp]:
  deploy_blocks_frame (compile_extcodesize_check addr)
Proof simp[compile_extcodesize_check_def] >> frame_tac
QED

Theorem deploy_blocks_frame_return_value_decode:
  (!c x y. deploy_blocks_frame (compile_select c x y)) ==>
  deploy_blocks_frame (compile_return_value_decode lo hi)
Proof strip_tac >> simp[compile_return_value_decode_def] >> frame_tac
QED

Theorem deploy_blocks_frame_unwrap_value:
  (!ctor imm loc off. deploy_blocks_frame (compile_ptr_load ctor imm loc off)) /\
  (!p loc bytes words ctor imm.
    deploy_blocks_frame (compile_ensure_in_memory p loc bytes words ctor imm)) ==>
  deploy_blocks_frame (unwrap_value cenv vv)
Proof
  strip_tac >> Cases_on `vv` >> simp[unwrap_value_def] >>
  IF_CASES_TAC >> simp[] >> Cases_on `p.ptr_location` >> simp[]
QED

Theorem deploy_blocks_frame_multi_vvs:
  !es. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_multi_vvs cfn cenv es)
Proof Induct >> simp[compile_multi_vvs_def] >> strip_tac >> frame_tac
QED

Theorem deploy_blocks_frame_extcall_store_values:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst. deploy_blocks_frame (compile_store_bytestring v dst)) ==>
  !vs buf off. deploy_blocks_frame (compile_extcall_store_values cenv vs buf off)
Proof
  strip_tac >> Induct >> simp[compile_extcall_store_values_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[compile_extcall_store_values_def] >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >> simp[] >> frame_tac
QED

Theorem deploy_blocks_frame_default_return_path:
  (!v dst dt st. deploy_blocks_frame (compile_store_memory cenv v dst dt st)) /\
  (!lo hi. deploy_blocks_frame (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. deploy_blocks_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  deploy_blocks_frame (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)
Proof
  strip_tac >> Cases_on `skip` >> simp[compile_default_return_path_def] >> frame_tac
QED

Theorem deploy_blocks_frame_external_call_kwargs:
  (!vs buf off. deploy_blocks_frame (compile_extcall_store_values cenv vs buf off)) /\
  (!dst src info. deploy_blocks_frame (compile_abi_encode_to_buf dst src info)) /\
  (!rt dt buf res dop addr skip lo hi info.
     deploy_blocks_frame (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)) /\
  (!lo hi. deploy_blocks_frame (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. deploy_blocks_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  deploy_blocks_frame (compile_external_call_kwargs cenv addr vals tys mem abi mid rabi lo rmem static value gas skip has_default dop rt dt einfo dinfo)
Proof
  strip_tac >> simp[compile_external_call_kwargs_def] >>
  frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem deploy_blocks_frame_dynarray_append:
  (!v dst dt st. deploy_blocks_frame (compile_store_memory cenv v dst dt st)) /\
  (!src dst n sl dl imm. deploy_blocks_frame (compile_word_copy_loop src dst n sl dl imm)) /\
  (!src slot ty trans. deploy_blocks_frame (compile_store_slots cenv src slot ty trans)) ==>
  deploy_blocks_frame (compile_dynarray_append cenv arr v ws sz dt st cap prim ld sd)
Proof
  strip_tac >> simp[compile_dynarray_append_def] >>
  frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem deploy_blocks_frame_dynarray_pop:
  (!ctor imm loc off. deploy_blocks_frame (compile_ptr_load ctor imm loc off)) /\
  (!ctor imm loc off v. deploy_blocks_frame (compile_ptr_store ctor imm loc off v)) ==>
  deploy_blocks_frame (compile_dynarray_pop arr ws sz ctor imm loc)
Proof strip_tac >> simp[compile_dynarray_pop_def] >> frame_tac
QED

Theorem deploy_blocks_frame_stage_intcall_args:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst. deploy_blocks_frame (compile_store_bytestring v dst)) /\
  (!v dst dt st. deploy_blocks_frame (compile_store_memory cenv v dst dt st)) ==>
  !vs flags tys.
    (!e. MEM e vs ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_stage_intcall_args cfn cenv vs flags tys)
Proof
  strip_tac >> Induct >> simp[compile_stage_intcall_args_def] >>
  rpt gen_tac >> Cases_on `flags` >> Cases_on `tys` >>
  simp[compile_stage_intcall_args_def] >>
  TRY (Cases_on `h'` >> simp[compile_stage_intcall_args_def]) >>
  strip_tac >> frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem deploy_blocks_frame_store_multi_results[simp]:
  !vs buf off. deploy_blocks_frame (store_multi_results buf vs off)
Proof Induct >> simp[store_multi_results_def] >> rpt gen_tac >> frame_tac
QED

Theorem deploy_blocks_frame_array_subscript:
  (!p. deploy_blocks_frame (loader p)) ==>
  deploy_blocks_frame (compile_array_subscript arr idx dyn cnt ws sz sg loader)
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `sg` >>
  simp[compile_array_subscript_def] >> frame_tac
QED

Theorem deploy_blocks_frame_tuple_subscript[simp]:
  deploy_blocks_frame (compile_tuple_subscript arr off)
Proof simp[compile_tuple_subscript_def]
QED

Theorem deploy_blocks_frame_store_byte_chunks[simp]:
  !p bs off. deploy_blocks_frame (compile_store_byte_chunks p bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def] >> frame_tac >> gvs[]
QED

Theorem deploy_blocks_frame_bytelike_literal[simp]:
  deploy_blocks_frame (compile_bytelike_literal bs maxlen)
Proof simp[compile_bytelike_literal_def] >> frame_tac
QED

Theorem deploy_blocks_frame_literal_vv[simp]:
  deploy_blocks_frame (compile_literal_vv ty lit)
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BoolL b` >> Cases_on `b` >> simp[compile_literal_vv_def]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BaseT b` >> Cases_on `b` >> simp[compile_literal_vv_def]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[compile_literal_vv_def]) >> frame_tac
QED

Theorem deploy_blocks_frame_name_vv[simp]:
  deploy_blocks_frame (compile_name_vv cenv ty id)
Proof
  simp[compile_name_vv_def] >> Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
  Cases_on `x` >> simp[] >> frame_tac
QED

Theorem deploy_blocks_frame_env_var[simp]:
  deploy_blocks_frame (compile_env_var item)
Proof Cases_on `item` >> simp[compile_env_var_def] >> frame_tac
QED

Theorem deploy_blocks_frame_load_bytestring_as_word[simp]:
  deploy_blocks_frame (load_bytestring_as_word v opc)
Proof Cases_on `opc = SAR` >> simp[load_bytestring_as_word_def] >> frame_tac
QED

Theorem deploy_blocks_frame_int_clamp[simp]:
  deploy_blocks_frame (compile_int_clamp sg bits v)
Proof Cases_on `sg` >> simp[compile_int_clamp_def] >> frame_tac
QED

Theorem deploy_blocks_frame_type_convert[simp]:
  deploy_blocks_frame (compile_type_convert v conv)
Proof
  Cases_on `conv` >> simp[compile_type_convert_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac >>
  rpt (IF_CASES_TAC >> simp[] >> frame_tac) >>
  pairarg_tac >> simp[] >> frame_tac >>
  rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem deploy_blocks_frame_bytestring_widen_copy:
  (!dst src sz. deploy_blocks_frame (compile_copy_memory dst src sz)) ==>
  deploy_blocks_frame (compile_bytestring_widen_copy dstsz v srcsz)
Proof strip_tac >> simp[compile_bytestring_widen_copy_def] >> frame_tac
QED

Theorem deploy_blocks_frame_neg[simp]:
  deploy_blocks_frame (compile_neg v ty)
Proof simp[compile_neg_def] >> pairarg_tac >> simp[] >> frame_tac
QED

Theorem deploy_blocks_frame_lower_value:
  deploy_blocks_frame (cfn cenv ty e) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (lower_value cfn cenv ty e)
Proof simp[lower_value_def]
QED

Theorem deploy_blocks_frame_lower_value_with_loc:
  deploy_blocks_frame (cfn cenv ty e) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (lower_value_with_loc cfn cenv ty e)
Proof simp[lower_value_with_loc_def]
QED

Theorem deploy_blocks_frame_as_stack_val:
  deploy_blocks_frame m ==>
  deploy_blocks_frame (\st. as_stack_val ty (m st))
Proof
  rw[deploy_blocks_frame_def] >> Cases_on `m st` >>
  gvs[as_stack_val_def] >>
  first_x_assum drule >> disch_then (qspec_then `B` mp_tac) >> simp[as_stack_val_def, as_ptr_val_def]
QED

Theorem deploy_blocks_frame_as_ptr_val:
  deploy_blocks_frame m ==>
  deploy_blocks_frame (\st. as_ptr_val ty loc (m st))
Proof
  rw[deploy_blocks_frame_def] >> Cases_on `m st` >>
  gvs[as_ptr_val_def] >>
  first_x_assum drule >> disch_then (qspec_then `B` mp_tac) >> simp[as_stack_val_def, as_ptr_val_def]
QED

Theorem deploy_blocks_frame_multi_exprs:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  !es. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_multi_exprs cfn cenv es)
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def] >>
  rpt strip_tac >> match_mp_tac deploy_blocks_frame_bind >> conj_tac
  >- (irule deploy_blocks_frame_lower_value >> simp[]) >> simp[]
QED

Theorem deploy_blocks_frame_make_tuple:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  !es tys buf off.
    (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_make_tuple cfn cenv es tys buf off)
Proof
  strip_tac >> Induct >> rpt gen_tac >> Cases_on `tys` >> simp[compile_make_tuple_def] >>
  rpt strip_tac >> frame_tac
QED

Theorem deploy_blocks_frame_make_array_elems:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  !es et sz lw buf idx.
    (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_make_array_elems cfn cenv es et sz lw buf idx)
Proof
  strip_tac >> Induct >> simp[compile_make_array_elems_def] >>
  rpt strip_tac >> frame_tac
QED

Theorem deploy_blocks_frame_make_array:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) /\
  (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_make_array cfn cenv es et sz lw buf)
Proof
  strip_tac >> simp[compile_make_array_def, comp_ignore_bind_def] >>
  match_mp_tac deploy_blocks_frame_bind >> conj_tac
  >- (Cases_on `lw` >> simp[]) >>
  simp[deploy_blocks_frame_make_array_elems]
QED

Theorem deploy_blocks_frame_concat:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  !es dp infos off.
    (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_concat cfn cenv es dp infos off)
Proof
  strip_tac >> Induct >> simp[compile_concat_def] >> rpt gen_tac >>
  Cases_on `infos` >> simp[compile_concat_def] >> Cases_on `h'` >>
  strip_tac >> Cases_on `q` >> simp[compile_concat_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
       >- simp[deploy_blocks_frame_lower_value] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_store_abi_tuple:
  (!dst src n. deploy_blocks_frame (compile_copy_memory dst src n)) ==>
  !vs buf off. deploy_blocks_frame (compile_store_abi_tuple cenv buf off vs)
Proof
  strip_tac >> Induct >> simp[compile_store_abi_tuple_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[]) >> simp[]
QED

Theorem deploy_blocks_frame_materialize_vv:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  deploy_blocks_frame (compile_materialize_vv cenv ty vv)
Proof simp[compile_materialize_vv_def, comp_ignore_bind_def]
QED

Theorem deploy_blocks_frame_ifexp_arm:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  deploy_blocks_frame (compile_ifexp_arm cenv rt at vv)
Proof
  strip_tac >> rw[compile_ifexp_arm_def, comp_ignore_bind_def] >> simp[]
QED

Theorem deploy_blocks_frame_snapshot_vv:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) ==>
  deploy_blocks_frame (compile_snapshot_vv cenv copy vv)
Proof strip_tac >> rw[compile_snapshot_vv_def] >> simp[]
QED

Theorem deploy_blocks_frame_struct_lit:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  !fields ty buf off.
    (!nm e. MEM (nm,e) fields ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_struct_lit cfn cenv ty fields buf off)
Proof
  strip_tac >> Induct >> simp[compile_struct_lit_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  simp[compile_struct_lit_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> first_x_assum irule >> metis_tac[]
QED

Theorem deploy_blocks_frame_abi_encode_args:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) ==>
  !es. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_abi_encode_args cfn cenv es)
Proof
  strip_tac >> Induct >> simp[compile_abi_encode_args_def] >> rpt strip_tac >>
  match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[]) >> simp[]
QED

Theorem deploy_blocks_frame_ext_call_kwarg:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) /\
  (!ty. deploy_blocks_frame (cfn cenv ty e)) ==>
  deploy_blocks_frame (compile_ext_call_kwarg cfn cenv rt k e)
Proof
  strip_tac >> rw[compile_ext_call_kwarg_def] >>
  simp[deploy_blocks_frame_lower_value]
QED

Theorem deploy_blocks_frame_ext_call_kwargs:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) ==>
  !es ks rt.
    (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_ext_call_kwargs cfn cenv rt ks es)
Proof
  strip_tac >> Induct >> Cases_on `ks` >> simp[compile_ext_call_kwargs_def] >>
  rpt strip_tac >> match_mp_tac deploy_blocks_frame_bind >> conj_tac
  >- (irule deploy_blocks_frame_ext_call_kwarg >> simp[]) >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem deploy_blocks_frame_create_salt:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!e. opt = SOME e ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_create_salt cfn cenv opt)
Proof
  Cases_on `opt` >> simp[compile_create_salt_def, deploy_blocks_frame_lower_value]
QED

Theorem deploy_blocks_frame_store_words[simp]:
  !vs buf off. deploy_blocks_frame (compile_store_words buf vs off)
Proof
  Induct >> rpt gen_tac >> Cases_on `off = 0` >> simp[compile_store_words_def]
QED

Theorem deploy_blocks_frame_invert[simp]:
  deploy_blocks_frame (compile_invert v ty cenv)
Proof Cases_on `ty` >> simp[compile_invert_def]
QED

Theorem deploy_blocks_frame_attribute:
  deploy_blocks_frame (cfn cenv ty base_e) ==>
  deploy_blocks_frame (compile_attribute cfn cenv rt ty base_e fld)
Proof simp[compile_attribute_def]
QED

Theorem deploy_blocks_frame_extcall_store_args:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst. deploy_blocks_frame (compile_store_bytestring v dst)) ==>
  !es tys buf off.
    (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_extcall_store_args cfn cenv es tys buf off)
Proof
  strip_tac >> Induct >> simp[compile_extcall_store_args_def] >>
  rpt gen_tac >> Cases_on `tys` >> rpt strip_tac >>
  simp[compile_extcall_store_args_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
       >- simp[deploy_blocks_frame_lower_value] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
       >- (rpt IF_CASES_TAC >> simp[]) >> gen_tac >> BETA_TAC) >> simp[]
QED

(* Equation interface for helpers written as explicit state-passing lets. *)
Theorem deploy_blocks_frame_equation:
  deploy_blocks_frame m ==>
  m (s with cs_blocks := s.cs_blocks ++ B) =
    (FST (m s), (SND (m s)) with cs_blocks := (SND (m s)).cs_blocks ++ B)
Proof
  strip_tac >> Cases_on `m s` >> gvs[] >>
  fs[deploy_blocks_frame_def]
QED

Theorem deploy_blocks_frame_acc:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  deploy_blocks_frame (cfn cenv (BaseT AddressT) e) ==>
  deploy_blocks_frame (compile_acc cfn cenv e acc)
Proof
  strip_tac >>
  `deploy_blocks_frame (lower_value cfn cenv (BaseT AddressT) e)` by
    simp[deploy_blocks_frame_lower_value] >>
  Cases_on `acc` >>
  simp[deploy_blocks_frame_def, compile_acc_def] >> rpt strip_tac >>
  simp[deploy_blocks_frame_equation,
       deploy_blocks_frame_emit_op, deploy_blocks_frame_emit_inst] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_blocks_frame_addmod_names:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!a b m. deploy_blocks_frame (compile_addmod a b m)) ==>
  deploy_blocks_frame (compile_addmod_names cenv rt aty a bty b mty m)
Proof
  strip_tac >> simp[deploy_blocks_frame_def, compile_addmod_names_def] >>
  rpt strip_tac >> simp[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()]
QED

Theorem deploy_blocks_frame_mulmod_names:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!a b m. deploy_blocks_frame (compile_mulmod a b m)) ==>
  deploy_blocks_frame (compile_mulmod_names cenv rt aty a bty b mty m)
Proof
  strip_tac >> simp[deploy_blocks_frame_def, compile_mulmod_names_def] >>
  rpt strip_tac >> simp[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()]
QED

Theorem deploy_blocks_frame_powmod256_names:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!a b. deploy_blocks_frame (compile_pow_mod256 a b)) ==>
  deploy_blocks_frame (compile_powmod256_names cenv rt aty a bty b)
Proof
  strip_tac >> simp[deploy_blocks_frame_def, compile_powmod256_names_def] >>
  rpt strip_tac >> simp[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()]
QED

Theorem deploy_blocks_frame_ext_call_args:
  (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!copy vv. deploy_blocks_frame (compile_snapshot_vv cenv copy vv)) ==>
  deploy_blocks_frame (compile_ext_call_args cfn cenv kw_es tys es)
Proof
  qid_spec_tac `tys` >> Induct_on `es` >>
  simp[compile_ext_call_args_def] >>
  gen_tac >> Cases_on `tys` >> simp[compile_ext_call_args_def] >>
  strip_tac >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_get_target_ptr:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v b. deploy_blocks_frame (compile_keccak256_key v b)) /\
  (!v k. deploy_blocks_frame (compile_mapping_subscript v k)) /\
  (!b i d n ws sz si loc.
    deploy_blocks_frame (compile_array_subscript b i d n ws sz si
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc))) ==>
  !t. (!e. MEM e (target_indices t) ==>
        deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
      deploy_blocks_frame (compile_get_target_ptr cfn cenv t)
Proof
  strip_tac >> ho_match_mp_tac base_assignment_target_induct >>
  rpt conj_tac
  >- (gen_tac >> simp[target_indices_def, compile_get_target_ptr_def] >>
      namedCases_on `FLOOKUP cenv.ce_vars id` ["", "binding"] >> simp[] >>
      Cases_on `binding` >> simp[])
  >- (gen_tac >> simp[target_indices_def, compile_get_target_ptr_def] >>
      namedCases_on `FLOOKUP cenv.ce_module_vars nsid` ["", "binding"] >> simp[] >>
      Cases_on `binding` >> simp[])
  >- (simp[target_indices_def, compile_get_target_ptr_def] >>
      rpt strip_tac >> match_mp_tac deploy_blocks_frame_bind >> conj_tac
      >- (first_x_assum irule >> simp[]) >>
      gen_tac >> BETA_TAC >>
      namedCases_on `SND (SND x)` ["", "pt"] >> simp[]
      >- simp[deploy_blocks_frame_lower_value] >>
      Cases_on `pt` >> simp[] >>
      rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
           >- simp[deploy_blocks_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[]) >>
  simp[target_indices_def, compile_get_target_ptr_def]
QED

Theorem deploy_blocks_frame_subscript:
  (!copy vv. deploy_blocks_frame (compile_snapshot_vv cenv copy vv)) /\
  deploy_blocks_frame (cfn cenv ty base_e) /\
  deploy_blocks_frame (cfn cenv ty idx_e) /\
  deploy_blocks_frame (cfn cenv (expr_type idx_e) idx_e) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v b. deploy_blocks_frame (compile_keccak256_key v b)) /\
  (!v k. deploy_blocks_frame (compile_mapping_subscript v k)) /\
  (!v off. deploy_blocks_frame (compile_tuple_subscript v off)) /\
  (!b i d n ws sz si loc.
    deploy_blocks_frame (compile_array_subscript b i d n ws sz si
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc))) ==>
  deploy_blocks_frame (compile_subscript cfn cenv rt ty base_e idx_e)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >>
  namedCases_on `place_type cenv base_e` ["kt vt", "bt"]
  >- (simp[] >>
      rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
           >- simp[deploy_blocks_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
           >- simp[deploy_blocks_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[]) >>
  Cases_on `bt` >> simp[deploy_blocks_frame_lower_value] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
       >- (rpt IF_CASES_TAC >> simp[deploy_blocks_frame_lower_value]) >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_create_ctor_tuple:
  (!vs p off. deploy_blocks_frame (compile_extcall_store_values cenv vs p off)) /\
  deploy_blocks_frame (compile_multi_vvs cfn cenv es) ==>
  deploy_blocks_frame (compile_create_ctor_tuple cfn cenv es)
Proof
  strip_tac >> simp[compile_create_ctor_tuple_def, comp_ignore_bind_def]
QED

Theorem deploy_blocks_frame_create_blueprint_args:
  (!p s enc. deploy_blocks_frame (compile_abi_encode_to_buf p s enc)) /\
  deploy_blocks_frame (compile_create_ctor_tuple cfn cenv es) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_create_blueprint_args cfn cenv raw es)
Proof
  strip_tac >> Cases_on `raw`
  >- (Cases_on `es` >> simp[compile_create_blueprint_args_def] >>
      Cases_on `t` >> simp[compile_create_blueprint_args_def,
        deploy_blocks_frame_lower_value] >>
      Cases_on `t'` >> simp[compile_create_blueprint_args_def]) >>
  rw[compile_create_blueprint_args_def] >> simp[]
QED

Theorem deploy_blocks_frame_create_snapshot:
  (!p d n loc. deploy_blocks_frame (compile_slot_to_memory p d n loc)) /\
  (!b a p d n off. deploy_blocks_frame (compile_imm_copy_to_memory b a p d n off)) /\
  (!d s n. deploy_blocks_frame (compile_copy_memory_dynamic d s n)) ==>
  deploy_blocks_frame (compile_create_snapshot cenv vv ty)
Proof
  strip_tac >> simp[compile_create_snapshot_def, comp_ignore_bind_def] >>
  match_mp_tac deploy_blocks_frame_bind >> simp[] >> gen_tac >>
  Cases_on `vv_location vv` >> simp[] >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp[]
QED

Theorem deploy_blocks_frame_raw_create:
  deploy_blocks_frame (cfn cenv (expr_type bytecode) bytecode) /\
  deploy_blocks_frame (lower_value cfn cenv (expr_type value) value) /\
  (!vv ty. deploy_blocks_frame (compile_create_snapshot cenv vv ty)) /\
  (!d s n. deploy_blocks_frame (compile_copy_memory_dynamic d s n)) /\
  deploy_blocks_frame (compile_create_ctor_tuple cfn cenv es) /\
  (!d s enc. deploy_blocks_frame (compile_abi_encode_to_buf d s enc)) /\
  deploy_blocks_frame (compile_create_salt cfn cenv salt) /\
  (!p n v s b. deploy_blocks_frame (compile_create_dispatch p n v s b)) ==>
  deploy_blocks_frame (compile_raw_create cfn cenv bytecode value es salt rof)
Proof
  strip_tac >> simp[compile_raw_create_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac deploy_blocks_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
           gen_tac >> BETA_TAC) >> simp[]) >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem deploy_blocks_frame_create_call:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v. deploy_blocks_frame (compile_create_proxy_buf v)) /\
  (!p n v s b. deploy_blocks_frame (compile_create_dispatch p n v s b)) /\
  (!v w s b. deploy_blocks_frame (compile_create_copy v w s b)) /\
  (!v off. deploy_blocks_frame (compile_create_blueprint_check v off)) /\
  (!v w s off n p len b.
     deploy_blocks_frame (compile_create_blueprint_append v w s off n p len b)) /\
  (!es raw. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
     deploy_blocks_frame (compile_create_blueprint_args cfn cenv raw es)) /\
  (!bytecode value es salt b.
     deploy_blocks_frame (cfn cenv (expr_type bytecode) bytecode) /\
     deploy_blocks_frame (cfn cenv (expr_type value) value) /\
     (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) /\
     (!e. salt = SOME e ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
     deploy_blocks_frame (compile_raw_create cfn cenv bytecode value es salt b)) /\
  (!e. MEM e args ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_create_call cfn cenv ck has_salt rof args)
Proof
  strip_tac >> Cases_on `args` >> simp[compile_create_call_def] >>
  Cases_on `t` >> simp[compile_create_call_def] >>
  rename1 `target::value::rest` >>
  Cases_on `ck` >> Cases_on `has_salt` >>
  simp[compile_create_call_def, deploy_blocks_frame_lower_value,
       deploy_blocks_frame_create_salt] >>
  Cases_on `rest` >> simp[compile_create_call_def,
    deploy_blocks_frame_lower_value, deploy_blocks_frame_create_salt] >>
  gvs[] >>
  simp[deploy_blocks_frame_lower_value, deploy_blocks_frame_create_salt] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
       >- simp[deploy_blocks_frame_lower_value, deploy_blocks_frame_create_salt] >>
       gen_tac >> BETA_TAC) >> simp[]
  >~ [`compile_create_blueprint_args`]
  >- (Cases_on `t` >> gvs[] >>
      rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
           >- simp[deploy_blocks_frame_lower_value, deploy_blocks_frame_create_salt] >>
           gen_tac >> BETA_TAC) >> pairarg_tac >> simp[])
  >~ [`compile_create_blueprint_append`]
  >- (pairarg_tac >> simp[]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[rich_listTheory.MEM_FRONT, rich_listTheory.MEM_LAST, listTheory.MEM]
QED

Theorem deploy_blocks_frame_call_internal:
  (!opc ops n. deploy_blocks_frame (emit_multi_op opc ops n)) /\
  (!stack tys. deploy_blocks_frame (compile_stage_intcall_args cfn cenv args stack tys)) /\
  (!buf vs off. deploy_blocks_frame (store_multi_results buf vs off)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty (IntCall id) args dr)
Proof
  strip_tac >> simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `returns_count > 0` >> Cases_on `return_buf_size > 0` >>
  gvs[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation]) >>
  gvs[AllCaseEqs()]
QED

Theorem deploy_blocks_frame_call_external:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!copy vv. deploy_blocks_frame (compile_snapshot_vv cenv copy vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!a vs ts ms az mid rz mn rb sc v g sk hd d rt dt ei di.
    deploy_blocks_frame (compile_external_call_kwargs cenv a vs ts ms az mid rz mn rb
      sc v g sk hd d rt dt ei di)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty (ExtCall sc sk sig opts) args dr)
Proof
  strip_tac >> PairCases_on `sig` >> Cases_on `args`
  >- (simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
      simp[deploy_blocks_frame_equation] >> rpt (pairarg_tac >> gvs[])) >>
  `deploy_blocks_frame (lower_value cfn cenv (BaseT AddressT) h)` by
    (irule deploy_blocks_frame_lower_value >> simp[]) >>
  `deploy_blocks_frame (compile_ext_call_args cfn cenv
      (DROP (LENGTH sig1) t)
      (MAP (lowered_value_type cenv) (TAKE (LENGTH sig1) t))
      (TAKE (LENGTH sig1) t))` by
    (irule deploy_blocks_frame_ext_call_args >> simp[] >>
     metis_tac[rich_listTheory.MEM_TAKE, listTheory.MEM]) >>
  `deploy_blocks_frame (compile_ext_call_kwargs cfn cenv sig2 opts (DROP (LENGTH sig1) t))` by
    (first_x_assum irule >> metis_tac[rich_listTheory.MEM_DROP_IMP, listTheory.MEM]) >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  simp[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation]) >>
  Cases_on `gas_opt` >> Cases_on `value_opt` >> Cases_on `default_opt` >>
  gvs[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation]) >>
  IF_CASES_TAC >> gvs[]
QED

Theorem deploy_blocks_frame_call_send:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty (Send gas) args dr)
Proof
  strip_tac >> Cases_on `args` >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  rpt (CASE_TAC >> gvs[]) >>
  gvs[deploy_blocks_frame_equation, deploy_blocks_frame_lower_value] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation,
                          deploy_blocks_frame_lower_value])
QED

Theorem deploy_blocks_frame_call_raw_revert:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v. deploy_blocks_frame (compile_raw_revert v)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty RawRevert args dr)
Proof
  strip_tac >> Cases_on `args` >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  rpt (CASE_TAC >> gvs[]) >>
  gvs[deploy_blocks_frame_equation, deploy_blocks_frame_lower_value] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation,
                          deploy_blocks_frame_lower_value])
QED

Theorem deploy_blocks_frame_call_selfdestruct:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v. deploy_blocks_frame (compile_selfdestruct v)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty SelfDestructTarget args dr)
Proof
  strip_tac >> Cases_on `args` >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  rpt (CASE_TAC >> gvs[]) >>
  gvs[deploy_blocks_frame_equation, deploy_blocks_frame_lower_value] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation,
                          deploy_blocks_frame_lower_value])
QED

Theorem deploy_blocks_frame_call_raw:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!n. deploy_blocks_frame (compile_raw_call_outbuf n)) /\
  (!a p n g v ct sz rof ov op.
    deploy_blocks_frame (compile_raw_call_finish a p n g v ct sz rof ov op)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty (RawCallTarget rcf) args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
      simp[deploy_blocks_frame_equation] >> rpt (pairarg_tac >> gvs[])) >>
  Cases_on `t`
  >- (simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
      simp[deploy_blocks_frame_equation] >> rpt (pairarg_tac >> gvs[])) >>
  `deploy_blocks_frame (compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws t')` by
    (first_x_assum irule >> simp[]) >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  simp[deploy_blocks_frame_equation, deploy_blocks_frame_lower_value] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation,
                          deploy_blocks_frame_lower_value]) >>
  Cases_on `gas_opt` >> Cases_on `value_opt` >>
  gvs[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation]) >>
  IF_CASES_TAC >> gvs[]
QED

Theorem deploy_blocks_frame_call_raw_calldata:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!n. deploy_blocks_frame (compile_raw_call_outbuf n)) /\
  deploy_blocks_frame compile_msg_data_to_memory /\
  (!a p n g v ct sz rof ov op.
    deploy_blocks_frame (compile_raw_call_finish a p n g v ct sz rof ov op)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty (RawCallCalldataTarget rcf) args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
      simp[deploy_blocks_frame_equation] >> rpt (pairarg_tac >> gvs[])) >>
  `deploy_blocks_frame (compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws t)` by
    (first_x_assum irule >> simp[]) >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  simp[deploy_blocks_frame_equation, deploy_blocks_frame_lower_value] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation,
                          deploy_blocks_frame_lower_value]) >>
  Cases_on `gas_opt` >> Cases_on `value_opt` >>
  gvs[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation]) >>
  IF_CASES_TAC >> gvs[]
QED

Theorem deploy_blocks_frame_call_raw_log_pair:
  (!e. MEM e (raw_log_topic_exprs topics) ==>
       deploy_blocks_frame (cfn cenv (expr_type e) e)) /\
  deploy_blocks_frame (cfn cenv (expr_type data) data) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty RawLog [topics; data] dr)
Proof
  strip_tac >>
  `deploy_blocks_frame (compile_multi_exprs cfn cenv (raw_log_topic_exprs topics))` by
    (irule deploy_blocks_frame_multi_exprs >> simp[]) >>
  `deploy_blocks_frame (lower_value cfn cenv (expr_type data) data)` by
    simp[deploy_blocks_frame_lower_value] >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  simp[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation]) >>
  IF_CASES_TAC >> gvs[deploy_blocks_frame_equation] >>
  rpt (pairarg_tac >> gvs[deploy_blocks_frame_equation])
QED

Theorem deploy_blocks_frame_call_raw_log:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!topics data e. args = [topics; data] /\ MEM e (raw_log_topic_exprs topics) ==>
       deploy_blocks_frame (cfn cenv (expr_type e) e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty RawLog args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
      simp[deploy_blocks_frame_equation] >> rpt (pairarg_tac >> gvs[])) >>
  Cases_on `t`
  >- (simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
      simp[deploy_blocks_frame_equation] >> rpt (pairarg_tac >> gvs[])) >>
  Cases_on `t'`
  >- (irule deploy_blocks_frame_call_raw_log_pair >> simp[]) >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  simp[deploy_blocks_frame_equation] >> rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_blocks_frame_call:
  (!opc ops n. deploy_blocks_frame (emit_multi_op opc ops n)) /\
  (!copy vv. deploy_blocks_frame (compile_snapshot_vv cenv copy vv)) /\
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!topics data e. target = RawLog /\ args = [topics; data] /\
     MEM e (raw_log_topic_exprs topics) ==>
     deploy_blocks_frame (cfn cenv (expr_type e) e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!stack tys. deploy_blocks_frame (compile_stage_intcall_args cfn cenv args stack tys)) /\
  (!a vs ts ms az mid rz mn rb sc v g sk hd d rt dt ei di.
    deploy_blocks_frame (compile_external_call_kwargs cenv a vs ts ms az mid rz mn rb
      sc v g sk hd d rt dt ei di)) /\
  (!n. deploy_blocks_frame (compile_raw_call_outbuf n)) /\
  (!a p n g v ct sz rof ov op.
    deploy_blocks_frame (compile_raw_call_finish a p n g v ct sz rof ov op)) /\
  deploy_blocks_frame compile_msg_data_to_memory /\
  (!v. deploy_blocks_frame (compile_raw_revert v)) /\
  (!v. deploy_blocks_frame (compile_selfdestruct v)) /\
  (!ck salt rof. deploy_blocks_frame (compile_create_call cfn cenv ck salt rof args)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty target args dr)
Proof
  strip_tac >> Cases_on `target`
  >- (irule deploy_blocks_frame_call_internal >> simp[])
  >- (irule deploy_blocks_frame_call_external >> simp[])
  >- (irule deploy_blocks_frame_call_send >> simp[])
  >- (irule deploy_blocks_frame_call_raw >> simp[])
  >- (irule deploy_blocks_frame_call_raw_calldata >> simp[])
  >- (irule deploy_blocks_frame_call_raw_log >> simp[])
  >- (irule deploy_blocks_frame_call_raw_revert >> simp[])
  >- (irule deploy_blocks_frame_call_selfdestruct >> simp[]) >>
  simp[deploy_blocks_frame_def, compile_call_def] >> rpt strip_tac >>
  simp[deploy_blocks_frame_equation, oneline as_stack_val_def] >>
  gvs[oneline as_stack_val_def, AllCaseEqs()]
QED

(* Coverage: noncallback arithmetic/operand helpers; callback list builders;
   target addressing; creation; every compile_call target (including derived
   RawLog topic expressions); modular name fast paths. Lower context/ABI and
   builtin frame facts remain explicit at their call boundaries for assembly. *)
