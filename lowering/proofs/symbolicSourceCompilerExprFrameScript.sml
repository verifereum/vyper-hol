Theory symbolicSourceCompilerExprFrame
Ancestors symbolicSourceCompilerFrame symbolicSourceCompilerCreateFrame exprLowering compileEnv emitHelper
Libs symbolicSourceCompilerFrameLib

open symbolicSourceCompilerFrameLib

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind]];

Theorem symbolic_frame_compile_clamp[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_clamp v ty)
Proof
  strip_tac >>
  simp[compile_clamp_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >> frame_tac
QED

Theorem symbolic_frame_clamp_and_return[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (clamp_and_return v ty)
Proof
  strip_tac >>
  simp[clamp_and_return_def]
QED

Theorem symbolic_frame_clamp_basetype[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_clamp_basetype v ty)
Proof
  strip_tac >>
  Cases_on `ty` >> simp[compile_clamp_basetype_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[compile_clamp_basetype_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[compile_clamp_basetype_def]) >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem symbolic_frame_safe_add[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_safe_add x y ty)
Proof
  strip_tac >>
  simp[compile_safe_add_def] >> irule symbolic_frame_bind >> simp[] >>
  gen_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem symbolic_frame_safe_sub[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_safe_sub x y ty)
Proof
  strip_tac >>
  simp[compile_safe_sub_def] >> irule symbolic_frame_bind >> simp[] >>
  gen_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem symbolic_frame_mul_overflow[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_mul_overflow_check x y res sg bits)
Proof
  strip_tac >>
  simp[compile_mul_overflow_check_def] >>
  Cases_on `sg /\ bits = 256` >> simp[] >> frame_tac
QED

Theorem symbolic_frame_safe_mul[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_safe_mul x y ty)
Proof
  strip_tac >>
  simp[compile_safe_mul_def] >>
  Cases_on `type_bits ty > 128` >>
  Cases_on `is_decimal_type ty` >>
  Cases_on `type_bits ty < 256` >> simp[]
QED

Theorem symbolic_frame_safe_div[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_safe_div x y ty)
Proof
  strip_tac >>
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >> simp[compile_safe_div_def] >> frame_tac
QED

Theorem symbolic_frame_safe_decimal_div[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_safe_decimal_div x y divisor ty)
Proof
  strip_tac >>
  simp[compile_safe_decimal_div_def] >> frame_tac
QED

Theorem symbolic_frame_safe_mod[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_safe_mod x y ty)
Proof
  strip_tac >>
  Cases_on `is_signed_type ty` >> simp[compile_safe_mod_def]
QED

Theorem symbolic_frame_safe_pow[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_safe_pow x y ty bl el)
Proof
  strip_tac >>
  Cases_on `bl` >> Cases_on `el` >> simp[compile_safe_pow_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem symbolic_frame_compare[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_compare op x y ty)
Proof
  strip_tac >>
  Cases_on `op` >> simp[compile_compare_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem symbolic_frame_wrap_truncate[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (wrap_truncate v ty)
Proof
  strip_tac >>
  simp[wrap_truncate_def] >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem symbolic_frame_binop:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!c x y. symbolic_frame R (compile_select c x y)) ==>
  symbolic_frame R (compile_binop op x y ty bl el)
Proof
  strip_tac >> Cases_on `op` >> simp[compile_binop_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem symbolic_frame_bytestring_hash[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_bytestring_hash p)
Proof
  strip_tac >>
  simp[compile_bytestring_hash_def] >> frame_tac
QED

Theorem symbolic_frame_membership_eqs[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  !es n. symbolic_frame R (emit_membership_eqs n es)
Proof
  strip_tac >>
  Induct >> simp[emit_membership_eqs_def] >> frame_tac
QED

Theorem symbolic_frame_membership_or[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  !es acc. symbolic_frame R (fold_membership_or acc es)
Proof
  strip_tac >>
  Induct >> simp[fold_membership_or_def] >> frame_tac
QED

Theorem symbolic_frame_membership_and[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  !es acc. symbolic_frame R (fold_membership_and acc es)
Proof
  strip_tac >>
  Induct >> simp[fold_membership_and_def] >> frame_tac
QED

Theorem symbolic_frame_list_membership_in[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_list_membership_in n es)
Proof
  strip_tac >>
  simp[compile_list_membership_in_def] >>
  match_mp_tac symbolic_frame_bind >> simp[] >> Cases >> simp[]
QED

Theorem symbolic_frame_list_membership_notin[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_list_membership_notin n es)
Proof
  strip_tac >>
  simp[compile_list_membership_notin_def] >>
  match_mp_tac symbolic_frame_bind >> simp[] >> Cases >> simp[] >> frame_tac
QED

Theorem symbolic_frame_array_membership_loop:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!label. symbolic_frame R (fresh_label label)) /\
  (!label. symbolic_frame R (new_block label)) /\
  symbolic_frame R fresh_var /\
  (!p. symbolic_frame R (loader p)) ==>
  symbolic_frame R (compile_array_membership_loop n arr len sz off loader bd isin)
Proof
  strip_tac >> Cases_on `bd` >> Cases_on `off > 0` >> Cases_on `isin` >>
  simp[compile_array_membership_loop_def] >>
  rpt (FIRST [irule symbolic_frame_ignore_bind >> conj_tac,
              irule symbolic_frame_bind >> conj_tac,
              gen_tac,
              CHANGED_TAC (asm_simp_tac bool_ss [symbolic_frame_return])])
QED

Theorem symbolic_frame_var_array_membership:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!label. symbolic_frame R (fresh_label label)) /\
  (!label. symbolic_frame R (new_block label)) /\
  symbolic_frame R fresh_var /\
  (!ctor imm loc off. symbolic_frame R (compile_ptr_load ctor imm loc off)) ==>
  symbolic_frame R (compile_var_array_membership cenv n vv ty isin)
Proof
  strip_tac >> Cases_on `ty` >>
  TRY (rename1 `ArrayT t bd` >> Cases_on `bd`) >>
  simp[compile_var_array_membership_def] >>
  simp[symbolic_frame_array_membership_loop] >>
  frame_tac >> irule symbolic_frame_array_membership_loop >> simp[]
QED

Theorem symbolic_frame_mapping_subscript:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_mapping_subscript slot key)
Proof strip_tac >> simp[compile_mapping_subscript_def] >> frame_tac
QED

Theorem symbolic_frame_keccak256_key:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_keccak256_key key bs32)
Proof strip_tac >> Cases_on `bs32` >> simp[compile_keccak256_key_def] >> frame_tac
QED

Theorem symbolic_frame_extcodesize_check[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_extcodesize_check addr)
Proof
  strip_tac >>
  simp[compile_extcodesize_check_def] >> frame_tac
QED

Theorem symbolic_frame_ext_call_args:
  (!e ty. MEM e es ==> symbolic_frame R (cfn cenv ty e)) /\
  (!copy vv. symbolic_frame R (compile_snapshot_vv cenv copy vv)) ==>
  symbolic_frame R (compile_ext_call_args cfn cenv kw_es tys es)
Proof
  qid_spec_tac `tys` >> Induct_on `es` >>
  simp[compile_ext_call_args_def] >>
  gen_tac >> Cases_on `tys` >> simp[compile_ext_call_args_def] >>
  strip_tac >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_store_abi_tuple:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!dst src n. symbolic_frame R (compile_copy_memory dst src n)) ==>
  !vs buf off. symbolic_frame R (compile_store_abi_tuple cenv buf off vs)
Proof
  strip_tac >> Induct >> simp[compile_store_abi_tuple_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[]) >> simp[]
QED

Theorem symbolic_frame_materialize_vv:
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst ty sty. symbolic_frame R (compile_store_memory cenv v dst ty sty)) ==>
  symbolic_frame R (compile_materialize_vv cenv ty vv)
Proof
  simp[compile_materialize_vv_def, comp_ignore_bind_def]
QED

Theorem symbolic_frame_ifexp_arm:
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst ty sty. symbolic_frame R (compile_store_memory cenv v dst ty sty)) ==>
  symbolic_frame R (compile_ifexp_arm cenv rt at vv)
Proof
  strip_tac >> rw[compile_ifexp_arm_def, comp_ignore_bind_def] >> simp[]
QED

Theorem symbolic_frame_snapshot_vv:
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!ty vv. symbolic_frame R (compile_materialize_vv cenv ty vv)) ==>
  symbolic_frame R (compile_snapshot_vv cenv copy vv)
Proof
  strip_tac >> rw[compile_snapshot_vv_def] >> simp[]
QED

Theorem symbolic_frame_multi_exprs:
  (!vv. symbolic_frame R (unwrap_value cenv vv)) ==>
  !es. (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
  symbolic_frame R (compile_multi_exprs cfn cenv es)
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def] >>
  rpt strip_tac >> match_mp_tac symbolic_frame_bind >> conj_tac
  >- (irule symbolic_frame_lower_value >> simp[]) >>
  simp[]
QED

Theorem symbolic_frame_make_tuple:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst ty sty. symbolic_frame R (compile_store_memory cenv v dst ty sty)) ==>
  !es tys buf off.
    (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
    symbolic_frame R (compile_make_tuple cfn cenv es tys buf off)
Proof
  strip_tac >> Induct >> rpt gen_tac >> Cases_on `tys` >> simp[compile_make_tuple_def] >>
  rpt strip_tac >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_make_array_elems:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst ty sty. symbolic_frame R (compile_store_memory cenv v dst ty sty)) ==>
  !es et sz lw buf idx.
    (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
    symbolic_frame R (compile_make_array_elems cfn cenv es et sz lw buf idx)
Proof
  strip_tac >> Induct >> simp[compile_make_array_elems_def] >>
  rpt strip_tac >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_make_array:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst ty sty. symbolic_frame R (compile_store_memory cenv v dst ty sty)) /\
  (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
  symbolic_frame R (compile_make_array cfn cenv es et sz lw buf)
Proof
  strip_tac >> simp[compile_make_array_def, comp_ignore_bind_def] >>
  match_mp_tac symbolic_frame_bind >> conj_tac
  >- (Cases_on `lw` >> simp[]) >>
  simp[symbolic_frame_make_array_elems]
QED

Theorem symbolic_frame_concat:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) ==>
  !es dp infos off.
    (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
    symbolic_frame R (compile_concat cfn cenv es dp infos off)
Proof
  strip_tac >> Induct >> simp[compile_concat_def] >> rpt gen_tac >>
  Cases_on `infos` >> simp[compile_concat_def] >> Cases_on `h'` >>
  strip_tac >> Cases_on `q` >> simp[compile_concat_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
       >- simp[symbolic_frame_lower_value] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_struct_lit:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst ty sty. symbolic_frame R (compile_store_memory cenv v dst ty sty)) ==>
  !fields ty buf off.
    (!nm e. MEM (nm,e) fields ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
    symbolic_frame R (compile_struct_lit cfn cenv ty fields buf off)
Proof
  strip_tac >> Induct >> simp[compile_struct_lit_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  simp[compile_struct_lit_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> first_x_assum irule >> metis_tac[]
QED

Theorem symbolic_frame_return_value_decode:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!c x y. symbolic_frame R (compile_select c x y)) ==>
  symbolic_frame R (compile_return_value_decode lo hi)
Proof strip_tac >> simp[compile_return_value_decode_def] >> frame_tac
QED

Theorem symbolic_frame_unwrap_value:
  (!ctor imm loc off. symbolic_frame R (compile_ptr_load ctor imm loc off)) /\
  (!p loc bytes words ctor imm.
    symbolic_frame R (compile_ensure_in_memory p loc bytes words ctor imm)) ==>
  symbolic_frame R (unwrap_value cenv vv)
Proof
  strip_tac >> Cases_on `vv` >> simp[unwrap_value_def] >>
  IF_CASES_TAC >> simp[] >> Cases_on `p.ptr_location` >> simp[]
QED

Theorem symbolic_frame_multi_vvs:
  !es. (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
  symbolic_frame R (compile_multi_vvs cfn cenv es)
Proof Induct >> simp[compile_multi_vvs_def] >> strip_tac >> frame_tac
QED

Theorem symbolic_frame_dynarray_append:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!ctor imm loc off. symbolic_frame R (compile_ptr_load ctor imm loc off)) /\
  (!ctor imm loc off v. symbolic_frame R (compile_ptr_store ctor imm loc off v)) /\
  (!im p off n i. symbolic_frame R (compile_imm_store_words im p off n i)) /\
  (!v dst dt st. symbolic_frame R (compile_store_memory cenv v dst dt st)) /\
  (!src dst n sl dl imm. symbolic_frame R (compile_word_copy_loop src dst n sl dl imm)) /\
  (!src slot ty trans. symbolic_frame R (compile_store_slots cenv src slot ty trans)) ==>
  symbolic_frame R (compile_dynarray_append cenv arr v ws sz dt st cap prim loc)
Proof
  strip_tac >> simp[compile_dynarray_append_def] >>
  frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem symbolic_frame_dynarray_pop:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!ctor imm loc off. symbolic_frame R (compile_ptr_load ctor imm loc off)) /\
  (!ctor imm loc off v. symbolic_frame R (compile_ptr_store ctor imm loc off v)) ==>
  symbolic_frame R (compile_dynarray_pop arr ws sz ctor imm loc)
Proof
  strip_tac >> simp[compile_dynarray_pop_def] >> frame_tac
QED

Theorem symbolic_frame_store_multi_results:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  !vs buf off. symbolic_frame R (store_multi_results buf vs off)
Proof
  strip_tac >> Induct >> simp[store_multi_results_def] >> rpt gen_tac >> frame_tac
QED

Theorem symbolic_frame_array_subscript:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!p. symbolic_frame R (loader p)) ==>
  symbolic_frame R (compile_array_subscript arr idx dyn cnt ws sz sg loader)
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `sg` >>
  simp[compile_array_subscript_def] >> frame_tac
QED

Theorem symbolic_frame_store_byte_chunks:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  !p bs off. symbolic_frame R (compile_store_byte_chunks p bs off)
Proof
  strip_tac >> recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def] >> frame_tac >>
  gvs[]
QED

Theorem symbolic_frame_bytelike_literal:
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!p bs off. symbolic_frame R (compile_store_byte_chunks p bs off)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_bytelike_literal bs maxlen)
Proof
  strip_tac >> simp[compile_bytelike_literal_def] >> frame_tac
QED

Theorem symbolic_frame_literal_vv:
  (!bs n. symbolic_frame R (compile_bytelike_literal bs n)) ==>
  symbolic_frame R (compile_literal_vv ty lit)
Proof
  strip_tac >> Cases_on `lit` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BoolL b` >> Cases_on `b` >> simp[compile_literal_vv_def]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BaseT b` >> Cases_on `b` >> simp[compile_literal_vv_def]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[compile_literal_vv_def]) >> frame_tac
QED

Theorem symbolic_frame_name_vv:
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) ==>
  symbolic_frame R (compile_name_vv cenv ty id)
Proof
  strip_tac >> simp[compile_name_vv_def] >> Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
  rename1 `FLOOKUP cenv.ce_vars id = SOME loc` >> Cases_on `loc` >> simp[] >> frame_tac
QED

Theorem symbolic_frame_env_var:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_env_var item)
Proof
  strip_tac >> Cases_on `item` >> simp[compile_env_var_def] >> frame_tac
QED

Theorem symbolic_frame_load_bytestring_as_word[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (load_bytestring_as_word v opc)
Proof
  strip_tac >> Cases_on `opc = SAR` >> simp[load_bytestring_as_word_def] >> frame_tac
QED

Theorem symbolic_frame_int_clamp[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_int_clamp sg bits v)
Proof
  strip_tac >> Cases_on `sg` >> simp[compile_int_clamp_def] >> frame_tac
QED

Theorem symbolic_frame_type_convert:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_type_convert v conv)
Proof
  strip_tac >> Cases_on `conv` >> simp[compile_type_convert_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac >>
  rpt (IF_CASES_TAC >> simp[] >> frame_tac) >>
  pairarg_tac >> simp[] >> frame_tac >>
  rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem symbolic_frame_bytestring_widen_copy:
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!dst src sz. symbolic_frame R (compile_copy_memory dst src sz)) ==>
  symbolic_frame R (compile_bytestring_widen_copy dstsz v srcsz)
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def] >> frame_tac
QED

Theorem symbolic_frame_neg:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_neg v ty)
Proof
  strip_tac >> simp[compile_neg_def] >> pairarg_tac >> simp[] >> frame_tac
QED

Theorem symbolic_frame_tuple_subscript:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_tuple_subscript arr off)
Proof
  strip_tac >> simp[compile_tuple_subscript_def]
QED

Theorem symbolic_frame_lower_value_with_loc:
  symbolic_frame R (cfn cenv ty e) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) ==>
  symbolic_frame R (lower_value_with_loc cfn cenv ty e)
Proof
  simp[lower_value_with_loc_def]
QED

Theorem symbolic_frame_as_stack_val:
  symbolic_frame R m ==>
  symbolic_frame R (\st. as_stack_val ty (m st))
Proof
  simp[symbolic_frame_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s g t. R g s t ==> _` drule >>
  Cases_on `m st` >> Cases_on `m st'` >> simp[as_stack_val_def]
QED

Theorem symbolic_frame_as_ptr_val:
  symbolic_frame R m ==>
  symbolic_frame R (\st. as_ptr_val ty loc (m st))
Proof
  simp[symbolic_frame_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s g t. R g s t ==> _` drule >>
  Cases_on `m st` >> Cases_on `m st'` >> simp[as_ptr_val_def]
QED
