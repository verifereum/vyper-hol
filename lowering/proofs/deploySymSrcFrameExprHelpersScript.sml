Theory deploySymSrcFrameExprHelpers
Ancestors
  symbolicSourceCompilerCallFrame
  symbolicSourceCompilerAddressFrame
  symbolicSourceCompilerExprFrame symbolicSourceCompilerCreateFrame
  deploySymSrcBlockFrame deploySymSrcFrameContext exprLowering compileEnv
  targetPlaceLive targetPlaceSimCasesBase

val _ = temp_delsimps ["deploy_blocks_frame_cond"];

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

(* Match_mp_tac retains the source order of the two closure premises. *)
fun frame_tac g =
  (simp[comp_ignore_bind_def] >>
   rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac
     >- (simp[] >> frame_tac) >> gen_tac >> BETA_TAC) >> simp[]) g;

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

Theorem deploy_blocks_frame_compile_clamp[simp]:
  deploy_blocks_frame (compile_clamp v ty)
Proof
  apply_symbolic_frame symbolic_frame_compile_clamp >> simp[]
QED

Theorem deploy_blocks_frame_clamp_and_return[simp]:
  deploy_blocks_frame (clamp_and_return v ty)
Proof
  apply_symbolic_frame symbolic_frame_clamp_and_return >> simp[]
QED

Theorem deploy_blocks_frame_clamp_basetype[simp]:
  deploy_blocks_frame (compile_clamp_basetype v ty)
Proof
  apply_symbolic_frame symbolic_frame_clamp_basetype >> simp[]
QED

Theorem deploy_blocks_frame_safe_add[simp]:
  deploy_blocks_frame (compile_safe_add x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_add >> simp[]
QED

Theorem deploy_blocks_frame_safe_sub[simp]:
  deploy_blocks_frame (compile_safe_sub x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_sub >> simp[]
QED

Theorem deploy_blocks_frame_mul_overflow[simp]:
  deploy_blocks_frame (compile_mul_overflow_check x y res sg bits)
Proof
  apply_symbolic_frame symbolic_frame_mul_overflow >> simp[]
QED

Theorem deploy_blocks_frame_safe_mul[simp]:
  deploy_blocks_frame (compile_safe_mul x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_mul >> simp[]
QED

Theorem deploy_blocks_frame_safe_div[simp]:
  deploy_blocks_frame (compile_safe_div x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_div >> simp[]
QED

Theorem deploy_blocks_frame_safe_decimal_div[simp]:
  deploy_blocks_frame (compile_safe_decimal_div x y divisor ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_decimal_div >> simp[]
QED

Theorem deploy_blocks_frame_safe_mod[simp]:
  deploy_blocks_frame (compile_safe_mod x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_mod >> simp[]
QED

Theorem deploy_blocks_frame_safe_pow[simp]:
  deploy_blocks_frame (compile_safe_pow x y ty bl el)
Proof
  apply_symbolic_frame symbolic_frame_safe_pow >> simp[]
QED

Theorem deploy_blocks_frame_compare[simp]:
  deploy_blocks_frame (compile_compare op x y ty)
Proof
  apply_symbolic_frame symbolic_frame_compare >> simp[]
QED

Theorem deploy_blocks_frame_wrap_truncate[simp]:
  deploy_blocks_frame (wrap_truncate v ty)
Proof
  apply_symbolic_frame symbolic_frame_wrap_truncate >> simp[]
QED

Theorem deploy_blocks_frame_binop:
  (!c x y. deploy_blocks_frame (compile_select c x y)) ==>
  deploy_blocks_frame (compile_binop op x y ty bl el)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_binop >> simp[]
QED

Theorem deploy_blocks_frame_bytestring_hash[simp]:
  deploy_blocks_frame (compile_bytestring_hash p)
Proof
  apply_symbolic_frame symbolic_frame_bytestring_hash >> simp[]
QED

Theorem deploy_blocks_frame_membership_eqs[simp]:
  !es n. deploy_blocks_frame (emit_membership_eqs n es)
Proof
  apply_symbolic_frame symbolic_frame_membership_eqs >> simp[]
QED

Theorem deploy_blocks_frame_membership_or[simp]:
  !es acc. deploy_blocks_frame (fold_membership_or acc es)
Proof
  apply_symbolic_frame symbolic_frame_membership_or >> simp[]
QED

Theorem deploy_blocks_frame_membership_and[simp]:
  !es acc. deploy_blocks_frame (fold_membership_and acc es)
Proof
  apply_symbolic_frame symbolic_frame_membership_and >> simp[]
QED

Theorem deploy_blocks_frame_list_membership_in[simp]:
  deploy_blocks_frame (compile_list_membership_in n es)
Proof
  apply_symbolic_frame symbolic_frame_list_membership_in >> simp[]
QED

Theorem deploy_blocks_frame_list_membership_notin[simp]:
  deploy_blocks_frame (compile_list_membership_notin n es)
Proof
  apply_symbolic_frame symbolic_frame_list_membership_notin >> simp[]
QED

Theorem deploy_blocks_frame_array_membership_loop:
  (!p. deploy_blocks_frame (loader p)) ==>
  deploy_blocks_frame (compile_array_membership_loop n arr len sz off loader bd isin)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_array_membership_loop >> simp[]
QED

Theorem deploy_blocks_frame_var_array_membership:
  (!ctor imm loc off. deploy_blocks_frame (compile_ptr_load ctor imm loc off)) ==>
  deploy_blocks_frame (compile_var_array_membership cenv n vv ty isin)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_var_array_membership >> simp[]
QED

Theorem deploy_blocks_frame_mapping_subscript[simp]:
  deploy_blocks_frame (compile_mapping_subscript slot key)
Proof
  apply_symbolic_frame symbolic_frame_mapping_subscript >> simp[]
QED

Theorem deploy_blocks_frame_keccak256_key[simp]:
  deploy_blocks_frame (compile_keccak256_key key bs32)
Proof
  apply_symbolic_frame symbolic_frame_keccak256_key >> simp[]
QED

Theorem deploy_blocks_frame_extcodesize_check[simp]:
  deploy_blocks_frame (compile_extcodesize_check addr)
Proof
  apply_symbolic_frame symbolic_frame_extcodesize_check >> simp[]
QED

Theorem deploy_blocks_frame_return_value_decode:
  (!c x y. deploy_blocks_frame (compile_select c x y)) ==>
  deploy_blocks_frame (compile_return_value_decode lo hi)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_return_value_decode >> simp[]
QED

Theorem deploy_blocks_frame_unwrap_value:
  (!ctor imm loc off. deploy_blocks_frame (compile_ptr_load ctor imm loc off)) /\
  (!p loc bytes words ctor imm.
    deploy_blocks_frame (compile_ensure_in_memory p loc bytes words ctor imm)) ==>
  deploy_blocks_frame (unwrap_value cenv vv)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_unwrap_value >> simp[]
QED

Theorem deploy_blocks_frame_multi_vvs:
  !es. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_multi_vvs cfn cenv es)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_multi_vvs)
QED

Theorem deploy_blocks_frame_extcall_store_values:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst. deploy_blocks_frame (compile_store_bytestring v dst)) ==>
  !vs buf off. deploy_blocks_frame (compile_extcall_store_values cenv vs buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_extcall_store_values >> simp[]
QED

Theorem deploy_blocks_frame_default_return_path:
  (!v dst dt st. deploy_blocks_frame (compile_store_memory cenv v dst dt st)) /\
  (!lo hi. deploy_blocks_frame (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. deploy_blocks_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  deploy_blocks_frame (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_default_return_path >> simp[]
QED

Theorem deploy_blocks_frame_abi_encode_values_to_buf:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!src dst ty. deploy_blocks_frame (compile_store_memory cenv src dst ty ty)) /\
  (!dst src info. deploy_blocks_frame (compile_abi_encode_to_buf dst src info)) ==>
  deploy_blocks_frame (compile_abi_encode_values_to_buf cenv dst rows)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_abi_encode_values_to_buf >> simp[]
QED

Theorem deploy_blocks_frame_external_call_kwargs:
  (!dst rows. deploy_blocks_frame (compile_abi_encode_values_to_buf cenv dst rows)) /\
  (!rt dt buf res dop addr skip lo hi info.
     deploy_blocks_frame (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)) /\
  (!lo hi. deploy_blocks_frame (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. deploy_blocks_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  deploy_blocks_frame (compile_external_call_kwargs cenv addr vals tys abi mid rabi lo rmem static value gas skip has_default dop rt dt dinfo)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_external_call_kwargs >> simp[]
QED

Theorem deploy_blocks_frame_dynarray_append:
  (!v dst dt st. deploy_blocks_frame (compile_store_memory cenv v dst dt st)) /\
  (!src dst n sl dl imm. deploy_blocks_frame (compile_word_copy_loop src dst n sl dl imm)) /\
  (!src slot ty trans. deploy_blocks_frame (compile_store_slots cenv src slot ty trans)) ==>
  deploy_blocks_frame (compile_dynarray_append cenv arr v ws sz dt st cap prim loc)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_dynarray_append >> simp[]
QED

Theorem deploy_blocks_frame_dynarray_pop:
  (!ctor imm loc off. deploy_blocks_frame (compile_ptr_load ctor imm loc off)) /\
  (!ctor imm loc off v. deploy_blocks_frame (compile_ptr_store ctor imm loc off v)) ==>
  deploy_blocks_frame (compile_dynarray_pop arr ws sz ctor imm loc)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_dynarray_pop >> simp[]
QED

Theorem deploy_blocks_frame_stage_intcall_args:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst. deploy_blocks_frame (compile_store_bytestring v dst)) /\
  (!v dst dt st. deploy_blocks_frame (compile_store_memory cenv v dst dt st)) ==>
  !vs flags tys.
    (!e. MEM e vs ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_stage_intcall_args cfn cenv vs flags tys)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_stage_intcall_args >> simp[]
QED

Theorem deploy_blocks_frame_store_multi_results[simp]:
  !vs buf off. deploy_blocks_frame (store_multi_results buf vs off)
Proof
  apply_symbolic_frame symbolic_frame_store_multi_results >> simp[]
QED

Theorem deploy_blocks_frame_array_subscript:
  (!p. deploy_blocks_frame (loader p)) ==>
  deploy_blocks_frame (compile_array_subscript arr idx dyn cnt ws sz sg loader)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_array_subscript >> simp[]
QED

Theorem deploy_blocks_frame_tuple_subscript[simp]:
  deploy_blocks_frame (compile_tuple_subscript arr off)
Proof
  apply_symbolic_frame symbolic_frame_tuple_subscript >> simp[]
QED

Theorem deploy_blocks_frame_store_byte_chunks[simp]:
  !p bs off. deploy_blocks_frame (compile_store_byte_chunks p bs off)
Proof
  apply_symbolic_frame symbolic_frame_store_byte_chunks >> simp[]
QED

Theorem deploy_blocks_frame_bytelike_literal[simp]:
  deploy_blocks_frame (compile_bytelike_literal bs maxlen)
Proof
  apply_symbolic_frame symbolic_frame_bytelike_literal >> simp[]
QED

Theorem deploy_blocks_frame_literal_vv[simp]:
  deploy_blocks_frame (compile_literal_vv ty lit)
Proof
  apply_symbolic_frame symbolic_frame_literal_vv >> simp[]
QED

Theorem deploy_blocks_frame_name_vv[simp]:
  deploy_blocks_frame (compile_name_vv cenv ty id)
Proof
  apply_symbolic_frame symbolic_frame_name_vv >> simp[]
QED

Theorem deploy_blocks_frame_env_var[simp]:
  deploy_blocks_frame (compile_env_var item)
Proof
  apply_symbolic_frame symbolic_frame_env_var >> simp[]
QED

Theorem deploy_blocks_frame_load_bytestring_as_word[simp]:
  deploy_blocks_frame (load_bytestring_as_word v opc)
Proof
  apply_symbolic_frame symbolic_frame_load_bytestring_as_word >> simp[]
QED

Theorem deploy_blocks_frame_int_clamp[simp]:
  deploy_blocks_frame (compile_int_clamp sg bits v)
Proof
  apply_symbolic_frame symbolic_frame_int_clamp >> simp[]
QED

Theorem deploy_blocks_frame_type_convert[simp]:
  deploy_blocks_frame (compile_type_convert v conv)
Proof
  apply_symbolic_frame symbolic_frame_type_convert >> simp[]
QED

Theorem deploy_blocks_frame_bytestring_widen_copy:
  (!dst src sz. deploy_blocks_frame (compile_copy_memory dst src sz)) ==>
  deploy_blocks_frame (compile_bytestring_widen_copy dstsz v srcsz)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_bytestring_widen_copy >> simp[]
QED

Theorem deploy_blocks_frame_neg[simp]:
  deploy_blocks_frame (compile_neg v ty)
Proof
  apply_symbolic_frame symbolic_frame_neg >> simp[]
QED

Theorem deploy_blocks_frame_lower_value:
  deploy_blocks_frame (cfn cenv ty e) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (lower_value cfn cenv ty e)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_lower_value >> simp[]
QED

Theorem deploy_blocks_frame_lower_value_with_loc:
  deploy_blocks_frame (cfn cenv ty e) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (lower_value_with_loc cfn cenv ty e)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_lower_value_with_loc)
QED

Theorem deploy_blocks_frame_as_stack_val:
  deploy_blocks_frame m ==>
  deploy_blocks_frame (\st. as_stack_val ty (m st))
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_as_stack_val)
QED

Theorem deploy_blocks_frame_as_ptr_val:
  deploy_blocks_frame m ==>
  deploy_blocks_frame (\st. as_ptr_val ty loc (m st))
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_as_ptr_val)
QED

Theorem deploy_blocks_frame_multi_exprs:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  !es. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_multi_exprs cfn cenv es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_multi_exprs >> simp[]
QED

Theorem deploy_blocks_frame_make_tuple:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  !es tys buf off.
    (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_make_tuple cfn cenv es tys buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_make_tuple >> simp[]
QED

Theorem deploy_blocks_frame_make_array_elems:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  !es et sz lw buf idx.
    (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_make_array_elems cfn cenv es et sz lw buf idx)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_make_array_elems >> simp[]
QED

Theorem deploy_blocks_frame_make_array:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) /\
  (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_make_array cfn cenv es et sz lw buf)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_make_array >> simp[]
QED

Theorem deploy_blocks_frame_concat:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  !es dp infos off.
    (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_concat cfn cenv es dp infos off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_concat >> simp[]
QED

Theorem deploy_blocks_frame_store_abi_tuple:
  (!dst src n. deploy_blocks_frame (compile_copy_memory dst src n)) ==>
  !vs buf off. deploy_blocks_frame (compile_store_abi_tuple cenv buf off vs)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_store_abi_tuple >> simp[]
QED

Theorem deploy_blocks_frame_materialize_vv:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  deploy_blocks_frame (compile_materialize_vv cenv ty vv)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_materialize_vv >> simp[]
QED

Theorem deploy_blocks_frame_ifexp_arm:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  deploy_blocks_frame (compile_ifexp_arm cenv rt at vv)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_ifexp_arm >> simp[]
QED

Theorem deploy_blocks_frame_snapshot_vv:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) ==>
  deploy_blocks_frame (compile_snapshot_vv cenv copy vv)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_snapshot_vv >> simp[]
QED

Theorem deploy_blocks_frame_struct_lit:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. deploy_blocks_frame (compile_store_memory cenv v dst ty sty)) ==>
  !fields ty buf off.
    (!nm e. MEM (nm,e) fields ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
    deploy_blocks_frame (compile_struct_lit cfn cenv ty fields buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_struct_lit >> simp[]
QED

Theorem deploy_blocks_frame_abi_encode_args:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) ==>
  !es. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_abi_encode_args cfn cenv es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_abi_encode_args >> simp[]
QED

Theorem deploy_blocks_frame_ext_call_kwarg:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) /\
  (!ty. deploy_blocks_frame (cfn cenv ty e)) ==>
  deploy_blocks_frame (compile_ext_call_kwarg cfn cenv rt k e)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_ext_call_kwarg >> simp[]
QED

Theorem deploy_blocks_frame_ext_call_kwargs:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!ty vv. deploy_blocks_frame (compile_materialize_vv cenv ty vv)) ==>
  !es ks rt.
    (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_ext_call_kwargs cfn cenv rt ks es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_ext_call_kwargs >> simp[]
QED

Theorem deploy_blocks_frame_create_salt:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!e. opt = SOME e ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_create_salt cfn cenv opt)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_salt >> simp[]
QED

Theorem deploy_blocks_frame_store_words[simp]:
  !vs buf off. deploy_blocks_frame (compile_store_words buf vs off)
Proof
  apply_symbolic_frame symbolic_frame_store_words >> simp[]
QED

Theorem deploy_blocks_frame_invert[simp]:
  deploy_blocks_frame (compile_invert v ty cenv)
Proof
  apply_symbolic_frame symbolic_frame_invert >> simp[]
QED

Theorem deploy_blocks_frame_attribute:
  deploy_blocks_frame (cfn cenv ty base_e) ==>
  deploy_blocks_frame (compile_attribute cfn cenv rt ty base_e fld)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_attribute >> simp[]
QED

Theorem deploy_blocks_frame_extcall_store_args:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v dst. deploy_blocks_frame (compile_store_bytestring v dst)) ==>
  !es tys buf off.
    (!e ty. MEM e es ==> deploy_blocks_frame (cfn cenv ty e)) ==>
    deploy_blocks_frame (compile_extcall_store_args cfn cenv es tys buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_extcall_store_args >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_acc >> simp[]
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
  strip_tac >>
  apply_symbolic_frame symbolic_frame_ext_call_args >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_get_target_ptr >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_subscript >> simp[]
QED

Theorem deploy_blocks_frame_create_ctor_tuple:
  (!vs p off. deploy_blocks_frame (compile_extcall_store_values cenv vs p off)) /\
  (!copy vv. deploy_blocks_frame (compile_snapshot_vv cenv copy vv)) /\
  (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_create_ctor_tuple cfn cenv es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_ctor_tuple >> simp[]
QED

Theorem deploy_blocks_frame_create_blueprint_args:
  (!copy vv. deploy_blocks_frame (compile_snapshot_vv cenv copy vv)) /\
  (!p s enc. deploy_blocks_frame (compile_abi_encode_to_buf p s enc)) /\
  deploy_blocks_frame (compile_create_ctor_tuple cfn cenv es) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_create_blueprint_args cfn cenv raw later_es es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_blueprint_args >> simp[]
QED

Theorem deploy_blocks_frame_create_snapshot:
  (!p d n loc. deploy_blocks_frame (compile_slot_to_memory p d n loc)) /\
  (!b a p d n off. deploy_blocks_frame (compile_imm_copy_to_memory b a p d n off)) /\
  (!d s n. deploy_blocks_frame (compile_copy_memory_dynamic d s n)) ==>
  deploy_blocks_frame (compile_create_snapshot cenv vv ty)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_snapshot >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_raw_create >> simp[]
QED

Theorem deploy_blocks_frame_create_call:
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v. deploy_blocks_frame (compile_create_proxy_buf v)) /\
  (!p n v s b. deploy_blocks_frame (compile_create_dispatch p n v s b)) /\
  (!v w s b. deploy_blocks_frame (compile_create_copy v w s b)) /\
  (!is_lit v off. deploy_blocks_frame (compile_create_blueprint_check is_lit v off)) /\
  (!v w s off n p len b.
     deploy_blocks_frame (compile_create_blueprint_append v w s off n p len b)) /\
  (!es raw later_es. (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
     deploy_blocks_frame (compile_create_blueprint_args cfn cenv raw later_es es)) /\
  (!bytecode value es salt b.
     deploy_blocks_frame (cfn cenv (expr_type bytecode) bytecode) /\
     deploy_blocks_frame (cfn cenv (expr_type value) value) /\
     (!e. MEM e es ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) /\
     (!e. salt = SOME e ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
     deploy_blocks_frame (compile_raw_create cfn cenv bytecode value es salt b)) /\
  (!e. MEM e args ==> deploy_blocks_frame (cfn cenv (expr_type e) e)) ==>
  deploy_blocks_frame (compile_create_call cfn cenv ck has_salt rof args)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_call >> simp[]
QED

Theorem deploy_blocks_frame_call_internal:
  (!opc ops n. deploy_blocks_frame (emit_multi_op opc ops n)) /\
  (!stack tys. deploy_blocks_frame (compile_stage_intcall_args cfn cenv args stack tys)) /\
  (!stack tys. deploy_blocks_frame (compile_stage_intcall_args cfn
    (cenv_without_defaults cenv (nsid_to_string id))
    (omitted_defaults cenv (nsid_to_string id) (LENGTH args)) stack tys)) /\
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
  (!a vs ts az mid rz mn rb sc v g sk hd d rt dt di.
    deploy_blocks_frame (compile_external_call_kwargs cenv a vs ts az mid rz mn rb
      sc v g sk hd d rt dt di)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty (ExtCall sc sk sig opts) args dr)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_call_external >> simp[]
QED

Theorem deploy_blocks_frame_call_send:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty (Send gas) args dr)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_call_send >> simp[]
QED

Theorem deploy_blocks_frame_call_raw_revert:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v. deploy_blocks_frame (compile_raw_revert v)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty RawRevert args dr)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_call_raw_revert >> simp[]
QED

Theorem deploy_blocks_frame_call_selfdestruct:
  (!e ty. MEM e args ==> deploy_blocks_frame (cfn cenv ty e)) /\
  (!vv. deploy_blocks_frame (unwrap_value cenv vv)) /\
  (!v. deploy_blocks_frame (compile_selfdestruct v)) ==>
  deploy_blocks_frame (compile_call cfn cenv rt ty SelfDestructTarget args dr)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_call_selfdestruct >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_call_raw >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_call_raw_calldata >> simp[]
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
  (!id stack tys. target = IntCall id ==>
    deploy_blocks_frame (compile_stage_intcall_args cfn
      (cenv_without_defaults cenv (nsid_to_string id))
      (omitted_defaults cenv (nsid_to_string id) (LENGTH args)) stack tys)) /\
  (!a vs ts az mid rz mn rb sc v g sk hd d rt dt di.
    deploy_blocks_frame (compile_external_call_kwargs cenv a vs ts az mid rz mn rb
      sc v g sk hd d rt dt di)) /\
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
