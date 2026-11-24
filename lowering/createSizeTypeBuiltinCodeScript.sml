(* Static branch destinations of the type-builtin dispatcher. *)
Theory createSizeTypeBuiltinCode
Ancestors
  exprValueWrapperStateProps createSizeCutCode createSizeCutOpens exprLowering exprCallBounds builtinAbi builtinBytes
  builtinSimple context emitHelper compileEnv vyperAST pair list option

val _ = augment_srw_ss [rewrites [dalloca_windows_state_wrappers]];

(* Discharge the straight-line templates without unfolding a compiler state. *)
fun type_cut_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_DEF, create_cut_code_emit_inst,
                  create_cut_code_emit_op, create_cut_code_emit_void,
                  create_cut_targets_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              irule create_cut_code_pair, conj_tac, IF_CASES_TAC]);

val _ = augment_srw_ss [rewrites [create_alloc_buffer_cut_code, create_cut_copy_memory]];

Theorem type_cut_widen[local,simp]:
  create_cut_code exits a (SND (compile_bytestring_widen_copy n v m a))
Proof
  type_cut_steps [compile_bytestring_widen_copy_def]
QED

Theorem type_cut_zero_words[local,simp]:
  !n a. create_cut_code exits a (SND (compile_zero_words buf n a))
Proof
  Induct >> gen_tac >> type_cut_steps [compile_zero_words_def]
QED

Theorem type_cut_empty_complex[local,simp]:
  create_cut_code exits a (SND (compile_builtin_empty_complex n b a))
Proof
  type_cut_steps [compile_builtin_empty_complex_def, comp_return_def]
QED

Theorem type_cut_int_clamp[local,simp]:
  create_cut_code exits a (SND (compile_int_clamp b n v a))
Proof
  type_cut_steps [compile_int_clamp_def]
QED

Theorem type_cut_bytestring_as_word[local,simp]:
  (opc = SHR \/ opc = SAR) ==>
  create_cut_code exits a (SND (load_bytestring_as_word v opc a))
Proof
  strip_tac >> gvs[] >> type_cut_steps [load_bytestring_as_word_def]
QED

Theorem type_cut_type_convert[local,simp]:
  create_cut_code exits a (SND (compile_type_convert v op a))
Proof
  Cases_on `op` >> type_cut_steps [compile_type_convert_def, UNCURRY_VAR]
QED

Theorem compile_type_convert_cut_code:
  create_cut_code exits a (SND (compile_type_convert v op a))
Proof
  simp[type_cut_type_convert]
QED

Theorem type_cut_clamp_return[local,simp]:
  create_cut_code exits a (SND (clamp_and_return v ty a))
Proof
  type_cut_steps [clamp_and_return_def, compile_clamp_def, UNCURRY_VAR]
QED

Theorem type_cut_clamp_basetype[local,simp]:
  create_cut_code exits a (SND (compile_clamp_basetype v ty a))
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_clamp_basetype_def] >>
  TRY (rename1 `BytesT b` >> Cases_on `b`) >>
  type_cut_steps [compile_clamp_basetype_def]
QED

Theorem type_cut_bytestring_src[local,simp]:
  create_cut_code exits a (SND (compile_bytestring_src v a))
Proof
  type_cut_steps [compile_bytestring_src_def]
QED

Theorem type_cut_extract32[local,simp]:
  create_cut_code exits a (SND (compile_extract32_load len src off a))
Proof
  type_cut_steps [compile_extract32_load_def, compile_assert_slice_bounds_def]
QED

Theorem type_cut_encode[local]:
  (!dst a. create_cut_code {} a (SND (encode dst a))) ==>
  create_cut_code {} a (SND (lower_abi_encode mid n encode a))
Proof
  strip_tac >> Cases_on `mid` >>
  type_cut_steps [lower_abi_encode_def, comp_return_def]
QED

Theorem type_cut_decode[local]:
  (!dst off src len info a. create_cut_code {} a
      (SND (compile_abi_decode_to_buf dst off MLOAD src len info a))) ==>
  create_cut_code {} a (SND (lower_abi_decode data_op info mn mx n a))
Proof
  strip_tac >> type_cut_steps [lower_abi_decode_def, comp_return_def]
QED

(* The child premise applies only below the production dispatcher bound.
   Staging, payload encoding and memory decoding have separate certificates. *)
Theorem create_type_builtin_body_cut_code:
  (!ty e a. expr_size e + cenv_defaults_size cenv <
              list_size expr_size args + cenv_defaults_size cenv ==>
            create_cut_code {} a (SND (cfn cenv ty e a))) /\
  (!vv a. create_cut_code {} a (SND (unwrap_value cenv vv a))) /\
  (!a. create_cut_code {} a
      (SND (compile_ext_call_args
         (expr_child_callback (list_size expr_size args + cenv_defaults_size cenv) cfn)
         cenv [] (MAP (lowered_value_type cenv) args) args a))) /\
  (!single vals tys dst a. create_cut_code {} a
      (SND (compile_abi_encode_payload cenv single vals tys dst a))) /\
  (!dst off src len info a. create_cut_code {} a
      (SND (compile_abi_decode_to_buf dst off MLOAD src len info a))) ==>
  create_cut_code {} a
    (SND (compile_type_builtin_dispatch_body
       (expr_child_callback (list_size expr_size args + cenv_defaults_size cenv) cfn)
       cenv vv_ty ty tb ret_ty args a))
Proof
  strip_tac >>
  drule create_cut_guarded_expr >> strip_tac >>
  drule_all create_cut_lower_value >> strip_tac >>
  qabbrev_tac `bound = list_size expr_size args + cenv_defaults_size cenv` >>
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, Excl "expr_child_callback_def"] >>
  rpt (FIRST [CHANGED_TAC (simp[LET_DEF, compile_abi_encode_args_def,
                               Excl "expr_child_callback_def"]),
              irule create_cut_code_pair, irule type_cut_encode, irule type_cut_decode,
              conj_tac, gen_tac, IF_CASES_TAC,
              CONV_TAC (RAND_CONV (RAND_CONV (FIRST_CONV
                [REWR_CONV UNCURRY_VAR, RATOR_CONV (REWR_CONV UNCURRY_VAR)])))]) >>
  Cases_on `ret_ty` >> simp[]
QED
