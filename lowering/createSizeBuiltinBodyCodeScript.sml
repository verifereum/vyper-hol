(* Static ID and caller branch-target certificates for ordinary builtins. *)
Theory createSizeBuiltinBodyCode
Ancestors
  exprValueWrapperStateProps createSizeCutCode createSizeCutOpens createSizeBoolChainCutCode
  exprLowering exprCallBounds vyperAST context builtinStrings builtinMath
  builtinHashing builtinSimple builtinBytes builtinMisc externalEntryShape
  pair list pred_set arithmetic emitHelper compileEnv venomInst

Theorem builtin_labels_open[local]:
  added_labels a (SND (new_block l a)) = [l]
Proof
  Cases_on `new_block l a` >> simp[] >> metis_tac[added_labels_new_block]
QED

(* A template may borrow its own future block openings. The second conjunct
   records the openings still owed, independently of which paths execute. *)
Theorem builtin_cut_require[local]:
  create_cut_code pending a b /\ pending SUBSET set (added_labels a b) ==>
  create_cut_code exits a b
Proof
  strip_tac >> irule create_cut_code_close >> qexists_tac `pending` >>
  fs[SUBSET_DEF]
QED

Theorem builtin_cut_require_open[local]:
  (!x s. create_cut_code pending s (SND (k x s)) /\
    owed DELETE l SUBSET set (added_labels s (SND (k x s)))) ==>
  create_cut_code pending a (SND (comp_bind (new_block l) k a)) /\
  owed SUBSET set (added_labels a (SND (comp_bind (new_block l) k a)))
Proof
  strip_tac >> Cases_on `new_block l a` >> fs[comp_bind_def] >>
  qpat_x_assum `!x s. _ /\ _` (qspecl_then [`q`,`r`] strip_assume_tac) >>
  `create_cut_code pending a r` by metis_tac[create_cut_code_new_block, SND] >>
  conj_tac
  >- (irule create_cut_code_join >> qexists_tac `r` >> simp[]) >>
  fs[create_cut_code_def] >> drule_all added_labels_trans >>
  `added_labels a r = [l]` by metis_tac[added_labels_new_block] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem builtin_cut_targets_jnz[local]:
  create_cut_targets JNZ [cond; Label l; Label r] = [l;r]
Proof
  Cases_on `cond` >> simp[create_cut_targets_def]
QED

Theorem builtin_cut_jnz[local]:
  l IN exits /\ r IN exits ==>
  create_cut_code exits a (SND (emit_inst JNZ [cond;Label l;Label r] [] a))
Proof
  strip_tac >> irule create_cut_code_emit_inst >> simp[builtin_cut_targets_jnz] >>
  metis_tac[]
QED

val cut_prims = [builtin_cut_jnz, create_cut_code_emit_op, create_cut_code_emit_inst,
                 create_cut_code_emit_void, create_cut_code_emit_multi_op,
                 create_cut_targets_def];

(* Introduce each continuation at a fresh symbolic state. Do not unwind
   comp_bind into a nested expression for that state. *)
fun cut_chain rules =
  let val cleanup = simp (rules @ cut_prims @ [LET_THM, comp_ignore_bind_def])
  in cleanup >>
     rpt (FIRST [irule create_cut_code_bind_uniform >> conj_tac >> rpt gen_tac >> BETA_TAC,
                 COND_CASES_TAC, CASE_TAC, gen_tac] >> cleanup)
  end;

Theorem create_ptr_load_cut_code[local]:
  create_cut_code exits a (SND (compile_ptr_load ic imm loc op a))
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def, compile_imm_load_word_def] >>
  cut_chain []
QED

fun cut_debt rules =
  rpt (FIRST
    [match_mp_tac builtin_cut_require_open >> rpt gen_tac >> BETA_TAC,
     match_mp_tac create_cut_opens_bind_keep >>
       (conj_tac >- (rpt gen_tac >> cut_chain rules)) >>
       rpt gen_tac >> BETA_TAC]) >>
  conj_tac >- cut_chain rules >>
  simp[SUBSET_DEF, builtin_labels_open] >> metis_tac[];

fun cut_fresh labels =
  map_every (fn l => match_mp_tac create_cut_code_bind_uniform >>
    (conj_tac >- simp[]) >> qx_gen_tac l >> gen_tac >> BETA_TAC) labels;

Theorem builtin_uint2str_code[local]:
  create_cut_code {} a (SND (compile_uint2str v n bytes a))
Proof
  simp[compile_uint2str_def, LET_THM, comp_ignore_bind_def] >>
  ntac 8 (match_mp_tac create_cut_code_bind_uniform >>
    (conj_tac >- cut_chain [create_alloc_buffer_cut_code]) >>
    rpt gen_tac >> BETA_TAC) >>
  cut_fresh [`lchk`, `lcond`, `lbody`, `lzero`, `lfin`, `lexit`] >>
  match_mp_tac (Q.INST [`pending` |-> `{lchk;lcond;lbody;lzero;lfin;lexit}`]
    builtin_cut_require) >> cut_debt []
QED

Theorem builtin_list_membership_steps[local]:
  (!xs a. create_cut_code exits a (SND (emit_membership_eqs needle xs a))) /\
  (!xs acc a. create_cut_code exits a (SND (fold_membership_or acc xs a))) /\
  (!xs acc a. create_cut_code exits a (SND (fold_membership_and acc xs a)))
Proof
  rpt conj_tac >> Induct >>
  cut_chain [emit_membership_eqs_def, fold_membership_or_def, fold_membership_and_def]
QED

Theorem builtin_list_membership_code[local]:
  create_cut_code exits a (SND (compile_list_membership_in needle xs a)) /\
  create_cut_code exits a (SND (compile_list_membership_notin needle xs a))
Proof
  conj_tac >> cut_chain [compile_list_membership_in_def,
    compile_list_membership_notin_def, builtin_list_membership_steps]
QED

Theorem builtin_array_loop_code[local]:
  (!op a. create_cut_code {} a (SND (loader op a))) ==>
  create_cut_code {} a
    (SND (compile_array_membership_loop needle arr len esz ofs loader bnd isin a))
Proof
  strip_tac >> simp[compile_array_membership_loop_def, LET_THM, comp_ignore_bind_def] >>
  match_mp_tac create_cut_code_bind_uniform >> (conj_tac >- simp[]) >> rpt gen_tac >> BETA_TAC >>
  cut_fresh [`lentry`, `lcond`, `lbody`, `lfound`, `lincr`, `lexit`] >>
  match_mp_tac (Q.INST [`pending` |-> `{lentry;lcond;lbody;lfound;lincr;lexit}`]
    builtin_cut_require) >> cut_debt [create_cut_code_widen_empty]
QED

Theorem builtin_var_array_code[local]:
  create_cut_code {} a (SND (compile_var_array_membership cenv needle arr ty isin a))
Proof
  Cases_on `ty` >>
  cut_chain [compile_var_array_membership_def, builtin_array_loop_code,
             create_ptr_load_cut_code]
QED

Theorem builtin_binop_code[local]:
  create_cut_code exits a (SND (compile_binop bop x y ty bl el a))
Proof
  Cases_on `bop` >>
  cut_chain [compile_binop_def, compile_safe_add_def, compile_safe_sub_def,
    compile_safe_mul_def, compile_safe_div_def, compile_safe_decimal_div_def,
    compile_safe_mod_def, compile_safe_pow_def, compile_mul_overflow_check_def,
    compile_compare_def, wrap_truncate_def, compile_select_def,
    clamp_and_return_def, compile_clamp_def, UNCURRY_VAR]
QED

val _ = augment_srw_ss [rewrites [dalloca_windows_state_wrappers]];

(* Pair lets sequence actions, while ordinary lets may select a type or
   compute metadata. Try the pair rule before eliminating UNCURRY. *)
fun builtin_steps rules =
  let val clean = simp (rules @ cut_prims @ [LET_DEF, comp_ignore_bind_def,
                  Excl "expr_child_callback_def"])
  in clean >>
     rpt (FIRST [irule create_cut_code_pair, irule create_cut_code_bind,
                 conj_tac, gen_tac, COND_CASES_TAC,
                 CONV_TAC (RAND_CONV (RAND_CONV (RATOR_CONV (REWR_CONV UNCURRY_VAR))))] >> clean)
     >> clean
  end;

Theorem builtin_acc_code[local]:
  (!ty e a. create_cut_code {} a (SND (lower_value f ce ty e a))) ==>
  create_cut_code {} a (SND (compile_acc f ce addr acc a))
Proof
  strip_tac >> Cases_on `acc` >> builtin_steps [compile_acc_def]
QED

Theorem builtin_literal_chunks_code[local]:
  !ptr bs ofs a. create_cut_code exits a
    (SND (compile_store_byte_chunks ptr bs ofs a))
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt strip_tac >>
  cut_chain [compile_store_byte_chunks_def] >>
  first_x_assum (qspecl_then
    [`TAKE 32 (v4::v5 ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (v4::v5 ++ REPLICATE 31 0w))`] mp_tac) >>
  simp[]
QED

Theorem create_bytelike_literal_cut_code:
  create_cut_code exits a (SND (compile_bytelike_literal bs n a))
Proof
  cut_chain [compile_bytelike_literal_def, builtin_literal_chunks_code,
    create_alloc_buffer_cut_code]
QED

Theorem builtin_literal_code[local]:
  create_cut_code exits a (SND (compile_literal_vv ty lit a))
Proof
  Cases_on `lit` >> TRY (rename1 `BoolL b` >> Cases_on `b`) >>
  simp[compile_literal_vv_def] >>
  TRY (Cases_on `ty` >> simp[]) >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  TRY (rename1 `BytesT b` >> Cases_on `b`) >>
  cut_chain [compile_literal_vv_def, create_bytelike_literal_cut_code]
QED

Theorem builtin_simple_math_code[local]:
  create_cut_code exits a (SND (compile_neg v ty a)) /\
  create_cut_code exits a (SND (compile_builtin_abs v a)) /\
  create_cut_code exits a (SND (compile_ceil v d a)) /\
  create_cut_code exits a (SND (compile_floor v d a)) /\
  create_cut_code exits a (SND (compile_as_wei_value_int v m sg a)) /\
  create_cut_code exits a (SND (compile_as_wei_value_decimal v m d a))
Proof
  rpt conj_tac >> cut_chain [compile_neg_def, compile_builtin_abs_def,
    compile_ceil_def, compile_floor_def, compile_select_def, UNCURRY_VAR,
    compile_as_wei_value_int_def, compile_as_wei_value_decimal_def]
QED

Theorem builtin_chain_prims_code[local]:
  create_cut_code exits a (SND (compile_blockhash v a)) /\
  create_cut_code exits a (SND (compile_ecrecover h vv r ss a)) /\
  create_cut_code exits a (SND (compile_ecadd_points u v a)) /\
  create_cut_code exits a (SND (compile_ecmul_point u v a))
Proof
  rpt conj_tac >> cut_chain [compile_blockhash_def, compile_ecrecover_def,
    compile_ecadd_points_def, compile_ecmul_point_def, create_alloc_buffer_cut_code]
QED

val builtin_simple_rules =
    [builtin_simple_math_code, builtin_chain_prims_code,
     compile_pow_mod256_def, compile_addmod_def, compile_mulmod_def,
     compile_blobhash_def, compile_builtin_calldatasize_def];

Theorem builtin_method_hash_code[local]:
  !ty v a. create_cut_code exits a (SND (compile_method_id_hash ty v a))
Proof
  ho_match_mp_tac compile_method_id_hash_ind >> rpt strip_tac >>
  cut_chain [compile_method_id_hash_def, compile_keccak256_bytes_def,
             compile_keccak256_bytesm_def, create_alloc_buffer_cut_code]
QED

Theorem builtin_slices_code[local]:
  create_cut_code exits a (SND (compile_slice_calldata start len n a)) /\
  create_cut_code exits a (SND (compile_slice_code start len n a)) /\
  create_cut_code exits a (SND (compile_slice_extcode addr start len n a)) /\
  create_cut_code exits a (SND (compile_slice_data sl sd start len n a)) /\
  create_cut_code exits a (SND (compile_bytestring_src v a))
Proof
  rpt conj_tac >> cut_chain [compile_slice_calldata_def, compile_slice_code_def,
    compile_slice_extcode_def, compile_slice_data_def, compile_slice_out_buf_def,
    compile_bytestring_src_def, compile_assert_slice_bounds_def,
    create_alloc_buffer_cut_code, UNCURRY_VAR]
QED

Theorem builtin_multi_code[local]:
  (!ty e a. create_cut_code {} a (SND (lower_value f ce ty e a))) ==>
  !es a. create_cut_code {} a (SND (compile_multi_exprs f ce es a))
Proof
  strip_tac >> Induct >> cut_chain [compile_multi_exprs_def]
QED

Theorem builtin_concat_code[local]:
  (!ty e a. create_cut_code {} a (SND (lower_value f ce ty e a))) ==>
  !es infos a. create_cut_code {} a (SND (compile_concat f ce es dst infos off a))
Proof
  strip_tac >> Induct >- simp[compile_concat_def] >>
  qx_gen_tac `el` >> Cases >> simp[compile_concat_def] >>
  rename1 `compile_concat _ _ _ _ (info::rest) _ _` >>
  Cases_on `info` >> cut_chain [compile_concat_def]
QED

Theorem builtin_aggregate_code[local]:
  (!ty e a. create_cut_code {} a (SND (f ce ty e a))) /\
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!src dst dt st a. create_cut_code {} a (SND (compile_store_memory ce src dst dt st a))) ==>
  (!es tys dst ofs a. create_cut_code {} a
      (SND (compile_make_tuple f ce es tys dst ofs a))) /\
  (!es et sz b dst i a. create_cut_code {} a
      (SND (compile_make_array_elems f ce es et sz b dst i a)))
Proof
  strip_tac >> conj_tac
  >- (Induct >- simp[compile_make_tuple_def] >>
      qx_gen_tac `el` >> Cases >> cut_chain [compile_make_tuple_def]) >>
  Induct >> cut_chain [compile_make_array_elems_def]
QED

Theorem create_builtin_body_cut_code:
  (!ty e a. expr_size e + cenv_defaults_size ce <
              list_size expr_size args + cenv_defaults_size ce ==>
      create_cut_code {} a (SND (f ce ty e a))) /\
  (!vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!src dst dt st a. create_cut_code {} a (SND (compile_store_memory ce src dst dt st a))) ==>
  create_cut_code {} a
    (SND (compile_builtin_dispatch_body
       (expr_child_callback (list_size expr_size args + cenv_defaults_size ce) f)
       ce ret_ty ty bi args a))
Proof
  strip_tac >> drule create_cut_guarded_expr >> strip_tac >>
  drule_all create_cut_lower_value >> strip_tac >>
  drule builtin_multi_code >> strip_tac >>
  drule builtin_concat_code >> strip_tac >>
  drule_all builtin_aggregate_code >> strip_tac >>
  qabbrev_tac `bound = list_size expr_size args + cenv_defaults_size ce` >>
  Cases_on `bi` >> simp[compile_builtin_dispatch_body_def, LET_DEF,
                        Excl "expr_child_callback_def"]
  >~ [`compile_binop _ _ _ _ _ _ _`] >- suspend "bop"
  >~ [`compile_slice_extcode _ _ _ _ _`] >- suspend "slice"
  >~ [`compile_method_id_runtime _ _ _ _`] >- suspend "method"
  >~ [`compile_make_array _ _ _ _ _ _ _ _`] >- suspend "array"
  >~ [`compile_keccak256_bytesm _ _ _`] >- suspend "keccak"
  >~ [`compile_sha256_bytesm _ _ _`] >- suspend "sha"
  >~ [`compile_builtin_len _ _ _ _ _`] >- suspend "len"
  >~ [`compile_bool_chain_ops _ _ _ _ _ _ _`] >- suspend "chain"
  >~ [`is_word_type ret_ty`] >- suspend "named"
  >> rpt (irule create_cut_code_pair >> conj_tac >>
       simp (cut_prims @ [create_alloc_buffer_cut_code, Excl "expr_child_callback_def"])) >>
  simp[builtin_uint2str_code, builtin_slices_code, builtin_acc_code,
       Excl "expr_child_callback_def"] >>
  cut_chain (builtin_simple_rules @ [UNCURRY_VAR, Excl "expr_child_callback_def"]) >>
  TRY (rename1 `compile_env_var item _` >> Cases_on `item` >>
       cut_chain [compile_env_var_def]) >>
  TRY (rename1 `compile_invert _ et _ _` >> Cases_on `et` >>
       cut_chain [compile_invert_def])
QED

Resume create_builtin_body_cut_code[len]:
  irule create_cut_code_pair >> simp[compile_builtin_len_def, create_ptr_load_cut_code,
                               Excl "expr_child_callback_def"]
QED

Resume create_builtin_body_cut_code[bop]:
  COND_CASES_TAC
  >- (irule create_cut_code_pair >> simp[Excl "expr_child_callback_def"] >>
      Cases_on `HD (TL args)` >>
      TRY (rename1 `Builtin _ bi2 elems` >> Cases_on `bi2`) >>
      simp[Excl "expr_child_callback_def"] >>
      rpt (irule create_cut_code_pair >> conj_tac >>
           simp[builtin_var_array_code, Excl "expr_child_callback_def"]) >>
      COND_CASES_TAC >> simp[builtin_list_membership_code]) >>
  COND_CASES_TAC
  >- (Cases_on `bytestring_literal_hash (HD args)` >>
      Cases_on `bytestring_literal_hash (HD (TL args))` >>
      builtin_steps [compile_bytestring_hash_def]) >>
  builtin_steps [builtin_binop_code]
QED

Resume create_builtin_body_cut_code[slice]:
  builtin_steps [builtin_slices_code, create_alloc_buffer_cut_code]
QED

Resume create_builtin_body_cut_code[method]:
  Cases_on `method_id_literal (HD args)` >>
  builtin_steps [compile_method_id_runtime_def, builtin_method_hash_code,
    create_alloc_buffer_cut_code, builtin_literal_code]
QED

Resume create_builtin_body_cut_code[array]:
  Cases_on `o'` >> builtin_steps [compile_make_array_def, create_alloc_buffer_cut_code]
QED

Theorem builtin_sha_word_code[local]:
  create_cut_code exits a (SND (compile_sha256_word v a)) /\
  create_cut_code exits a (SND (compile_sha256_bytesm v m a))
Proof
  conj_tac >> cut_chain [compile_sha256_word_def, compile_sha256_bytesm_def,
                       create_alloc_buffer_cut_code]
QED

fun builtin_hash_cases rules =
  Cases_on `expr_type (HD args)` >>
  TRY (rename1 `expr_type _ = BaseT bt` >> Cases_on `bt`) >>
  TRY (rename1 `expr_type _ = BaseT (BytesT bd)` >> Cases_on `bd`) >>
  simp[Excl "expr_child_callback_def"] >>
  irule create_cut_code_pair >> simp (rules @ [Excl "expr_child_callback_def"]);

Resume create_builtin_body_cut_code[keccak]:
  COND_CASES_TAC
  >- builtin_steps [compile_keccak256_bytes_def] >>
  builtin_hash_cases [] >>
  cut_chain [compile_keccak256_bytesm_def, compile_keccak256_word_def,
             create_alloc_buffer_cut_code, Excl "expr_child_callback_def"]
QED

Resume create_builtin_body_cut_code[sha]:
  COND_CASES_TAC
  >- builtin_steps [create_alloc_buffer_cut_code, compile_sha256_bytes_def] >>
  builtin_hash_cases [builtin_sha_word_code]
QED

Resume create_builtin_body_cut_code[named]:
  irule create_cut_code_pair >> simp[Excl "expr_child_callback_def"] >>
  COND_CASES_TAC >> simp[]
QED

Resume create_builtin_body_cut_code[chain]:
  ntac 2 (match_mp_tac create_cut_code_pair >>
    (conj_tac >- simp[]) >> BETA_TAC) >>
  Cases_on `fresh_label "bool_exit" (SND (fresh_var a))` >>
  fs[UNCURRY_VAR, Excl "expr_child_callback_def"] >>
  rename1 `SND (new_block exit_lbl _)` >>
  match_mp_tac (Q.INST [`pending` |-> `{exit_lbl}`, `opened` |-> `{exit_lbl}`]
    create_cut_opens_close) >>
  reverse conj_tac >- simp[] >>
  qmatch_goalsub_abbrev_tac `new_block exit_lbl chain_state` >>
  match_mp_tac create_cut_opens_prepend >> qexists_tac `chain_state` >>
  reverse conj_tac >- simp[create_cut_opens_block, builtin_labels_open] >>
  simp[Abbr `chain_state`, compile_bool_chain_ops_cut_code,
       Excl "expr_child_callback_def"]
QED

Finalise create_builtin_body_cut_code
