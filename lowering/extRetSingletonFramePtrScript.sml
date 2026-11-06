Theory extRetSingletonFramePtr
Ancestors
  extRetSingletonStmtPtr extRetLoweredBytesFramePtr extRetSingletonCapacityPtr
  extRetSingletonWordCapacityPtr returnMetadataPtr abiEncoderProps vyperTypeABI
  vyperABI contractABI vyperTyping vyperTypeSystem vyperAST compileEnv
  vyperValue valueEncoding valueTypingMemoryProps vyperTypeCallGraph abiBytesExecution

Theorem typed_string_return_source:
  IS_SOME (type_stmt env (BaseT (StringT n)) (Return (SOME e))) ==>
  well_typed_expr env e /\ ?k. expr_type e = BaseT (StringT k) /\ k <= n
Proof
  simp[typedCopyPtrTheory.type_stmt_return_some_iff] >> strip_tac >> simp[] >>
  qpat_x_assum `type_widens_to _ _ _` mp_tac >>
  simp[type_widens_to_def] >>
  Cases_on `expr_type e` >> simp[arg_type_fits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem bytes_singleton_plan_shape:
  abi_enc_plan tenv (TupleT [BaseT (BytesT (Dynamic n))]) ei ==>
  ?cap. ei = AbiComplex [(AbiBytestring n,32,cap,T)] /\ 32+n <= cap
Proof
  simp[Once abi_enc_plan_cases] >>
  simp[is_word_type_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
       is_dynamic_def] >>
  simp[Once abi_enc_plan_cases] >>
  simp[Once abi_enc_plan_cases] >>
  simp[Once abi_enc_plan_cases] >>
  simp[is_word_type_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
       is_dynamic_def, evaluate_type_def,
       type_memory_size_def] >>
  simp[word_size_capacity]
QED

Theorem string_singleton_plan_shape:
  abi_enc_plan tenv (TupleT [BaseT (StringT n)]) ei ==>
  ?cap. ei = AbiComplex [(AbiBytestring n,32,cap,T)] /\ 32+n <= cap
Proof
  simp[Once abi_enc_plan_cases] >>
  simp[is_word_type_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
       is_dynamic_def] >>
  simp[Once abi_enc_plan_cases] >>
  simp[Once abi_enc_plan_cases] >>
  simp[Once abi_enc_plan_cases] >>
  simp[is_word_type_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
       is_dynamic_def, evaluate_type_def, type_memory_size_def] >>
  simp[word_size_capacity]
QED

val _ = Parse.hide "body";

Theorem external_frame_bytes_singleton_plan:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (BytesT (Dynamic n)),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  well_formed_type (type_env tops) (BaseT (BytesT (Dynamic n))) ==>
  ?cap. next.ce_ret_enc_info = AbiComplex [(AbiBytestring n,32,cap,T)] /\
        32+n <= cap
Proof
  strip_tac >> drule external_frame_ret_abi_plan >>
  simp[assignable_type_def, needs_external_call_wrap_def,
       vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def] >>
  disch_then drule_all >> strip_tac >>
  drule bytes_singleton_plan_shape >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem external_frame_string_singleton_plan:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (StringT n),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  well_formed_type (type_env tops) (BaseT (StringT n)) ==>
  ?cap. next.ce_ret_enc_info = AbiComplex [(AbiBytestring n,32,cap,T)] /\
        32+n <= cap
Proof
  strip_tac >> drule external_frame_ret_abi_plan >>
  simp[assignable_type_def, needs_external_call_wrap_def,
       vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def] >>
  disch_then drule_all >> strip_tac >>
  drule string_singleton_plan_shape >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem typed_bytes_return_source:
  IS_SOME (type_stmt env (BaseT (BytesT (Dynamic n))) (Return (SOME e))) ==>
  well_typed_expr env e /\ ?k. expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= n
Proof
  simp[typedCopyPtrTheory.type_stmt_return_some_iff] >> strip_tac >> simp[] >>
  qpat_x_assum `type_widens_to _ _ _` mp_tac >>
  simp[type_widens_to_def] >>
  Cases_on `expr_type e` >> simp[arg_type_fits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem external_return_singleton_bytes_frame_stmt_frag_ptr:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (BytesT (Dynamic n)),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  well_formed_type (type_env tops) (BaseT (BytesT (Dynamic n))) /\
  next.ce_return_pc = NONE /\ ~next.ce_raw_return /\
  next.ce_nonreentrant = (F,nkey,ut',iv) /\ next.ce_is_external /\
  stmt_exprs_ok next (Return (SOME e)) /\
  expr_sim_inv next cx env es /\
  IS_SOME (type_stmt env (BaseT (BytesT (Dynamic n))) (Return (SOME e))) /\
  is_bytestring_type (lowered_value_type next e) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_ptr d ctx PG func next cx (BaseT (BytesT (Dynamic n))) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) next
    (stmt_env next lctx (BaseT (BytesT (Dynamic n))) (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> drule_all external_frame_bytes_singleton_plan >> strip_tac >>
  `assignable_type (type_env tops) (BaseT (BytesT (Dynamic n)))` by
    simp[assignable_type_def] >>
  drule_all external_frame_bytes_return_capacity >> strip_tac >>
  drule_all frame_valued_return_capacity_word_bound >> strip_tac >>
  drule typed_bytes_return_source >> strip_tac >>
  irule external_return_singleton_bytes_stmt_frag_ptr >> simp[arithmeticTheory.ADD_COMM, abi_bytes_ceil32_eq] >>
  conj_tac >- (fs[int_calls_stmt_def, int_calls_expr_def] >> decide_tac) >>
  qexists_tac `env` >> simp[]
QED

Theorem external_return_singleton_string_frame_stmt_frag_ptr:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (StringT n),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  well_formed_type (type_env tops) (BaseT (StringT n)) /\
  next.ce_return_pc = NONE /\ ~next.ce_raw_return /\
  next.ce_nonreentrant = (F,nkey,ut',iv) /\ next.ce_is_external /\
  stmt_exprs_ok next (Return (SOME e)) /\
  expr_sim_inv next cx env es /\
  IS_SOME (type_stmt env (BaseT (StringT n)) (Return (SOME e))) /\
  is_bytestring_type (lowered_value_type next e) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_ptr d ctx PG func next cx (BaseT (StringT n)) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) next
    (stmt_env next lctx (BaseT (StringT n)) (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> drule_all external_frame_string_singleton_plan >> strip_tac >>
  `assignable_type (type_env tops) (BaseT (StringT n))` by
    simp[assignable_type_def] >>
  drule_all external_frame_string_return_capacity >> strip_tac >>
  drule_all frame_valued_return_capacity_word_bound >> strip_tac >>
  drule typed_string_return_source >> strip_tac >>
  irule external_return_singleton_string_stmt_frag_ptr >> simp[arithmeticTheory.ADD_COMM, abi_bytes_ceil32_eq] >>
  conj_tac >- (fs[int_calls_stmt_def, int_calls_expr_def] >> decide_tac) >>
  qexists_tac `env` >> simp[]
QED
