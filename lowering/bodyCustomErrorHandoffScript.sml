(* Boundary audit for the custom-error S1 argument loop.
   This is a diagnostic, not a new simulation contract.  The reusable
   interfaces are aggregate_materialised_child_{typed,wf},
   aggregate_mem_store_lowered_elem, and expr_post's pure_frame. *)
Theory bodyCustomErrorHandoff
Ancestors
  exprSimAggregateSource bodyMemAggregateStore bodyExprPreFacts
  supportedExprTraverse exprSimHypsDefs loweringPosts abiEncoderAdmissible
  abiEncoderWindow abiEncoderSourceAggregate abiTypeBoundProps vyperABIValid
  exprLowering compileEnv contractABI valueEncodingDefs
  vyperABI vyperValue vyperTyping

Theorem custom_error_argument_handoff_audit[local]:
  supported_pure_expr tops e /\ expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tvv,es') /\
  read_result cx tvv es' = (INL v,es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  expr_post ctx func ce cx e es sa sb s0 es' v op s ==>
  value_has_type tv v /\ val_wf tv v /\
  compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
    compile_store_memory ce src dst (expr_type e) (expr_type e) /\
  pure_frame ce func es sa s0 s
Proof
  strip_tac >>
  `value_has_type tv v` by
    metis_tac[aggregate_materialised_child_typed] >>
  `val_wf tv v` by metis_tac[aggregate_materialised_child_wf] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `~expr_has_effect e` by metis_tac[supported_pure_expr_effect_free] >>
  simp[] >> conj_tac
  >- (irule aggregate_mem_store_lowered_elem >> metis_tac[]) >>
  fs[expr_post_def]
QED


(* The translation's no-value leaf has an empty tuple representative even
   though abi_enc_plan intentionally excludes NoneT. *)
Theorem custom_error_none_window:
  !ce p mem.
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce NoneT)
      (Tuple []) (ListV []) p 0 mem /\
    LENGTH (enc (Tuple []) (ListV [])) <=
      abi_size_bound ce.ce_struct_fields NoneT
Proof
  simp[type_to_abi_enc_info_def, abi_encoder_window_complex_nil,
       enc_def, abi_size_bound_def, abi_static_size_def, listTheory.REV_DEF]
QED

Theorem custom_error_empty_tuple_window:
  !ce p mem.
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT []))
      (Tuple []) (ListV []) p 0 mem /\
    LENGTH (enc (Tuple []) (ListV [])) <=
      abi_size_bound ce.ce_struct_fields (TupleT [])
Proof
  simp[type_to_abi_enc_info_def, is_abi_dynamic_def, type_memory_bytes_def,
       abi_size_bound_def, enc_def, listTheory.REV_DEF] >> gen_tac >> gen_tac >>
  irule abiEncoderWindowTheory.window_copy >>
  simp[has_type_def, is_dynamic_def, static_length_def, enc_def,
       mem_bytes_at_def, listTheory.REV_DEF]
QED

Theorem custom_error_empty_struct_window:
  !ce id p mem.
    FLOOKUP ce.ce_struct_fields (nsid_to_string id) = SOME [] ==>
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (StructT id))
      (Tuple []) (ListV []) p 0 mem /\
    LENGTH (enc (Tuple []) (ListV [])) <=
      abi_size_bound ce.ce_struct_fields (StructT id)
Proof
  rpt strip_tac >>
  simp[Once type_to_abi_enc_info_def, is_abi_dynamic_def,
       Once type_memory_bytes_def, get_struct_fields_def, abi_size_bound_def, enc_def,
       listTheory.REV_DEF] >>
  irule abiEncoderWindowTheory.window_copy >>
  simp[has_type_def, is_dynamic_def, static_length_def, enc_def,
       mem_bytes_at_def, listTheory.REV_DEF]
QED

Theorem custom_error_none_source_rep:
  !env. source_rep env NoneT (AbiComplex []) (Tuple [])
Proof
  simp[source_rep_def, vyper_to_abi_type_def, evaluate_type_def,
       value_has_type_def] >>
  rpt strip_tac >> gvs[vyper_to_abi_def] >>
  qexists_tac `ListV []` >>
  simp[abiEncoderOpenInputTheory.abi_encoder_open_complex_nil]
QED
