(* Custom-error argument typing/frame audit and evaluated-value encoder
   handoff. The store loop supplies value typing, ABI conversion and
   val_in_memory; the invariant bridge supplies layout and byte bounds.
   Encoder admissibility is independently unconditional by
   abi_encoder_translation_admissible. *)
Theory bodyCustomErrorHandoff
Ancestors
  exprSimAggregateSource bodyMemAggregateStore bodyExprPreFacts
  supportedExprTraverse exprSimHypsDefs loweringPosts abiEncoderAdmissible
  abiEncoderWindow abiEncoderSourceAggregate abiTypeBoundProps vyperABIValid
  exprLowering compileEnv contractABI valueEncodingDefs
  vyperABI vyperValue vyperTyping bodyCustomErrorSourceRep
  bodyCustomErrorWindowBounds finite_map

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

(* The argument-store loop supplies the evaluated tuple value and its actual
   memory representation.  All compiler layout and encoding bounds below
   come from the unchanged body/expression invariants. *)
Theorem custom_error_invariant_encoder_handoff:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ val_in_memory tv v p mem ==>
  ?at rv.
    abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
      at rv p (type_memory_size tv) mem /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    LENGTH (enc at rv) <= abi_size_bound ce.ce_struct_fields ty
Proof
  strip_tac >> drule_all custom_error_invariant_layout >> strip_tac >>
  `?at. source_rep (get_tenv cx) ty
     (type_to_abi_enc_info ce.ce_struct_fields ce ty) at` by
    (irule custom_error_evaluated_source_rep >> simp[] >>
     qexists_tac `get_tenv cx` >> simp[]) >>
  metis_tac[custom_error_source_rep_window_bound]
QED

Theorem custom_error_tuple_encoder_handoff:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) (TupleT (MAP SND params)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (TupleT (MAP SND params)) v = SOME av /\
  val_in_memory tv v p mem ==>
  ?at rv.
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND params)))
      at rv p (type_memory_bytes ce (TupleT (MAP SND params))) mem /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT (MAP SND params))) av /\
    LENGTH (enc at rv) <= abi_size_bound ce.ce_struct_fields (TupleT (MAP SND params))
Proof
  strip_tac >> drule_all custom_error_invariant_encoder_handoff >> strip_tac >>
  drule_all custom_error_expr_inv_memory_size >> strip_tac >> metis_tac[]
QED
