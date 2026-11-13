(* Call-specific typing adapter for the prepared return decoder. *)
Theory extcallReturnDefaultTypes
Ancestors
  extcallReturnInterface exprExtReturnDecodeMetadata exprExtReturnDecodeCoherence
  exprSimAbiDecodeMinimumLayout abiReturnSuccessSource vyperABIValid
  vyperTypeExtCallCore valueTypingMemoryProps exprSimHypsDefs vyperTypeInvariants
  vyperTypeSystem vyperTyping vyperABI vyperValue compileEnv list rich_list arithmetic
  abiDecoderLayoutBounds abiMalformedBoundedContract abiTypeBoundProps abiDecoderCoherence
  exprLowering

Theorem return_default_wrapped_types:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ty) opts) args dflt) es /\
  ty <> NoneT /\ evaluate_type (get_tenv cx) ty = SOME actual_tv /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  tv = (if needs_external_call_wrap ty then TupleTV [actual_tv] else actual_tv) ==>
  assignable_type (get_tenv cx) rt /\ abi_decode_bytes_widths (get_tenv cx) rt /\
  evaluate_type (get_tenv cx) rt = SOME tv /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields rt tv /\
  abi_static_size ce.ce_struct_fields rt =
    abi_static_length (vyper_to_abi_type (get_tenv cx) rt) /\
  type_memory_bytes ce rt = type_memory_bytes ce ty
Proof
  strip_tac >> drule extcall_return_type_bounds >> strip_tac >>
  `assignable_type (get_tenv cx) ty /\ abi_decode_bytes_widths (get_tenv cx) ty` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >> metis_tac[]) >>
  `well_formed_type (get_tenv cx) ty` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >> metis_tac[]) >>
  `type_slot_size actual_tv <= dimword (:256)` by
    metis_tac[cj 1 evaluate_type_well_formed, well_formed_type_value_slot_size] >>
  `assignable_type (get_tenv cx) rt /\ abi_decode_bytes_widths (get_tenv cx) rt /\
   evaluate_type (get_tenv cx) rt = SOME tv` by
    (Cases_on `needs_external_call_wrap ty` >>
     gvs[Once assignable_type_def, Once abi_decode_bytes_widths_def,
       Once evaluate_type_def, evaluate_types_OPT_MMAP] >>
     simp[Once well_formed_type_def, type_slot_size_def,
       Once evaluate_type_def, evaluate_types_OPT_MMAP]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `abi_decode_root_metadata ce (get_tenv cx)` by
    metis_tac[abi_decode_root_metadata_inv] >>
  `abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields rt tv` by
    metis_tac[abi_decode_root_coherent] >>
  simp[] >> conj_tac >- metis_tac[abi_decode_coherent_minimum] >>
  Cases_on `needs_external_call_wrap ty` >>
  gvs[type_memory_bytes_def]
QED

Theorem return_default_source_success:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_abi_decode_return (get_tenv cx) ty bs = INL v ==>
  value_has_type tv v /\ val_wf tv v /\
  abi_static_length (vyper_to_abi_type (get_tenv cx)
    (if needs_external_call_wrap ty then TupleT [ty] else ty)) <= LENGTH bs
Proof
  strip_tac >>
  `value_has_type tv v` by
    metis_tac[vyperTypeExtCallCoreTheory.evaluate_abi_decode_return_well_typed] >>
  simp[] >> conj_tac >- metis_tac[value_has_type_memory_wf] >>
  qpat_x_assum `evaluate_abi_decode_return _ _ _ = _` mp_tac >>
  simp[evaluate_abi_decode_return_def] >>
  Cases_on `needs_external_call_wrap ty` >> simp[] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  drule_at (Pos last) evaluate_abi_decode_returndata_capped >>
  disch_then (qspec_then `vyper_abi_size_bound (get_tenv cx)
    (if needs_external_call_wrap ty then TupleT [ty] else ty)` mp_tac) >>
  simp[LENGTH_TAKE_EQ] >> strip_tac >> decide_tac
QED

Theorem return_default_decode_bounds:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ty) opts) args dflt) es /\
  ty <> NoneT /\ evaluate_type (get_tenv cx) ty = SOME actual_tv /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  tv = (if needs_external_call_wrap ty then TupleTV [actual_tv] else actual_tv) ==>
  abi_size_bound ce.ce_struct_fields rt = vyper_abi_size_bound (get_tenv cx) rt /\
  abi_static_size ce.ce_struct_fields rt <= abi_size_bound ce.ce_struct_fields rt /\
  abi_static_size ce.ce_struct_fields rt < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields rt < dimword (:256) /\
  type_memory_size tv < dimword (:256) /\
  (~is_dynamic (vyper_to_abi_type (get_tenv cx) rt) ==>
    abi_size_bound ce.ce_struct_fields rt =
      static_length (vyper_to_abi_type (get_tenv cx) rt))
Proof
  strip_tac >> drule_all return_default_wrapped_types >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule abi_decode_root_metadata_inv >>
  simp[abi_decode_root_metadata_def] >> strip_tac >>
  `abi_sfields_consistent_upto (type_value_size tv) ce.ce_struct_fields (get_tenv cx)` by
    metis_tac[abi_sfields_consistent_upto_init] >>
  drule_all abi_props_vyper_upto >> strip_tac >>
  `abi_size_bound ce.ce_struct_fields rt < dimword (:256)` by
    metis_tac[abi_malformed_return_root_bound] >>
  `abi_static_size ce.ce_struct_fields rt <= abi_size_bound ce.ce_struct_fields rt` by
    simp[abi_static_size_le_size_bound] >>
  `type_memory_bytes ce ty = type_memory_size actual_tv` by
    metis_tac[extcall_return_memory_size] >>
  `type_memory_size actual_tv + 64 < dimword (:256)` by
    metis_tac[extcall_return_store_bound] >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >>
  strip_tac >> gvs[]
QED

Theorem return_default_primitive_minimum:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) ==>
  (case type_to_abi_dec_info sf ce rt of DecPrimWord clamp =>
     32 <= abi_static_size sf rt | _ => T)
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[needs_external_call_wrap_def, Once type_to_abi_dec_info_def] >>
  Cases_on `LENGTH l <= 1` >>
  simp[type_to_abi_dec_info_def]
QED
