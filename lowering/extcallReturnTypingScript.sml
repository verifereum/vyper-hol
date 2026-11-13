(* Return-decoder premises supplied by the actual external-call caller. *)
Theory extcallReturnTyping
Ancestors
  exprSimAbiDecodeEntryTyping exprSimAbiDecodeEntryMetadata
  exprSimAbiDecodeEntryCoherence exprSimAbiDecodeBuiltin
  exprSimHypsDefs vyperTypeSystem vyperAST vyperValue allocLimits
  compileEnv words arithmetic option vyperTypeABI vyperABIValid abiBoundaryChecks
  vyperABI contractABI vyperTyping

Theorem extcall_return_void_decode:
  evaluate_abi_decode_return env NoneT bs = INL NoneV
Proof
  simp[evaluate_abi_decode_return_def, needs_external_call_wrap_def,
    evaluate_abi_decode_returndata_def, vyper_abi_size_bound_def,
    vyper_is_dynamic_def, vyper_valid_enc_returndata_def,
    vyper_decode_valid_enc_def, decode_abi_value_def, abi_to_vyper_def,
    vyper_to_abi_type_def, dec_def, is_dynamic_def, static_length_def,
    abi_static_length_def, head_lengths_def, dimword_def]
QED

Theorem extcall_return_capped_decode:
  evaluate_type env ty = SOME tv /\
  abi_static_length (vyper_to_abi_type env ty) <=
    LENGTH (TAKE (vyper_abi_size_bound env ty) bs) ==>
  (evaluate_abi_decode_returndata env ty bs = INL v <=>
   vyper_decode_valid_enc (vyper_to_abi_type env ty)
     (TAKE (vyper_abi_size_bound env ty) bs) /\
   (is_dynamic (vyper_to_abi_type env ty) \/
    static_length (vyper_to_abi_type env ty) <=
      LENGTH (TAKE (vyper_abi_size_bound env ty) bs)) /\
   abi_to_vyper env ty
     (dec (vyper_to_abi_type env ty) (TAKE (vyper_abi_size_bound env ty) bs)) =
       SOME v /\ value_has_type tv v)
Proof
  strip_tac >>
  `is_dynamic (vyper_to_abi_type env ty) \/
   static_length (vyper_to_abi_type env ty) <=
     LENGTH (TAKE (vyper_abi_size_bound env ty) bs)` by
    metis_tac[abi_static_length_static] >>
  simp[evaluate_abi_decode_returndata_def, vyper_valid_enc_returndata_def,
       decode_abi_value_def, LET_THM, AllCaseEqs()] >>
  metis_tac[CONJUNCT1 abi_to_vyper_well_typed]
QED

Theorem extcall_return_unwrap_memory:
  evaluate_abi_decode_returndata env
    (if needs_external_call_wrap rt then TupleT [rt] else rt) bs = INL v /\
  value_has_type (if needs_external_call_wrap rt then TupleTV [tv] else tv) v /\
  val_in_memory (if needs_external_call_wrap rt then TupleTV [tv] else tv) v d mem ==>
  ?rv. evaluate_abi_decode_return env rt bs = INL rv /\
       value_has_type tv rv /\ val_in_memory tv rv d mem
Proof
  Cases_on `needs_external_call_wrap rt` >> simp[] >> strip_tac
  >- (Cases_on `v` >> gvs[value_has_type_inv] >>
      Cases_on `a` >> gvs[value_has_type_inv] >>
      rename1 `values_have_types [tv] vs` >>
      Cases_on `vs` >> gvs[value_has_type_def] >>
      rename1 `values_have_types [] rest` >> Cases_on `rest` >> gvs[value_has_type_def] >>
      simp[evaluate_abi_decode_return_def] >>
      fs[val_in_memory_singleton_tuple]) >>
  simp[evaluate_abi_decode_return_def] >> metis_tac[]
QED

Theorem extcall_return_decoder_types:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt) es /\
  rt <> NoneT ==>
  let wrapped = if needs_external_call_wrap rt then TupleT [rt] else rt in
  assignable_type (get_tenv cx) wrapped /\
  abi_decode_bytes_widths (get_tenv cx) wrapped /\
  ?tv. abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields wrapped tv
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `expr_sim_inv ce cx env es /\
   well_typed_expr env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt)` by
    fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by metis_tac[abi_decode_inv_type_env] >>
  `assignable_type (get_tenv cx) rt /\
   abi_decode_bytes_widths (get_tenv cx) rt` by
    fs[Once well_typed_expr_def] >>
  `assignable_type (get_tenv cx)
    (if needs_external_call_wrap rt then TupleT [rt] else rt)` by
    (irule abi_decode_wrapped_assignable >> simp[]) >>
  `abi_decode_bytes_widths (get_tenv cx)
    (if needs_external_call_wrap rt then TupleT [rt] else rt)` by
    (irule abi_decode_wrapped_widths >> simp[]) >>
  simp[] >>
  `?tv. evaluate_type (get_tenv cx)
    (if needs_external_call_wrap rt then TupleT [rt] else rt) = SOME tv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def, IS_SOME_EXISTS] >>
  qexists_tac `tv` >> irule abi_decode_root_coherent >> simp[] >>
  metis_tac[abi_decode_root_metadata_inv]
QED

Theorem extcall_return_size_bounds:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt) es ==>
  let wrapped = if needs_external_call_wrap rt then TupleT [rt] else rt in
  abi_static_size ce.ce_struct_fields wrapped <= abi_size_bound ce.ce_struct_fields wrapped /\
  abi_size_bound ce.ce_struct_fields wrapped < 2 ** 64 /\
  abi_static_size ce.ce_struct_fields wrapped < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields wrapped < dimword (:256)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `ext_call_alloc_ok ce (ExtCall stat skip (fname,ats,rt) opts) args` by
    fs[expr_body_pre_def, Once alloc_limits_expr_def] >>
  `abi_size_bound ce.ce_struct_fields
    (if needs_external_call_wrap rt then TupleT [rt] else rt) < 2 ** 64` by
    (fs[ext_call_alloc_ok_def] >>
     fs[MAX_DEF] >> decide_tac) >>
  `abi_static_size ce.ce_struct_fields
    (if needs_external_call_wrap rt then TupleT [rt] else rt) <=
   abi_size_bound ce.ce_struct_fields
    (if needs_external_call_wrap rt then TupleT [rt] else rt)` by
    MATCH_ACCEPT_TAC abi_decode_builtin_min_le_max >>
  fs[dimword_def] >> decide_tac
QED
