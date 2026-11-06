(* Checked source-facing interfaces for actual-footprint tuple staging. *)
Theory exprSimAbiEncodeTupleProducer
Ancestors
  exprSimAbiEncodeTupleOpen abiEncodeInputSupplier abiTupleEncodeOpenAssembly
  abiTupleEncodeOpenStatic abiEncodeArgsSim abiTupleEncodeOpenInput
  abiTupleEncodeOpenMemory abiEncoderSourceAggregate arithmetic list

Theorem abi_encode_tuple_open_input_interface:
  abi_tuple_open_input sf ce ty at av op next lo hi s <=>
  abi_tuple_encode_open_input sf ce ty at av op next lo hi s
Proof
  Cases_on `is_word_type ty` >>
  simp[abi_tuple_open_input_def, abi_tuple_encode_open_input_def] >>
  metis_tac[ADD_COMM]
QED

Theorem abi_encode_tuple_open_memory_interface:
  !xs ats avs d mem.
  abi_tuple_open_memory sf ce xs ats avs d mem <=>
  abi_tuple_encode_open_memory sf ce xs ats avs d mem
Proof
  Induct >- simp[abi_tuple_open_memory_def, abi_tuple_encode_open_memory_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_open_memory_def, abi_tuple_encode_open_memory_def]
QED

Theorem abi_encode_tuple_dynamic_consumer:
  abi_tuple_open_memory sf ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\ any_dynamic ats ==>
  abi_encoder_open_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
    (Tuple ats) (ListV avs) d (abi_tuple_bytes ce xs) mem
Proof
  pure_rewrite_tac[abi_encode_tuple_open_memory_interface] >>
  metis_tac[abi_tuple_encode_open_dynamic_input]
QED

Theorem abi_encode_tuple_static_consumer:
  abi_tuple_open_memory sf ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\ ~any_dynamic ats /\
  abi_tuple_bytes ce xs MOD 32 = 0 ==>
  ?ct rv. has_type ct rv /\ ~is_dynamic ct /\
    static_length ct = abi_tuple_bytes ce xs /\
    enc ct rv = enc (Tuple ats) (ListV avs) /\
    abi_encoder_open_input (AbiCopy (abi_tuple_bytes ce xs)) ct rv d
      (abi_tuple_bytes ce xs) mem
Proof
  pure_rewrite_tac[abi_encode_tuple_open_memory_interface] >>
  metis_tac[abi_tuple_encode_open_static_representative]
QED

Theorem abi_encode_tuple_source_encoding:
  LENGTH ts = LENGTH cts /\ LENGTH ts = LENGTH avs /\ LENGTH avs = LENGTH rvs /\
  (!i. i < LENGTH ts ==>
    source_rep env (EL i ts) (EL i infos) (EL i cts) /\
    (?tv. evaluate_type env (EL i ts) = SOME tv) /\
    enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type env (EL i ts)) (EL i avs)) ==>
  enc (Tuple cts) (ListV rvs) =
    enc (Tuple (MAP (vyper_to_abi_type env) ts)) (ListV avs)
Proof
  strip_tac >> irule abi_encoder_tuple_encoding_cong >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH ts ==> _` (qspec_then `i` strip_assume_tac) >>
  gvs[] >> drule_all source_rep_metadata >> simp[EL_MAP]
QED

Theorem abi_encode_args_nonword_supplier_probe:
  abi_args_post ctx func ce cx es sa sb s0 es' [e] [op] [v] s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  abi_enc_plan (get_tenv cx) (expr_type e) (type_to_abi_enc_info sf ce (expr_type e)) /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\
  abi_decoder_operand_live next op /\
  (!w. eval_operand op s = SOME w ==>
    w2n w + val_footprint tv v <= lo \/ hi <= w2n w) /\
  abi_embedded_static_size ce.ce_struct_fields (expr_type e) =
    abi_member_head_size (vyper_to_abi_type (get_tenv cx) (expr_type e)) /\
  is_abi_dynamic ce.ce_struct_fields (expr_type e) =
    is_dynamic (vyper_to_abi_type (get_tenv cx) (expr_type e)) ==>
  ?ct rv. source_rep (get_tenv cx) (expr_type e)
      (type_to_abi_enc_info sf ce (expr_type e)) ct /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    abi_tuple_open_input sf ce (expr_type e) ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,expr_type e)] [ct]
Proof
  strip_tac >> pure_rewrite_tac[abi_encode_tuple_open_input_interface] >>
  irule abi_encode_nonword_input_supplier >> simp[] >>
  gvs[abi_args_post_def] >> qexists_tac `v` >> simp[]
QED
