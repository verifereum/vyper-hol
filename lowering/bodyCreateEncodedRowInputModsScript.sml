(* Select the constructor operand and ABI member at the same reached row
   index. The saved observation is not the entry of the encoder step. *)
Theory bodyCreateEncodedRowInputMods
Ancestors
  bodyAbiEncodePackedPostMods abiEncodeValuesMetadata abiDecoderMembers
  vyperABIRoundtrip exprLoweringProps vyperTyping contractABI list arithmetic

Theorem create_encoded_row_input_mods:
  LENGTH args = LENGTH vals /\
  (!j. j < LENGTH args ==>
    ?si sm ss vv copy tv.
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL j args)) = SOME tv /\
      value_has_type tv (EL j vs) /\
      type_memory_bytes ce (lowered_value_type ce (EL j args)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\
      (!l. vv_operand (EL j vals) <> Label l) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        abi_encode_saved_row_mods lo ce cx sa se (EL j args) (EL j vals)
          (EL j vs) si sm ss vv copy H ee G tn s)) /\
  vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
  bytes = contractABI$enc (contractABI$Tuple ats) (contractABI$ListV avs) /\
  LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
  LENGTH prefix + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) <= capacity /\
  rows = ZIP (vals,MAP (lowered_value_type ce) args) /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  i < LENGTH rows /\ hl = head_lengths ats 0 /\
  h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  at = EL i ats /\ av = EL i avs ==>
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  hl <= off /\ h + abi_member_head_size at <= hl /\
  off <= capacity - LENGTH prefix /\
  (is_dynamic at ==> off + LENGTH (contractABI$enc at av) <= capacity - LENGTH prefix) /\
  (~is_dynamic at ==> LENGTH (contractABI$enc at av) = abi_member_head_size at) /\
  ?e saved ty v si sm ss vv copy tv.
    e = EL i args /\ saved = EL i vals /\ v = EL i vs /\
    ty = lowered_value_type ce e /\ EL i rows = (saved,ty) /\
    at = vyper_to_abi_type (get_tenv cx) ty /\
    vyper_to_abi (get_tenv cx) ty v = SOME av /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
    (!l. vv_operand saved <> Label l) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      abi_encode_saved_row_mods lo ce cx sa se e saved v si sm ss vv copy H ee G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH rows = LENGTH args` by simp[LENGTH_ZIP] >>
  `LENGTH rows = LENGTH ats /\ LENGTH ats = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  drule_then strip_assume_tac vyper_to_abi_list_EL >>
  `i < LENGTH args /\ i < LENGTH ats /\ i < LENGTH vals /\ i < LENGTH vs` by
    (fs[LENGTH_MAP] >> decide_tac) >>
  `LENGTH bytes = LENGTH (contractABI$enc (contractABI$Tuple ats) (contractABI$ListV avs))` by simp[] >>
  drule_all_then strip_assume_tac
    (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
      abi_encode_values_index_bounds) >>
  `off <= capacity - LENGTH prefix` by decide_tac >>
  `(is_dynamic at ==> off + LENGTH (contractABI$enc at av) <= capacity - LENGTH prefix)` by
    (strip_tac >> qpat_assum `is_dynamic at ==> _ <= LENGTH bytes` (drule_then assume_tac) >> decide_tac) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!j. j < LENGTH args ==> ?si sm ss vv copy tv. _`
    (qspec_then `i` (drule_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`,`tv`] strip_assume_tac))) >>
  qexistsl [`EL i args`,`EL i vals`,`lowered_value_type ce (EL i args)`,`EL i vs`,
            `si`,`sm`,`ss`,`vv`,`copy`,`tv`] >>
  simp[EL_ZIP,EL_MAP,vyper_to_abi_types_MAP] >>
  `EL i (MAP (lowered_value_type ce) args) = lowered_value_type ce (EL i args)` by
    (irule listTheory.EL_MAP >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!i. i < LENGTH vs ==> vyper_to_abi _ _ _ = _`
    (qspec_then `i` (drule_then mp_tac)) >>
  asm_rewrite_tac[]
QED
