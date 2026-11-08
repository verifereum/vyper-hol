Theory entryReachBodyMemberInputs
Ancestors
  valueEncodingDefs entryReachBodyLayoutWindows entryReachBodySourceLayout
  abiDecoderTypedContract abiEncoderOpenInput abiCanonicalWindows
  abiDecodeRanges contractABI list rich_list arithmetic words

Theorem entry_layout_member_parts[local]:
  LIST_REL abi_encoder_layout_valid (pre ++ aty::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs ==>
  ?prefix suffix.
    enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest)) =
      prefix ++ enc aty av ++ suffix /\
    LENGTH prefix =
      (if is_dynamic aty then head_lengths (pre ++ aty::post) 0 +
         SUM (MAP2 abi_member_tail_size pre pvs)
       else SUM (MAP abi_member_head_size pre))
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid pre pvs /\
   LIST_REL abi_encoder_layout_valid post rest` by
    metis_tac[LIST_REL_APPEND_EQ, LIST_REL_def] >>
  drule canonical_member_parts >> simp_tac bool_ss [LET_THM] >>
  disch_then kall_tac >> Cases_on `is_dynamic aty`
  >- (qexistsl_tac
       [`FLAT (abi_tuple_heads (head_lengths (pre ++ aty::post) 0) 0 pre pvs) ++
         enc_number (Uint 256)
           (NumV (head_lengths (pre ++ aty::post) 0 +
                  SUM (MAP2 abi_member_tail_size pre pvs))) ++
         FLAT (abi_tuple_heads (head_lengths (pre ++ aty::post) 0)
           (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size aty av)
           post rest) ++ FLAT (abi_tuple_tails pre pvs)`,
        `FLAT (abi_tuple_tails post rest)`] >>
      simp[APPEND_ASSOC, abi_encoder_open_heads_length, abi_tuple_tails_length,
           head_lengths_acc, MAP_APPEND, SUM_APPEND, abi_member_head_size_def] >>
      decide_tac) >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ aty::post) 0) 0 pre pvs)`,
     `FLAT (abi_tuple_heads (head_lengths (pre ++ aty::post) 0)
       (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size aty av)
       post rest) ++ FLAT (abi_tuple_tails pre pvs) ++
       FLAT (abi_tuple_tails post rest)`] >>
  simp[APPEND_ASSOC, abi_encoder_open_heads_length]
QED

Theorem entry_layout_member_source:
  LIST_REL abi_encoder_layout_valid (pre ++ aty::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\
  E = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at sb (LENGTH E) mem = E /\
  sb + LENGTH E < dimword (:256) /\
  off = (if is_dynamic aty then head_lengths (pre ++ aty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs)
         else SUM (MAP abi_member_head_size pre)) ==>
  mem_bytes_at (sb + off) (LENGTH (enc aty av)) mem = enc aty av /\
  sb + off + LENGTH (enc aty av) < dimword (:256)
Proof
  strip_tac >> drule_all entry_layout_member_parts >> strip_tac >>
  `off = LENGTH prefix` by metis_tac[] >>
  `E = prefix ++ enc aty av ++ suffix` by metis_tac[] >>
  conj_tac
  >- metis_tac[abi_decoder_source_subwindow] >>
  qpat_x_assum `sb + LENGTH E < _` mp_tac >>
  asm_rewrite_tac[LENGTH_APPEND] >> decide_tac
QED

Theorem entry_source_member_source:
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v)
    tys vs /\
  vyper_to_abi_list env tys vs = SOME (pvs ++ av::rest) /\
  MAP (vyper_to_abi_type env) tys = pre ++ aty::post /\
  LENGTH pre = LENGTH pvs /\
  E = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at sb (LENGTH E) mem = E /\
  sb + LENGTH E < dimword (:256) /\
  off = (if is_dynamic aty then head_lengths (pre ++ aty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs)
         else SUM (MAP abi_member_head_size pre)) ==>
  mem_bytes_at (sb + off) (LENGTH (enc aty av)) mem = enc aty av /\
  sb + off + LENGTH (enc aty av) < dimword (:256)
Proof
  strip_tac >> drule_all entry_source_list_conversion_layout >> strip_tac >>
  irule entry_layout_member_source >> goal_assum (drule_at Any) >>
  qexistsl_tac [`E`, `rest`] >> metis_tac[]
QED
