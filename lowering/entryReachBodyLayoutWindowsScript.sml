Theory entryReachBodyLayoutWindows
Ancestors
  abiEncoderOpenInput abiCanonicalWindows abiDecodeRanges contractABI
  list rich_list arithmetic

(* Reuse the existing static-byte layout relation, without ABI typing. *)
Theorem entry_layout_index_iff:
  LIST_REL abi_encoder_layout_valid ts avs <=>
  LENGTH ts = LENGTH avs /\
  (!i. i < LENGTH ts /\ ~is_dynamic (EL i ts) ==>
    LENGTH (enc (EL i ts) (EL i avs)) = abi_member_head_size (EL i ts))
Proof
  simp[LIST_REL_EL_EQN, abi_encoder_layout_valid_def,
       abi_member_head_size_def] >> metis_tac[]
QED

Theorem entry_layout_head_length[local]:
  abi_encoder_layout_valid ty v ==>
  LENGTH (if is_dynamic ty then enc_number (Uint 256) (NumV off)
          else enc ty v) = abi_member_head_size ty
Proof
  Cases_on `is_dynamic ty` >>
  simp[abi_encoder_layout_valid_def, abi_member_head_size_def]
QED

Theorem entry_layout_split[local]:
  !pre pvs ty post v rest.
  LIST_REL abi_encoder_layout_valid (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs ==>
  LIST_REL abi_encoder_layout_valid pre pvs /\
  abi_encoder_layout_valid ty v /\
  LIST_REL abi_encoder_layout_valid post rest
Proof
  Induct >> Cases_on `pvs` >> simp[] >> metis_tac[]
QED

Theorem entry_layout_member_head_window:
  LIST_REL abi_encoder_layout_valid (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs ==>
  let hl = head_lengths (pre ++ ty::post) 0 in
  let tl = SUM (MAP2 abi_member_tail_size pre pvs) in
  TAKE (abi_member_head_size ty)
    (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) =
    (if is_dynamic ty then enc_number (Uint 256) (NumV (hl + tl))
     else enc ty v)
Proof
  strip_tac >> drule_all entry_layout_split >> strip_tac >>
  simp_tac bool_ss [LET_THM] >> irule abi_window_from_parts >>
  conj_tac >- simp[entry_layout_head_length] >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs)`,
     `FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
       (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
       post rest) ++ FLAT (abi_tuple_tails pre pvs) ++
       (if is_dynamic ty then enc ty v else []) ++
       FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      match_mp_tac (SIMP_RULE pureSimps.pure_ss [LET_THM] canonical_member_parts) >>
      first_assum ACCEPT_TAC) >>
  simp[abi_encoder_open_heads_length]
QED

Theorem entry_layout_member_tail_window:
  LIST_REL abi_encoder_layout_valid (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty ==>
  TAKE (LENGTH (enc ty v))
    (DROP (head_lengths (pre ++ ty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) = enc ty v
Proof
  strip_tac >> drule_all entry_layout_split >> strip_tac >>
  irule abi_window_from_parts >>
  conj_tac >- REFL_TAC >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs) ++
      enc_number (Uint 256)
        (NumV (head_lengths (pre ++ ty::post) 0 +
               SUM (MAP2 abi_member_tail_size pre pvs))) ++
      FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
        (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
        post rest) ++ FLAT (abi_tuple_tails pre pvs)`,
     `FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      qpat_x_assum `is_dynamic ty` (fn dyn =>
        match_mp_tac (SIMP_RULE bool_ss [LET_THM,dyn]
          canonical_member_parts)) >>
      first_assum ACCEPT_TAC) >>
  simp[abi_encoder_open_heads_length, abi_tuple_tails_length,
       head_lengths_acc, MAP_APPEND, SUM_APPEND, abi_member_head_size_def] >>
  decide_tac
QED
