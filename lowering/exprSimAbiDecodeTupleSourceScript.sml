Theory exprSimAbiDecodeTupleSource
Ancestors
  abiValidMembers abiDecodeRanges vyperABI contractABI words list rich_list arithmetic

(* Cursor positions count heterogeneous ABI head widths; slices retain the
   original payload as their offset base, including on malformed input. *)
Definition abi_tuple_cursor_def:
  abi_tuple_cursor ts ao i = ao + SUM (MAP abi_member_head_size (TAKE i ts))
End

Theorem abi_tuple_cursor_zero[simp]:
  abi_tuple_cursor ts ao 0 = ao
Proof
  simp[abi_tuple_cursor_def]
QED

Theorem abi_tuple_cursor_cons[simp]:
  abi_tuple_cursor (t::ts) ao (SUC i) =
  abi_tuple_cursor ts (ao + abi_member_head_size t) i
Proof
  `SUC i <> 0` by decide_tac >>
  asm_simp_tac std_ss [abi_tuple_cursor_def, TAKE_def, MAP, SUM, ADD_ASSOC]
QED

Theorem abi_tuple_valid_cons_iff:
  vyper_decode_valid_enc_tuple (t::ts) bs hds <=>
  abi_member_head_size t <= LENGTH hds /\
  vyper_decode_valid_enc t (abi_decode_member_bytes t bs hds) /\
  vyper_decode_valid_enc_tuple ts bs (DROP (abi_member_head_size t) hds)
Proof
  Cases_on `is_dynamic t` >>
  asm_simp_tac (srw_ss()) [Once vyper_decode_valid_enc_def, LET_THM,
    abi_member_head_size_def, abi_decode_member_bytes_def,
    abi_head_word_def, dec_number_def, is_num_value_def, dest_NumV_def]
QED

Theorem abi_tuple_valid_cursor:
  !ts bs ao.
  vyper_decode_valid_enc_tuple ts bs (DROP ao bs) <=>
  (!i. i < LENGTH ts ==>
    abi_member_head_size (EL i ts) <=
      LENGTH (DROP (abi_tuple_cursor ts ao i) bs) /\
    vyper_decode_valid_enc (EL i ts)
      (abi_decode_member_bytes (EL i ts) bs
        (DROP (abi_tuple_cursor ts ao i) bs)))
Proof
  Induct >- simp[Once vyper_decode_valid_enc_def] >>
  rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_valid_cons_iff, DROP_DROP_T, LENGTH] >>
  once_rewrite_tac [ADD_COMM] >>
  asm_simp_tac bool_ss [] >>
  eq_tac
  >- (strip_tac >> Cases >>
      gvs[abi_tuple_cursor_zero, abi_tuple_cursor_cons,
        Excl "vyper_decode_valid_enc_def", Excl "dec_def"])
  >> strip_tac >> conj_tac
  >- (qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
      simp_tac (srw_ss()) [abi_tuple_cursor_zero] >>
      strip_tac >> gvs[Excl "vyper_decode_valid_enc_def", Excl "dec_def"])
  >> conj_tac
  >- (qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
      simp_tac (srw_ss()) [abi_tuple_cursor_zero] >>
      strip_tac >> gvs[Excl "vyper_decode_valid_enc_def", Excl "dec_def"])
  >> gen_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[abi_tuple_cursor_cons, Excl "vyper_decode_valid_enc_def", Excl "dec_def"]
QED

Theorem abi_tuple_members_cursor:
  !ts bs ao.
  abi_decode_members ts bs (DROP ao bs) =
    GENLIST (\i. dec (EL i ts)
      (abi_decode_member_bytes (EL i ts) bs
        (DROP (abi_tuple_cursor ts ao i) bs))) (LENGTH ts)
Proof
  Induct >- simp_tac bool_ss [abi_decode_members_def, LENGTH, GENLIST] >>
  rpt gen_tac >>
  simp_tac bool_ss [abi_decode_members_def, LENGTH, GENLIST_CONS, DROP_DROP_T] >>
  once_rewrite_tac [ADD_COMM] >>
  asm_simp_tac std_ss [abi_tuple_cursor_zero, abi_tuple_cursor_cons, EL, HD, TL,
    combinTheory.o_DEF]
QED

Theorem abi_tuple_decode_cursor:
  dec_tuple ts bs (DROP ao bs) acc =
    ListV (REVERSE acc ++ GENLIST (\i. dec (EL i ts)
      (abi_decode_member_bytes (EL i ts) bs
        (DROP (abi_tuple_cursor ts ao i) bs))) (LENGTH ts))
Proof
  rewrite_tac [abi_decode_members_value, abi_tuple_members_cursor]
QED

Theorem abi_tuple_valid_root:
  vyper_decode_valid_enc (Tuple ts) bs <=>
  LENGTH ts < dimword (:256) /\
  (!i. i < LENGTH ts ==>
    abi_member_head_size (EL i ts) <=
      LENGTH (DROP (abi_tuple_cursor ts 0 i) bs) /\
    vyper_decode_valid_enc (EL i ts)
      (abi_decode_member_bytes (EL i ts) bs
        (DROP (abi_tuple_cursor ts 0 i) bs)))
Proof
  simp_tac bool_ss [Once vyper_decode_valid_enc_def] >>
  mp_tac (Q.SPECL [`ts`, `bs`, `0`] abi_tuple_valid_cursor) >>
  simp_tac std_ss [DROP_0]
QED

Theorem abi_tuple_decode_root:
  dec (Tuple ts) bs =
    ListV (GENLIST (\i. dec (EL i ts)
      (abi_decode_member_bytes (EL i ts) bs
        (DROP (abi_tuple_cursor ts 0 i) bs))) (LENGTH ts))
Proof
  simp_tac bool_ss [Once dec_def, abi_decode_members_value, REVERSE_DEF, APPEND] >>
  mp_tac (Q.SPECL [`ts`, `bs`, `0`] abi_tuple_members_cursor) >>
  simp_tac std_ss [DROP_0]
QED

Theorem abi_tuple_valid_cursor_head_bound:
  vyper_decode_valid_enc_tuple ts bs (DROP ao bs) ==>
  SUM (MAP abi_member_head_size ts) <= LENGTH bs - ao
Proof
  strip_tac >> drule abi_valid_members_view >> simp_tac std_ss [LENGTH_DROP]
QED

Theorem abi_tuple_short_head_reject:
  LENGTH bs < SUM (MAP abi_member_head_size ts) ==>
  ~vyper_decode_valid_enc (Tuple ts) bs
Proof
  strip_tac >> simp_tac bool_ss [Once vyper_decode_valid_enc_def] >>
  disj2_tac >> strip_tac >> drule abi_valid_members_view >> simp[]
QED

Theorem abi_tuple_failed_member_reject:
  i < LENGTH ts /\
  ~vyper_decode_valid_enc (EL i ts)
    (abi_decode_member_bytes (EL i ts) bs
      (DROP (abi_tuple_cursor ts 0 i) bs)) ==>
  ~vyper_decode_valid_enc (Tuple ts) bs
Proof
  rewrite_tac [abi_tuple_valid_root] >> metis_tac []
QED

Theorem abi_tuple_valid_head_bound:
  vyper_decode_valid_enc (Tuple ts) bs ==>
  SUM (MAP abi_member_head_size ts) <= LENGTH bs
Proof
  simp_tac bool_ss [Once vyper_decode_valid_enc_def] >>
  strip_tac >> drule abi_valid_members_view >> simp_tac bool_ss []
QED

(* Expand these two small views only at the external cursor interface.
   In particular the dynamic offset is always relative to bs, not hds. *)
Theorem abi_tuple_cursor_width:
  abi_tuple_cursor ts ao i =
    ao + SUM (MAP (\t. if is_dynamic t then 32 else static_length t) (TAKE i ts))
Proof
  rewrite_tac [abi_tuple_cursor_def] >>
  `abi_member_head_size = (\t. if is_dynamic t then 32 else static_length t)` by
    simp_tac bool_ss [FUN_EQ_THM, abi_member_head_size_def] >>
  asm_rewrite_tac []
QED

Theorem abi_tuple_member_slice:
  abi_decode_member_bytes t bs (DROP ao bs) =
    if is_dynamic t then
      DROP (dest_NumV (dec_number (Uint 256) (TAKE 32 (DROP ao bs)))) bs
    else TAKE (static_length t) (DROP ao bs)
Proof
  rewrite_tac [abi_decode_member_bytes_def, abi_head_word_def]
QED
