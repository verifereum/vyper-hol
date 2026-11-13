Theory extcallDecoderStaticSuffix
Ancestors
  vyperABI contractABI list arithmetic

Theorem static_valid_tuple_take[local]:
  !ts k hds base base'.
  ~any_dynamic ts /\ static_length (Tuple ts) <= k /\ k <= LENGTH hds ==>
  (vyper_decode_valid_enc_tuple ts base (TAKE k hds) <=>
   vyper_decode_valid_enc_tuple ts base' hds)
Proof
  Induct >> simp[vyper_decode_valid_enc_def] >> rpt strip_tac >>
  gvs[is_dynamic_def] >>
  simp[vyper_decode_valid_enc_def, TAKE_TAKE_MIN, DROP_TAKE, LENGTH_TAKE] >>
  `MIN (static_length h) k = static_length h` by simp[MIN_DEF] >>
  `vyper_decode_valid_enc_tuple ts base
     (TAKE (k - static_length h) (DROP (static_length h) hds)) =
   vyper_decode_valid_enc_tuple ts base' (DROP (static_length h) hds)` by
    (first_x_assum irule >> simp[LENGTH_DROP] >> decide_tac) >>
  simp[is_dynamic_def]
QED

Theorem static_valid_array_take[local]:
  !n k hds base base'.
  n * l <= k /\ k <= LENGTH hds ==>
  (vyper_decode_valid_enc_array n (SOME l) t base (TAKE k hds) <=>
   vyper_decode_valid_enc_array n (SOME l) t base' hds)
Proof
  Induct >> simp[vyper_decode_valid_enc_def] >> rpt strip_tac >>
  `l <= k /\ n * l <= k - l` by gvs[MULT_CLAUSES] >>
  `MIN l k = l` by simp[MIN_DEF] >>
  `vyper_decode_valid_enc_array n (SOME l) t base
     (TAKE (k - l) (DROP l hds)) =
   vyper_decode_valid_enc_array n (SOME l) t base' (DROP l hds)` by
    (first_x_assum irule >> simp[LENGTH_DROP] >> decide_tac) >>
  simp[vyper_decode_valid_enc_def, TAKE_TAKE_MIN, DROP_TAKE, LENGTH_TAKE]
QED

Theorem static_dec_tuple_take[local]:
  !ts k hds base base' acc.
  ~any_dynamic ts /\ static_length (Tuple ts) <= k /\ k <= LENGTH hds ==>
  dec_tuple ts base (TAKE k hds) acc = dec_tuple ts base' hds acc
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[is_dynamic_def] >>
  `MIN (static_length h) k = static_length h` by simp[MIN_DEF] >>
  simp[dec_def, is_dynamic_def, TAKE_TAKE_MIN, DROP_TAKE] >>
  first_x_assum irule >> simp[LENGTH_DROP] >> decide_tac
QED

Theorem static_dec_array_take[local]:
  !n k hds base base' acc.
  n * l <= k /\ k <= LENGTH hds ==>
  dec_array n (SOME l) t base (TAKE k hds) acc =
  dec_array n (SOME l) t base' hds acc
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `l <= k /\ n * l <= k - l` by gvs[MULT_CLAUSES] >>
  `MIN l k = l` by simp[MIN_DEF] >>
  simp[dec_def, TAKE_TAKE_MIN, DROP_TAKE] >>
  first_x_assum irule >> simp[LENGTH_DROP] >> decide_tac
QED

Theorem static_decode_valid_suffix:
  !at bs. ~is_dynamic at /\ static_length at <= LENGTH bs ==>
  (vyper_decode_valid_enc at (TAKE (static_length at) bs) <=>
   vyper_decode_valid_enc at bs)
Proof
  Cases >> rpt strip_tac >>
  gvs[is_dynamic_def] >>
  simp[vyper_decode_valid_enc_def, TAKE_TAKE_MIN, LENGTH_TAKE] >~
   [`vyper_decode_valid_enc_tuple l _ _`] >-
   (`vyper_decode_valid_enc_tuple l (TAKE (static_length (Tuple l)) bs)
       (TAKE (static_length (Tuple l)) bs) =
     vyper_decode_valid_enc_tuple l bs bs` by
      (irule static_valid_tuple_take >> simp[]) >> simp[])
  >~ [`vyper_decode_valid_enc (Bytes ob) _`] >-
   (Cases_on `ob` >> gvs[is_dynamic_def, vyper_decode_valid_enc_def,
      valid_bytes_bound_def, LENGTH_TAKE, TAKE_TAKE_MIN] >>
    simp[MIN_DEF] >> eq_tac >> rpt strip_tac >> simp[] >> decide_tac) >>
  Cases_on `o'` >> gvs[is_dynamic_def, vyper_decode_valid_enc_def] >>
  `vyper_decode_valid_enc_array x (SOME (static_length a)) a
     (TAKE (x * static_length a) bs) (TAKE (x * static_length a) bs) =
   vyper_decode_valid_enc_array x (SOME (static_length a)) a bs bs` by
    (irule static_valid_array_take >> simp[]) >> simp[]
QED

Theorem static_dec_suffix:
  !at bs. ~is_dynamic at /\ static_length at <= LENGTH bs /\
  vyper_decode_valid_enc at bs ==>
  dec at (TAKE (static_length at) bs) = dec at bs
Proof
  Cases >> rpt strip_tac >> gvs[is_dynamic_def] >>
  simp[TAKE_TAKE_MIN] >~ [`dec_tuple ts _ _ _`] >-
   (irule static_dec_tuple_take >> simp[])
  >~ [`dec (Bytes ob) _`] >-
   (Cases_on `ob` >> gvs[is_dynamic_def, vyper_decode_valid_enc_def,
      valid_bytes_bound_def, TAKE_TAKE_MIN, MIN_DEF] >>
    IF_CASES_TAC >> gvs[] >> simp[TAKE_EQ_REWRITE]) >>
  Cases_on `o'` >> gvs[is_dynamic_def] >>
  simp[is_dynamic_def] >> irule static_dec_array_take >> simp[]
QED
