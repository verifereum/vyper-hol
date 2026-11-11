(* TOP-LEVEL: the separate physical head/tail model is exactly the source
   ABI tuple encoder, including arbitrary previously accumulated heads and
   tails. Static head sizes agree when individual static encodings do. *)
Theory abiFieldSource
Ancestors
  abiFieldLayoutDefs contractABI list pair rich_list words arithmetic

Theorem enc_tuple_field_parts:
  !tys vs head_size tail_size heads tails.
    LENGTH tys = LENGTH vs ==>
    enc_tuple head_size tail_size tys vs heads tails =
      FLAT (REVERSE heads) ++
      abi_field_heads (head_size + tail_size) (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs) ++
      FLAT (REVERSE tails) ++
      abi_field_tails (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs)
Proof
  Induct_on `tys`
  >- (Cases >> simp[Once enc_def, abi_field_heads_def, abi_field_tails_def, REV_REVERSE_LEM, FLAT_APPEND]) >>
  MAP_EVERY qx_gen_tac [`ty`, `vs`] >> Cases_on `vs` >- simp[] >>
  rename1 `enc_tuple _ _ (ty::tys) (v::vs) _ _` >> rpt gen_tac >> simp_tac (srw_ss()) [] >> DISCH_TAC >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
  asm_simp_tac (srw_ss()) [LET_THM, abi_field_heads_def, abi_field_tails_def, abi_field_head_def,
    abi_field_tail_def, REV_REVERSE_LEM, FLAT_APPEND, APPEND_ASSOC, ADD_ASSOC]
QED

Theorem enc_tuple_field_bytes:
  !tys vs.
    LENGTH tys = LENGTH vs ==>
    enc (Tuple tys) (ListV vs) =
      abi_field_bytes (head_lengths tys 0) (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs)
Proof
  rpt gen_tac >> DISCH_TAC >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
  asm_simp_tac (srw_ss()) [LET_THM, enc_tuple_field_parts, abi_field_bytes_def]
QED

Theorem static_field_head_sizes:
  !tys vs.
    LIST_REL (\ty v. ~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) tys vs ==>
    !acc. head_lengths tys acc =
      acc + abi_field_head_size (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs)
Proof
  Induct_on `tys` >- (Cases >> simp[head_lengths_def, abi_field_head_size_def]) >>
  MAP_EVERY qx_gen_tac [`ty`, `vs`] >> Cases_on `vs` >- simp[] >>
  rename1 `LIST_REL _ (ty::tys) (v::vs)` >> simp_tac (srw_ss()) [] >> strip_tac >>
  first_x_assum (qspec_then `vs` mp_tac) >> impl_tac
  >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qx_gen_tac `acc` >> Cases_on `is_dynamic ty` >>
  asm_simp_tac bool_ss [head_lengths_def, abi_field_head_size_def] >>
  fs[] >> decide_tac
QED

Theorem enc_tuple_head_size:
  !tys vs.
    LIST_REL (\ty v. ~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) tys vs ==>
    enc (Tuple tys) (ListV vs) =
      abi_field_bytes (abi_field_head_size (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs))
        (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs)
Proof
  rpt gen_tac >> DISCH_TAC >>
  `LENGTH tys = LENGTH vs` by (drule LIST_REL_LENGTH >> simp[]) >>
  mp_tac (Q.SPECL [`tys`, `vs`] static_field_head_sizes) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> disch_then (qspec_then `0` mp_tac) >>
  simp[enc_tuple_field_bytes]
QED
