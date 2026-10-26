(* Canonical array data and member windows, for fixed and dynamic arrays. *)
Theory abiCanonicalArrays
Ancestors
  venomMemProps
  abiCanonicalWindows abiDecodeRanges contractABI list rich_list arithmetic byte

Theorem canonical_array_tuple:
  enc (Array bound ty) (ListV vs) =
    (if bound = NONE then enc_number (Uint 256) (NumV (LENGTH vs)) else []) ++
    enc (Tuple (REPLICATE (LENGTH vs) ty)) (ListV vs)
Proof
  Cases_on `bound` >>
  simp[Once enc_def, enc_tuple_parts, abi_tuple_heads_def, abi_tuple_tails_def]
QED

Theorem canonical_array_drop_count:
  DROP (if bound = NONE then 32 else 0)
    (enc (Array bound ty) (ListV vs)) =
  enc (Tuple (REPLICATE (LENGTH vs) ty)) (ListV vs)
Proof
  pure_rewrite_tac[canonical_array_tuple] >> Cases_on `bound` >>
  simp[enc_number_def, LENGTH_word_to_bytes, DROP_APPEND]
QED

Theorem canonical_array_member_head_window:
  has_type (Array bound ty) (ListV (pre ++ v::post)) ==>
  TAKE (abi_member_head_size ty)
    (DROP ((if bound = NONE then 32 else 0) +
           LENGTH pre * abi_member_head_size ty)
      (enc (Array bound ty) (ListV (pre ++ v::post)))) =
    (if is_dynamic ty then enc_number (Uint 256)
       (NumV (LENGTH (pre ++ v::post) * abi_member_head_size ty +
               SUM (MAP (abi_member_tail_size ty) pre)))
     else enc ty v)
Proof
  strip_tac >>
  `has_types (REPLICATE (LENGTH (pre ++ v::post)) ty) (pre ++ v::post)` by
    (irule have_type_replicate >> gvs[has_type_def]) >>
  ONCE_REWRITE_TAC[ADD_COMM] >>
  pure_rewrite_tac[GSYM DROP_DROP_T, canonical_array_drop_count] >>
  qspecl_then [`REPLICATE (LENGTH pre) ty`, `ty`,
    `REPLICATE (LENGTH post) ty`, `pre`, `v`, `post`] mp_tac
    (Q.GENL [`pre`, `ty`, `post`, `pvs`, `v`, `rest`]
      canonical_member_head_window) >>
  simp_tac bool_ss [LENGTH_REPLICATE, GSYM REPLICATE, REPLICATE_APPEND,
    LENGTH_APPEND, LENGTH, uniform_member_sizes, head_lengths_acc,
    MAP_APPEND, SUM_APPEND, MAP, SUM] >>
  simp[uniform_member_sizes, LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
  gvs[LENGTH_APPEND, DROP_DROP_T]
QED

Theorem canonical_array_member_tail_window:
  has_type (Array bound ty) (ListV (pre ++ v::post)) /\ is_dynamic ty ==>
  TAKE (LENGTH (enc ty v))
    (DROP ((if bound = NONE then 32 else 0) +
           LENGTH (pre ++ v::post) * abi_member_head_size ty +
           SUM (MAP (abi_member_tail_size ty) pre))
      (enc (Array bound ty) (ListV (pre ++ v::post)))) = enc ty v
Proof
  strip_tac >>
  `has_types (REPLICATE (LENGTH (pre ++ v::post)) ty) (pre ++ v::post)` by
    (irule have_type_replicate >> gvs[has_type_def]) >>
  pure_rewrite_tac[GSYM ADD_ASSOC] >> ONCE_REWRITE_TAC[ADD_COMM] >>
  pure_rewrite_tac[GSYM DROP_DROP_T, canonical_array_drop_count] >>
  qspecl_then [`REPLICATE (LENGTH pre) ty`, `ty`,
    `REPLICATE (LENGTH post) ty`, `pre`, `v`, `post`] mp_tac
    (Q.GENL [`pre`, `ty`, `post`, `pvs`, `v`, `rest`]
      canonical_member_tail_window) >>
  simp_tac bool_ss [LENGTH_REPLICATE, GSYM REPLICATE, REPLICATE_APPEND,
    LENGTH_APPEND, LENGTH, uniform_member_sizes, head_lengths_acc,
    MAP_APPEND, SUM_APPEND, MAP, SUM] >>
  simp[uniform_member_sizes, LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
  gvs[LENGTH_APPEND, DROP_DROP_T]
QED
