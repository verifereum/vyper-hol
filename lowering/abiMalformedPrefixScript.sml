(* Pure processed-prefix reflection over arbitrary ABI source bytes. *)
Theory abiMalformedPrefix
Ancestors
  abiVyperAdmissible vyperABI contractABI list rich_list arithmetic

Definition abi_reflected_child_def:
  abi_reflected_child a xs k =
    if is_dynamic a then DROP (abi_head_word (DROP (32 * k) xs)) xs
    else TAKE (static_length a) (DROP (static_length a * k) xs)
End

Definition abi_reflected_head_ok_def:
  abi_reflected_head_ok a xs k <=>
    if is_dynamic a then
      32 <= LENGTH (DROP (32 * k) xs) /\
      is_num_value (dec_number (Uint 256) (TAKE 32 (DROP (32 * k) xs)))
    else static_length a <= LENGTH (DROP (static_length a * k) xs)
End

Definition abi_reflected_prefix_def:
  abi_reflected_prefix env ty xs j avs <=>
    LENGTH avs = j /\
    !k. k < j ==>
      abi_reflected_head_ok (vyper_to_abi_type env ty) xs k /\
      vyper_decode_valid_enc (vyper_to_abi_type env ty)
        (abi_reflected_child (vyper_to_abi_type env ty) xs k) /\
      EL k avs = dec (vyper_to_abi_type env ty)
        (abi_reflected_child (vyper_to_abi_type env ty) xs k) /\
      abi_vyper_admissible env ty (EL k avs)
End

Theorem abi_reflected_prefix_empty:
  abi_reflected_prefix env ty xs 0 []
Proof
  simp[abi_reflected_prefix_def]
QED

Theorem abi_reflected_prefix_append:
  abi_reflected_prefix env ty xs j avs /\
  abi_reflected_head_ok a xs j /\
  vyper_decode_valid_enc a (abi_reflected_child a xs j) /\
  abi_vyper_admissible env ty (dec a (abi_reflected_child a xs j)) /\
  a = vyper_to_abi_type env ty ==>
  abi_reflected_prefix env ty xs (SUC j)
    (avs ++ [dec a (abi_reflected_child a xs j)])
Proof
  simp_tac bool_ss [abi_reflected_prefix_def] >> strip_tac >> gvs[] >>
  qx_gen_tac `k` >> strip_tac >> Cases_on `k < LENGTH avs`
  >- (simp[EL_APPEND1] >> first_x_assum drule >> strip_tac >> gvs[]) >>
  `k = LENGTH avs` by decide_tac >> gvs[EL_APPEND2]
QED

Theorem abi_reflected_children_valid[local]:
  !n a xs i.
    (!k. k < n ==>
      abi_reflected_head_ok a xs (i + k) /\
      vyper_decode_valid_enc a (abi_reflected_child a xs (i + k))) ==>
    vyper_decode_valid_enc_array n
      (if is_dynamic a then NONE else SOME (static_length a)) a xs
      (DROP ((if is_dynamic a then 32 else static_length a) * i) xs)
Proof
  Induct >- simp[Once vyper_decode_valid_enc_def] >>
  rpt gen_tac >> strip_tac >>
  `abi_reflected_head_ok a xs i /\
   vyper_decode_valid_enc a (abi_reflected_child a xs i)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `vyper_decode_valid_enc_array n
      (if is_dynamic a then NONE else SOME (static_length a)) a xs
      (DROP ((if is_dynamic a then 32 else static_length a) * SUC i) xs)` by
    (first_x_assum irule >> qx_gen_tac `k` >> strip_tac >>
     first_x_assum (qspec_then `SUC k` mp_tac) >> simp[ADD_CLAUSES]) >>
  Cases_on `is_dynamic a` >>
  fs[abi_reflected_head_ok_def, abi_reflected_child_def, abi_head_word_def] >>
  simp[Once vyper_decode_valid_enc_def] >>
  pure_rewrite_tac [DROP_DROP_T] >>
  qpat_x_assum `vyper_decode_valid_enc_array n _ _ _ _` mp_tac >>
  simp_tac std_ss [MULT_CLAUSES, ADD_COMM]
QED

Theorem abi_reflected_prefix_valid:
  abi_reflected_prefix env ty xs j avs ==>
  vyper_decode_valid_enc_array j
    (if is_dynamic (vyper_to_abi_type env ty) then NONE
     else SOME (static_length (vyper_to_abi_type env ty)))
    (vyper_to_abi_type env ty) xs xs
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`j`, `vyper_to_abi_type env ty`, `xs`, `0`]
    abi_reflected_children_valid) >>
  simp[] >> disch_then irule >> fs[abi_reflected_prefix_def] >>
  metis_tac[]
QED

Theorem abi_vyper_admissible_replicate:
  !avs. abi_vyper_admissible_list env (REPLICATE (LENGTH avs) ty) avs <=>
    EVERY (abi_vyper_admissible env ty) avs
Proof
  Induct >> simp[abi_vyper_admissible_list_nil, abi_vyper_admissible_list_cons]
QED

Theorem abi_reflected_prefix_admissible:
  abi_reflected_prefix env ty xs j avs ==>
  abi_vyper_admissible_list env (REPLICATE j ty) avs
Proof
  simp_tac bool_ss [abi_reflected_prefix_def] >> strip_tac >> gvs[] >>
  simp[abi_vyper_admissible_replicate, EVERY_EL] >> metis_tac[]
QED
