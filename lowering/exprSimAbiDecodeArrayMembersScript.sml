Theory exprSimAbiDecodeArrayMembers
Ancestors
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeTupleSource
  exprSimAbiDecodeArraySource
  abiValidAggregateHeads abiValidMembers vyperABIValid vyperABI contractABI
  vyperValue words list rich_list arithmetic

(* Offsets in an element head are relative to the payload after the count. *)
Definition abi_array_member_view_def:
  abi_array_member_view at bs p k =
    abi_decode_member_bytes at (DROP (p+32) bs)
      (DROP (k * abi_member_head_size at) (DROP (p+32) bs))
End

Theorem abi_array_member_view_relative:
  abi_array_member_view at bs p k =
    abi_decode_member_bytes at (DROP 32 (DROP p bs))
      (DROP (k * abi_member_head_size at) (DROP 32 (DROP p bs)))
Proof
  simp[abi_array_member_view_def, DROP_DROP_T, ADD_COMM]
QED

Theorem abi_array_members_source:
  !n env ty bs ao vs.
  ao + n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs ==>
  (vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty)) bs (DROP ao bs) /\
   abi_to_vyper_list env (REPLICATE n ty)
     (abi_decode_members (REPLICATE n (vyper_to_abi_type env ty)) bs (DROP ao bs)) = SOME vs
   <=>
   LENGTH vs = n /\
   (!k. k < n ==> abi_decode_source_accepts env ty
     (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
       (DROP (ao + k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k vs)))
Proof
  Induct
  >- simp[Once vyper_decode_valid_enc_def, abi_decode_members_def] >>
  rpt gen_tac >> strip_tac >>
  `ao + abi_member_head_size (vyper_to_abi_type env ty) +
    n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs` by
    (fs[MULT_CLAUSES] >> decide_tac) >>
  `abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH (DROP ao bs)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  first_x_assum (qspecl_then [`env`, `ty`, `bs`,
    `ao + abi_member_head_size (vyper_to_abi_type env ty)`] mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  Cases_on `vs`
  >- simp[REPLICATE, abi_decode_members_def, Once abi_to_vyper_def, AllCaseEqs()] >>
  simp_tac (srw_ss()) [REPLICATE, abi_tuple_valid_cons_iff,
    abi_decode_members_def, Once abi_to_vyper_def, AllCaseEqs(), DROP_DROP_T,
    AC ADD_ASSOC ADD_COMM] >>
  gvs[Excl "vyper_decode_valid_enc_def", Excl "dec_def"] >>
  eq_tac
  >- (strip_tac >>
      `LENGTH t = n /\
       (!k. k < n ==> abi_decode_source_accepts env ty
         (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
           (DROP (ao + abi_member_head_size (vyper_to_abi_type env ty) +
                  k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k t))`
        by (simp_tac bool_ss [GSYM ADD_ASSOC] >> metis_tac[]) >>
      conj_tac >- simp[] >>
      Cases
      >- (simp_tac std_ss [EL, HD, TL, abi_decode_source_accepts_def] >> metis_tac[]) >>
      simp_tac std_ss [EL, TL, MULT_CLAUSES, AC ADD_ASSOC ADD_COMM] >>
      metis_tac[ADD_ASSOC, ADD_COMM]) >>
  strip_tac >>
  `abi_decode_source_accepts env ty
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs (DROP ao bs)) h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!k. k < n ==> abi_decode_source_accepts env ty
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (ao + abi_member_head_size (vyper_to_abi_type env ty) +
             k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k t)` by
    (gen_tac >> strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >>
     asm_simp_tac std_ss [EL, TL, MULT_CLAUSES, AC ADD_ASSOC ADD_COMM]) >>
  metis_tac[abi_decode_source_accepts_def, ADD_ASSOC]
QED

Theorem abi_array_dynamic_source:
  evaluate_type env ty = SOME tv /\
  32 <= LENGTH (DROP p bs) /\
  abi_head_word (DROP p bs) <= maxn /\
  32 + abi_head_word (DROP p bs) * abi_member_head_size (vyper_to_abi_type env ty)
    <= LENGTH (DROP p bs) ==>
  (abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) (DROP p bs)
     (ArrayV (make_array_value tv (Dynamic maxn) vs)) <=>
   LENGTH vs = abi_head_word (DROP p bs) /\
   (!k. k < abi_head_word (DROP p bs) ==>
     abi_decode_source_accepts env ty
       (abi_array_member_view (vyper_to_abi_type env ty) bs p k) (EL k vs)))
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`abi_head_word (DROP p bs)`, `env`, `ty`,
    `DROP 32 (DROP p bs)`, `0`, `vs`] abi_array_members_source) >>
  asm_simp_tac std_ss [LENGTH_DROP] >>
  impl_tac >- (fs[LENGTH_DROP] >> decide_tac) >>
  simp_tac std_ss [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once vyper_decode_valid_enc_def, Once dec_def, LET_THM,
    GSYM abi_head_word_def, abi_decode_array_members, abi_decode_members_value,
    abi_to_vyper_def, abi_decode_members_length, LENGTH_REPLICATE,
    REVERSE_DEF, APPEND, compatible_bound_def, abi_array_member_view_relative,
    GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
  `abi_head_word (DROP p bs) < dimword (:256)` by
    simp[abi_head_word_def, dec_number_def, dest_NumV_def, w2n_lt] >>
  asm_simp_tac (srw_ss()) [DROP_0, dec_number_def, is_num_value_def,
    make_array_value_def, AllCaseEqs(), Excl "dec_def",
    Excl "vyper_decode_valid_enc_def"]
QED

Theorem abi_array_dynamic_source_shape:
  abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) view v ==>
  ?tv vs. evaluate_type env ty = SOME tv /\
    v = ArrayV (make_array_value tv (Dynamic maxn) vs)
Proof
  simp_tac bool_ss [abi_decode_source_accepts_def, vyper_to_abi_type_def] >>
  strip_tac >> drule abi_valid_dynamic_array_view >> strip_tac >>
  gvs[abi_to_vyper_def, AllCaseEqs(),
      Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  metis_tac[]
QED

Theorem abi_array_dynamic_source_project:
  abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) (DROP p bs) v ==>
  ?tv vs. evaluate_type env ty = SOME tv /\
    v = ArrayV (make_array_value tv (Dynamic maxn) vs) /\
    LENGTH vs = abi_head_word (DROP p bs) /\
    (!k. k < abi_head_word (DROP p bs) ==>
      abi_decode_source_accepts env ty
        (abi_array_member_view (vyper_to_abi_type env ty) bs p k) (EL k vs))
Proof
  strip_tac >>
  drule abi_array_dynamic_source_shape >> strip_tac >>
  `32 <= LENGTH (DROP p bs) /\ abi_head_word (DROP p bs) <= maxn /\
   32 + abi_head_word (DROP p bs) * abi_member_head_size (vyper_to_abi_type env ty)
      <= LENGTH (DROP p bs)` by
    (irule abi_decode_dynarray_source_guard_bounds >>
     fs[abi_decode_source_accepts_def, vyper_to_abi_type_def,
        Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >> metis_tac[]) >>
  drule_all abi_array_dynamic_source >>
  metis_tac[]
QED

Theorem abi_array_dynamic_member_reject:
  k < abi_head_word (DROP p bs) /\
  ~(?v. abi_decode_source_accepts env ty
    (abi_array_member_view (vyper_to_abi_type env ty) bs p k) v) ==>
  ~(?v. abi_decode_source_accepts env (ArrayT ty (Dynamic maxn)) (DROP p bs) v)
Proof
  metis_tac[abi_array_dynamic_source_project]
QED
