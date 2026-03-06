(*
 * vyperTypingScript.sml
 *
 * Type-value compatibility predicates for Vyper values and typed_values.
 *
 * TOP-LEVEL:
 *   well_formed_value_def - structural well-formedness of values
 *   value_has_type_def - value matches a typed_value
 *   value_has_type_equiv - equivalence with encode_value IS_SOME
 *   well_formed_type_value_def - well-formedness of typed_value descriptors
 *)

Theory vyperTyping
Ancestors
  vyperStorage vyperValue vyperMisc sorting
Libs
  wordsLib

(* Well-formedness of type_values for storage operations.
   Ensures type_slot_size tv ≤ dimword(:256) for all well-formed types. *)
Definition well_formed_type_value_def:
  well_formed_type_value (BaseTV (BytesT (Fixed n))) = (n ≤ 32) ∧
  well_formed_type_value (BaseTV (BytesT (Dynamic n))) =
    (type_slot_size (BaseTV (BytesT (Dynamic n))) ≤ dimword(:256)) ∧
  well_formed_type_value (BaseTV (StringT n)) =
    (type_slot_size (BaseTV (StringT n)) ≤ dimword(:256)) ∧
  well_formed_type_value (TupleTV tvs) =
    (EVERY well_formed_type_value tvs ∧
     type_slot_size (TupleTV tvs) ≤ dimword(:256)) ∧
  well_formed_type_value (ArrayTV tv b) =
    (0 < type_slot_size tv ∧ well_formed_type_value tv ∧
     type_slot_size (ArrayTV tv b) ≤ dimword(:256)) ∧
  well_formed_type_value (StructTV fields) =
    (EVERY (well_formed_type_value o SND) fields ∧
     type_slot_size (StructTV fields) ≤ dimword(:256)) ∧
  well_formed_type_value _ = T
End

(* ===== well_formed_value ===== *)

(* Termination helpers for well_formed_value *)
Theorem wf_struct_size_helper[local]:
  ∀fields : (identifier # value) list.
    list_size (pair_size (K 0) value_size) fields ≤
    list_size (pair_size (list_size char_size) value_size) fields
Proof
  Induct >> rw[] >> PairCases_on `h` >> rw[]
QED

Theorem wf_sparse_size_helper[local]:
  ∀sparse : (num # value) list.
    list_size (pair_size (K 0) value_size) sparse ≤
    list_size (pair_size I value_size) sparse
Proof
  Induct >> rw[] >> PairCases_on `h` >> rw[]
QED

(* Well-formedness predicate on values (no type needed).
   Checks: numeric range fits in 256-bit words,
           static array keys in range and non-default,
           dynamic array length within bound,
           recursive well-formedness of sub-values. *)
Definition well_formed_value_def:
  well_formed_value (IntV (Unsigned _) i) = (0 ≤ i ∧ i < &dimword(:256)) ∧
  well_formed_value (IntV (Signed _) i) = (INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256)) ∧
  well_formed_value (DecimalV i) = (INT_MIN(:256) ≤ i ∧ i ≤ INT_MAX(:256)) ∧
  well_formed_value (FlagV _ k) = (k < dimword(:256)) ∧
  well_formed_value (BoolV _) = T ∧
  well_formed_value NoneV = T ∧
  well_formed_value (BytesV _ _) = T ∧
  well_formed_value (StringV _ _) = T ∧
  well_formed_value (ArrayV av) = wf_array av ∧
  well_formed_value (StructV fields) = wf_fields fields ∧
  wf_array (TupleV vs) = wf_values vs ∧
  wf_array (SArrayV tv n sparse) =
    (SORTED $< (MAP FST sparse) ∧ wf_sparse tv n sparse) ∧
  wf_array (DynArrayV tv max vs) = (LENGTH vs ≤ max ∧ wf_values vs) ∧
  wf_values [] = T ∧
  wf_values (v::vs) = (well_formed_value v ∧ wf_values vs) ∧
  wf_sparse tv n [] = T ∧
  wf_sparse tv n ((k,v)::rest) =
    (k < n ∧ v ≠ default_value tv ∧ well_formed_value v ∧ wf_sparse tv n rest) ∧
  wf_fields [] = T ∧
  wf_fields ((name,v)::rest) = (well_formed_value v ∧ wf_fields rest)
Termination
  WF_REL_TAC `measure (λx. case x of
    | INL v => value_size v
    | INR (INL av) => array_value_size av
    | INR (INR (INL vs)) => list_size value_size vs
    | INR (INR (INR (INL (_, _, sparse)))) =>
        list_size value_size (MAP SND sparse)
    | INR (INR (INR (INR fields))) =>
        list_size value_size (MAP SND fields))` >>
  rw[vyperMiscTheory.list_size_pair_size_map]
End

(* ===== value_has_type: structural characterization of encode_value success ===== *)

Definition value_has_type_def:
  (* Unsigned integer *)
  value_has_type (BaseTV (UintT m)) (IntV (Unsigned n) _) = (n = m) ∧
  (* Signed integer *)
  value_has_type (BaseTV (IntT m)) (IntV (Signed n) _) = (n = m) ∧
  (* Decimal *)
  value_has_type (BaseTV DecimalT) (DecimalV _) = T ∧
  (* Boolean *)
  value_has_type (BaseTV BoolT) (BoolV _) = T ∧
  (* Address *)
  value_has_type (BaseTV AddressT) (BytesV (Fixed m) bs) =
    (LENGTH bs = m ∧ m = 20) ∧
  (* Fixed bytes *)
  value_has_type (BaseTV (BytesT (Fixed n))) (BytesV (Fixed m) bs) =
    (m = n ∧ LENGTH bs = n ∧ n ≤ 32) ∧
  (* Dynamic bytes *)
  value_has_type (BaseTV (BytesT (Dynamic max))) (BytesV (Dynamic m) bs) =
    (m = max ∧ max < dimword(:256) ∧ LENGTH bs ≤ max) ∧
  (* String *)
  value_has_type (BaseTV (StringT max)) (StringV m s) =
    (m = max ∧ max < dimword(:256) ∧ LENGTH s ≤ max) ∧
  (* Flag *)
  value_has_type (FlagTV m') (FlagV m _) = (m = m') ∧
  (* None *)
  value_has_type NoneTV NoneV = T ∧
  (* Tuple *)
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) =
    values_have_types tvs vs ∧
  (* Static array *)
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV tv' m sparse)) =
    (tv = tv' ∧ n = m ∧ sparse_has_type tv sparse) ∧
  (* Dynamic array *)
  value_has_type (ArrayTV tv (Dynamic max)) (ArrayV (DynArrayV tv' m vs)) =
    (tv = tv' ∧ max = m ∧ all_have_type tv vs) ∧
  (* Struct *)
  value_has_type (StructTV ftypes) (StructV fields) =
    struct_has_type ftypes fields ∧
  (* Default: mismatch *)
  value_has_type _ _ = F ∧

  values_have_types [] [] = T ∧
  values_have_types (tv::tvs) (v::vs) =
    (value_has_type tv v ∧ values_have_types tvs vs) ∧
  values_have_types _ _ = F ∧

  sparse_has_type tv [] = T ∧
  sparse_has_type tv ((k:num,v)::rest) =
    (value_has_type tv v ∧ sparse_has_type tv rest) ∧

  all_have_type tv [] = T ∧
  all_have_type tv (v::vs) =
    (value_has_type tv v ∧ all_have_type tv vs) ∧

  struct_has_type [] [] = T ∧
  struct_has_type ((fname,tv)::ftypes) ((vname,v)::fields) =
    (fname = vname ∧ value_has_type tv v ∧ struct_has_type ftypes fields) ∧
  struct_has_type _ _ = F
Termination
  WF_REL_TAC `measure (λx. case x of
    | INL (_, v) => value_size v
    | INR (INL (_, vs)) => list_size value_size vs
    | INR (INR (INL (_, sparse))) =>
        list_size (pair_size (λx. 0) value_size) sparse
    | INR (INR (INR (INL (_, vs)))) => list_size value_size vs
    | INR (INR (INR (INR (_, fields)))) =>
        list_size (pair_size (λx. 0) value_size) fields)` >>
  rpt conj_tac >>
  TRY (Induct >> simp[basicSizeTheory.pair_size_def] >>
       Cases >> simp[basicSizeTheory.pair_size_def] >> NO_TAC) >>
  Induct_on `sparse` >> simp[basicSizeTheory.pair_size_def] >>
  Cases >> simp[basicSizeTheory.pair_size_def] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`m`, `tv'`] mp_tac) >> simp[]
End

(* ===== Helper lemmas  ===== *)

(* Helper: IS_SOME of compound encoders doesn't depend on offset *)
Theorem encode_IS_SOME_offset_indep[local]:
  (∀offset offset' tvs vs.
     IS_SOME (encode_tuple offset tvs vs) ⇔
     IS_SOME (encode_tuple offset' tvs vs)) ∧
  (∀tv offset offset' sparse.
     IS_SOME (encode_static_array tv offset sparse) ⇔
     IS_SOME (encode_static_array tv offset' sparse)) ∧
  (∀tv offset offset' vs.
     IS_SOME (encode_dyn_array tv offset vs) ⇔
     IS_SOME (encode_dyn_array tv offset' vs)) ∧
  (∀offset offset' ftypes fields.
     IS_SOME (encode_struct offset ftypes fields) ⇔
     IS_SOME (encode_struct offset' ftypes fields))
Proof
  rpt conj_tac
  (* encode_tuple *)
  >- (
    Induct_on `tvs` >> simp[encode_value_def] >> rpt gen_tac >>
    Cases_on `vs` >> simp[encode_value_def, AllCaseEqs()] >>
    Cases_on `encode_value h h'` >> simp[] >>
    first_x_assum (qspecl_then [`offset + type_slot_size h`,
      `offset' + type_slot_size h`, `t`] mp_tac) >>
    Cases_on `encode_tuple (offset + type_slot_size h) tvs t` >>
    Cases_on `encode_tuple (offset' + type_slot_size h) tvs t` >> simp[]
  )
  (* encode_static_array *)
  >- (
    Induct_on `sparse` >> simp[encode_value_def] >>
    Cases >> rpt gen_tac >> simp[encode_value_def, AllCaseEqs()] >>
    Cases_on `encode_value tv r` >> simp[] >>
    first_x_assum (qspecl_then [`tv`, `offset`, `offset'`] mp_tac) >>
    Cases_on `encode_static_array tv offset sparse` >>
    Cases_on `encode_static_array tv offset' sparse` >> simp[]
  )
  (* encode_dyn_array *)
  >- (
    Induct_on `vs` >> simp[encode_value_def] >>
    rpt gen_tac >> simp[encode_value_def, AllCaseEqs()] >>
    Cases_on `encode_value tv h` >> simp[] >>
    first_x_assum (qspecl_then [`tv`, `offset + type_slot_size tv`,
      `offset' + type_slot_size tv`] mp_tac) >>
    Cases_on `encode_dyn_array tv (offset + type_slot_size tv) vs` >>
    Cases_on `encode_dyn_array tv (offset' + type_slot_size tv) vs` >> simp[]
  )
  (* encode_struct *)
  >> Induct_on `ftypes` >> simp[encode_value_def] >>
  rpt gen_tac >> Cases_on `fields` >> simp[encode_value_def, AllCaseEqs()] >>
  Cases_on `h` >> Cases_on `h'` >>
  simp[encode_value_def, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `encode_value r r'` >> simp[] >>
  first_x_assum (qspecl_then [`offset + type_slot_size r`,
    `offset' + type_slot_size r`, `t`] mp_tac) >>
  Cases_on `encode_struct (offset + type_slot_size r) ftypes t` >>
  Cases_on `encode_struct (offset' + type_slot_size r) ftypes t` >> simp[]
QED

(* Corollary: normalize IS_SOME to offset 0 *)
Theorem encode_IS_SOME_at_0[local,simp]:
  (∀offset tvs vs. IS_SOME (encode_tuple offset tvs vs) ⇔
     IS_SOME (encode_tuple 0 tvs vs)) ∧
  (∀tv offset sparse. IS_SOME (encode_static_array tv offset sparse) ⇔
     IS_SOME (encode_static_array tv 0 sparse)) ∧
  (∀tv offset vs. IS_SOME (encode_dyn_array tv offset vs) ⇔
     IS_SOME (encode_dyn_array tv 0 vs)) ∧
  (∀offset ftypes fields. IS_SOME (encode_struct offset ftypes fields) ⇔
     IS_SOME (encode_struct 0 ftypes fields))
Proof
  metis_tac[encode_IS_SOME_offset_indep]
QED

(* Helper: IS_SOME distributes over option case *)
Theorem IS_SOME_option_CASE[local,simp]:
  IS_SOME (case opt of NONE => NONE | SOME x => f x) ⇔
  IS_SOME opt ∧ IS_SOME (f (THE opt))
Proof
  Cases_on `opt` >> simp[]
QED

(* ===== Theorems ===== *)

Theorem well_formed_type_value_slot_size:
  ∀tv. well_formed_type_value tv ⇒ type_slot_size tv ≤ dimword(:256)
Proof
  Cases >> simp[well_formed_type_value_def, type_slot_size_def] >>
  rename1 `BaseTV bt` >>
  Cases_on `bt` >> simp[well_formed_type_value_def, type_slot_size_def] >>
  rename1 `BytesT bd` >>
  Cases_on `bd` >> simp[well_formed_type_value_def, type_slot_size_def]
QED

Theorem within_int_bound_unsigned_well_formed:
  within_int_bound (Unsigned b) i ∧ b ≤ 256 ⇒
  well_formed_value (IntV (Unsigned b) i)
Proof
  rw[within_int_bound_def, well_formed_value_def] >>
  `Num i < dimword(:256)` by (
    simp[wordsTheory.dimword_def] >>
    `dimindex(:256) = 256` by EVAL_TAC >>
    irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
    qexists_tac `2 ** b` >> simp[]) >>
  `&(Num i) = i` by simp[integerTheory.INT_OF_NUM] >>
  pop_assum (SUBST_ALL_TAC o SYM) >> gvs[]
QED

Theorem within_int_bound_signed_well_formed:
  within_int_bound (Signed b) i ∧ b ≤ 256 ⇒
  well_formed_value (IntV (Signed b) i)
Proof
  strip_tac >>
  gvs[within_int_bound_def, well_formed_value_def] >>
  Cases_on `i < 0` >> gvs[]
  >- (
    `0 ≤ -i` by simp[integerTheory.INT_NEG_GE0, integerTheory.INT_LT_IMP_LE] >>
    `i = -&(Num (-i))` by (
      `&(Num(-i)) = -i` by simp[integerTheory.INT_OF_NUM] >> simp[]) >>
    pop_assum SUBST1_TAC >>
    `Num (-i) ≤ 2 ** 255` by (
      irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `2 ** (b − 1)` >> simp[]) >>
    simp[] >> gvs[])
  >> (
    `0 ≤ i` by fs[integerTheory.INT_NOT_LT] >>
    `i = &(Num i)` by simp[integerTheory.INT_OF_NUM] >>
    pop_assum SUBST1_TAC >>
    `Num i < 2 ** 255` by (
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `2 ** (b − 1)` >> simp[]) >>
    simp[] >> gvs[])
QED

Theorem value_has_type_equiv:
  (∀tv v. value_has_type tv v ⇒ IS_SOME (encode_value tv v)) ∧
  (∀tvs vs. values_have_types tvs vs ⇒ IS_SOME (encode_tuple 0 tvs vs)) ∧
  (∀tv sparse. sparse_has_type tv sparse ⇒
     IS_SOME (encode_static_array tv 0 sparse)) ∧
  (∀tv vs. all_have_type tv vs ⇒ IS_SOME (encode_dyn_array tv 0 vs)) ∧
  (∀ftypes fields. struct_has_type ftypes fields ⇒
     IS_SOME (encode_struct 0 ftypes fields))
Proof
  ho_match_mp_tac value_has_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[value_has_type_def, encode_value_def, encode_base_to_slot_def,
       encode_dyn_bytes_slots_def, AllCaseEqs(), COND_RAND, COND_RATOR,
       LET_THM] >>
  TRY (strip_tac >> metis_tac[]) >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd`) >>
  simp[encode_value_def]
QED
