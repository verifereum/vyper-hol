(*
 * vyperTypingScript.sml
 *
 * Type-value compatibility predicates for Vyper values and typed_values.
 *
 * TOP-LEVEL:
 *   value_has_type_def - value matches a typed_value
 *   value_has_type_equiv - equivalence with encode_value IS_SOME
 *   well_formed_type_value_def - well-formedness of typed_value descriptors
 *   value_has_type_inv - inversion lemma for value_has_type

 *   all_have_type_EVERY - all_have_type as EVERY
 *   sparse_has_type_enumerate - enumerate_static_array preserves sparse_has_type
 *)

Theory vyperTyping
Ancestors
  vyperStorage vyperValue vyperMisc
  vyperState[ignore_grammar] list sorting
Libs
  wordsLib

(* leaf_type: the type at the leaf of a subscript chain *)
Definition leaf_type_def:
  leaf_type tv [] = tv /\
  leaf_type (ArrayTV t _) (_ :: rest) = leaf_type t rest /\
  leaf_type (StructTV l) (vyperState$AttrSubscript id :: rest) =
    (case ALOOKUP l id of SOME t => leaf_type t rest | NONE => NoneTV) /\
  leaf_type _ (_ :: _) = NoneTV
End

(* Well-formedness of type_values for storage operations.
   Ensures type_slot_size tv ≤ dimword(:256) for all well-formed types. *)
Definition well_formed_type_value_def:
  well_formed_type_value (BaseTV (BytesT (Fixed n))) = (n ≤ 32) ∧
  well_formed_type_value (BaseTV (BytesT (Dynamic n))) =
    (n < dimword(:256) ∧
     type_slot_size (BaseTV (BytesT (Dynamic n))) ≤ dimword(:256)) ∧
  well_formed_type_value (BaseTV (StringT n)) =
    (n < dimword(:256) ∧
     type_slot_size (BaseTV (StringT n)) ≤ dimword(:256)) ∧
  well_formed_type_value (TupleTV tvs) =
    (EVERY well_formed_type_value tvs ∧
     type_slot_size (TupleTV tvs) ≤ dimword(:256)) ∧
  well_formed_type_value (ArrayTV tv b) =
    (0 < type_slot_size tv ∧ well_formed_type_value tv ∧
     type_slot_size (ArrayTV tv b) ≤ dimword(:256)) ∧
  well_formed_type_value (StructTV fields) =
    (EVERY (well_formed_type_value o SND) fields ∧
     type_slot_size (StructTV fields) ≤ dimword(:256)) ∧
  well_formed_type_value (BaseTV (UintT m)) = (m ≤ 256) ∧
  well_formed_type_value (BaseTV (IntT m)) = (0 < m ∧ m ≤ 256) ∧
  well_formed_type_value (FlagTV m) = (m ≤ 256) ∧
  well_formed_type_value _ = T
End

Theorem evaluate_type_well_formed:
  (!tenv ty tv. evaluate_type tenv ty = SOME tv ==>
    well_formed_type_value tv) /\
  (!tenv tys acc tvs. evaluate_types tenv tys acc = SOME tvs ==>
    EVERY well_formed_type_value acc ==>
    EVERY well_formed_type_value tvs)
Proof
  ho_match_mp_tac evaluate_type_ind
  >> simp[evaluate_type_def, AllCaseEqs(), well_formed_type_value_def,
          PULL_EXISTS]
  >> rpt strip_tac >> gvs[well_formed_type_value_def]
  >> res_tac >> gvs[]
  >> gvs[EVERY_MEM, MEM_ZIP, PULL_EXISTS, EL_MAP]
  >> gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF]
  >> gvs[ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, PULL_EXISTS]
QED

(* ===== value_has_type: structural characterization of encode_value success ===== *)

Definition value_has_type_def:
  (* Unsigned integer *)
  value_has_type (BaseTV (UintT m)) (IntV i) =
    (0 ≤ i ∧ Num i < 2 ** m ∧ m ≤ 256) ∧
  (* Signed integer *)
  value_has_type (BaseTV (IntT m)) (IntV i) =
    (within_int_bound (Signed m) i ∧ m ≤ 256) ∧
  (* Decimal *)
  value_has_type (BaseTV DecimalT) (DecimalV d) =
    within_int_bound (Signed 168) d ∧
  (* Boolean *)
  value_has_type (BaseTV BoolT) (BoolV _) = T ∧
  (* Address *)
  value_has_type (BaseTV AddressT) (BytesV bs) =
    (LENGTH bs = 20) ∧
  (* Fixed bytes *)
  value_has_type (BaseTV (BytesT (Fixed n))) (BytesV bs) =
    (LENGTH bs = n ∧ n ≤ 32) ∧
  (* Dynamic bytes *)
  value_has_type (BaseTV (BytesT (Dynamic max))) (BytesV bs) =
    (LENGTH bs ≤ max) ∧
  (* String *)
  value_has_type (BaseTV (StringT max)) (StringV s) =
    (LENGTH s ≤ max) ∧
  (* Flag *)
  value_has_type (FlagTV m') (FlagV k) = (k < 2 ** m' ∧ m' ≤ 256) ∧
  (* None *)
  value_has_type NoneTV NoneV = T ∧
  (* Tuple *)
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) =
    values_have_types tvs vs ∧
  (* Static array *)
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) =
    (SORTED $< (MAP FST sparse) ∧ sparse_has_type tv n sparse) ∧
  (* Dynamic array *)
  value_has_type (ArrayTV tv (Dynamic max)) (ArrayV (DynArrayV vs)) =
    (LENGTH vs ≤ max ∧ all_have_type tv vs) ∧
  (* Struct *)
  value_has_type (StructTV ftypes) (StructV fields) =
    struct_has_type ftypes fields ∧
  (* Default: mismatch *)
  value_has_type _ _ = F ∧

  values_have_types [] [] = T ∧
  values_have_types (tv::tvs) (v::vs) =
    (value_has_type tv v ∧ values_have_types tvs vs) ∧
  values_have_types _ _ = F ∧

  sparse_has_type tv n [] = T ∧
  sparse_has_type tv n ((k:num,v)::rest) =
    (k < n ∧ v ≠ default_value tv ∧ value_has_type tv v ∧ sparse_has_type tv n rest) ∧

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
    | INR (INR (INL (_, _, sparse))) =>
        list_size (pair_size (λx. 0) value_size) sparse
    | INR (INR (INR (INL (_, vs)))) => list_size value_size vs
    | INR (INR (INR (INR (_, fields)))) =>
        list_size (pair_size (λx. 0) value_size) fields)` >>
  rpt conj_tac >>
  TRY (Induct >> simp[basicSizeTheory.pair_size_def] >>
       Cases >> simp[basicSizeTheory.pair_size_def] >> NO_TAC) >>
  Induct_on `sparse` >> simp[basicSizeTheory.pair_size_def] >>
  Cases >> simp[basicSizeTheory.pair_size_def]
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

Theorem value_has_type_equiv:
  (∀tv v. value_has_type tv v ⇒ IS_SOME (encode_value tv v)) ∧
  (∀tvs vs. values_have_types tvs vs ⇒ IS_SOME (encode_tuple 0 tvs vs)) ∧
  (∀tv n sparse. sparse_has_type tv n sparse ⇒
     IS_SOME (encode_static_array tv 0 sparse)) ∧
  (∀tv vs. all_have_type tv vs ⇒ IS_SOME (encode_dyn_array tv 0 vs)) ∧
  (∀ftypes fields. struct_has_type ftypes fields ⇒
     IS_SOME (encode_struct 0 ftypes fields))
Proof
  ho_match_mp_tac value_has_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[value_has_type_def, encode_value_def, encode_base_to_slot_def,
       encode_dyn_bytes_slots_def, AllCaseEqs(), COND_RAND, COND_RATOR,
       LET_THM] >>
  TRY (strip_tac >> metis_tac[])
QED

(* ===== Derived typing properties ===== *)

Theorem all_have_type_EVERY:
  ∀tv vs. all_have_type tv vs ⇔ EVERY (value_has_type tv) vs
Proof
  gen_tac >> Induct >> simp[value_has_type_def]
QED

Theorem sparse_has_type_enumerate:
  ∀vs tv d n i. EVERY (value_has_type tv) vs ∧ i + LENGTH vs ≤ n ∧ d = default_value tv ⇒
    sparse_has_type tv n (enumerate_static_array d i vs)
Proof
  Induct >> simp[enumerate_static_array_def, value_has_type_def, LET_THM] >>
  rpt strip_tac >> rw[] >> simp[value_has_type_def]
QED

Theorem default_value_has_type[local]:
  (∀tv. well_formed_type_value tv ⇒ value_has_type tv (default_value tv)) ∧
  (∀ftypes. EVERY (well_formed_type_value o SND) ftypes ⇒
    struct_has_type ftypes (MAP (λ(id,t). (id, default_value t)) ftypes)) ∧
  (∀p : string # type_value. well_formed_type_value (SND p) ⇒
    value_has_type (SND p) (default_value (SND p))) ∧
  (∀tvs. EVERY well_formed_type_value tvs ⇒
    values_have_types tvs (MAP default_value tvs))
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:type_value``) >>
  simp[default_value_def, default_value_tuple_MAP,
       default_value_struct_MAP, value_has_type_def,
       well_formed_type_value_def, within_int_bound_def] >>
  rpt conj_tac >> rpt gen_tac >> simp[] >|
  [(* BaseTV b *)
   Cases_on `b` >> simp[default_value_def, value_has_type_def,
     well_formed_type_value_def, within_int_bound_def] >>
   TRY (Cases_on `b'` >> simp[default_value_def, value_has_type_def,
        well_formed_type_value_def]) ,
   (* TupleTV tvs - IH *)
   strip_tac >> metis_tac[] ,
   (* ArrayTV tv b *)
   strip_tac >> Cases_on `b` >>
   simp[default_value_def, value_has_type_def, all_have_type_EVERY] ,
   (* StructTV ftypes - IH *)
   strip_tac >> metis_tac[] ,
   (* struct cons: p::ftypes *)
   PairCases_on `p` >> simp[value_has_type_def]
  ]
QED

Theorem default_value_well_typed:
  ∀tv. well_formed_type_value tv ⇒ value_has_type tv (default_value tv)
Proof
  metis_tac[default_value_has_type]
QED

Theorem value_has_type_inv:
  (value_has_type tv NoneV ⇔ tv = NoneTV) ∧
  (value_has_type tv (BoolV b) ⇔ tv = BaseTV BoolT) ∧
  (value_has_type tv (IntV i) ⇔
    (∃n. tv = BaseTV (UintT n) ∧ 0 ≤ i ∧ Num i < 2 ** n ∧ n ≤ 256) ∨
    (∃n. tv = BaseTV (IntT n) ∧ within_int_bound (Signed n) i ∧ n ≤ 256)) ∧
  (value_has_type tv (DecimalV d) ⇔
    tv = BaseTV DecimalT ∧ within_int_bound (Signed 168) d) ∧
  (value_has_type tv (FlagV k) ⇔ ∃m. tv = FlagTV m ∧ k < 2 ** m ∧ m ≤ 256) ∧
  (value_has_type tv (StringV s) ⇔
    ∃m. tv = BaseTV (StringT m) ∧ LENGTH s ≤ m) ∧
  (value_has_type tv (BytesV bs) ⇔
    (tv = BaseTV AddressT ∧ LENGTH bs = 20) ∨
    (∃n. tv = BaseTV (BytesT (Fixed n)) ∧ LENGTH bs = n ∧ n ≤ 32) ∨
    (∃m. tv = BaseTV (BytesT (Dynamic m)) ∧ LENGTH bs ≤ m)) ∧
  (value_has_type tv (ArrayV (TupleV vs)) ⇔
    ∃tvs. tv = TupleTV tvs ∧ values_have_types tvs vs) ∧
  (value_has_type tv (ArrayV (SArrayV sp)) ⇔
    ∃tv0 n. tv = ArrayTV tv0 (Fixed n) ∧ SORTED $< (MAP FST sp) ∧
            sparse_has_type tv0 n sp) ∧
  (value_has_type tv (ArrayV (DynArrayV vs)) ⇔
    ∃tv0 m. tv = ArrayTV tv0 (Dynamic m) ∧ LENGTH vs ≤ m ∧ all_have_type tv0 vs) ∧
  (value_has_type tv (StructV fields) ⇔
    ∃ftypes. tv = StructTV ftypes ∧ struct_has_type ftypes fields)
Proof
  rpt conj_tac >>
  Cases_on `tv` >> simp[value_has_type_def] >>
  TRY (Cases_on `b` >> simp[value_has_type_def] >>
       TRY (Cases_on `b'` >> simp[value_has_type_def]) >> NO_TAC) >>
  TRY (Cases_on `b'` >> simp[value_has_type_def] >> NO_TAC) >>
  Cases_on `b` >> simp[value_has_type_def, EQ_IMP_THM] >> rpt strip_tac >> gvs[]
QED

(* Helper: values_have_types transfer, assuming element-wise transfer *)

