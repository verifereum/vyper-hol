Theory vyperLookupStorage

Ancestors
  vyperLookup vyperMisc vyperContext vyperState vyperStorage vyperInterpreter
  vyperValue vyperValueOperation vyperTyping vyperEncodeDecode
Libs
  wordsLib

Definition lookup_toplevel_name_def:
  lookup_toplevel_name cx st mid n =
  case lookup_global cx mid (string_to_num n) st of
  | (INL v, st) => SOME v
  | _ => NONE
End

Definition update_toplevel_name_def:
  update_toplevel_name cx st mid n v =
  SND (set_global cx mid (string_to_num n) v st)
End

Definition lookup_toplevel_name_target_def:
  lookup_toplevel_name_target cx st n = lookup_base_target cx st (TopLevelNameTarget n)
End

Definition var_in_storage_def:
  var_in_storage cx mid n ⇔
  ∃code b t id offset tv.
    get_module_code cx mid = SOME code ∧
    find_var_decl_by_num (string_to_num n) code = SOME (StorageVarDecl b t, id) ∧
    lookup_var_slot_from_layout cx b mid id = SOME offset ∧
    offset < dimword(:256) ∧
    evaluate_type (get_tenv cx) t = SOME tv ∧
    well_formed_type_value tv
End

Definition storage_var_info_def:
  storage_var_info cx mid n =
    case get_module_code cx mid of
    | NONE => NONE
    | SOME code =>
        case find_var_decl_by_num (string_to_num n) code of
        | SOME (StorageVarDecl b t, id) =>
            (case (lookup_var_slot_from_layout cx b mid id,
                   evaluate_type (get_tenv cx) t) of
             | (SOME off, SOME tv) => SOME (b, off, tv)
             | _ => NONE)
        | _ => NONE
End

Definition storage_type_of_def:
  storage_type_of cx mid n =
    case storage_var_info cx mid n of
    | NONE => NONE
    | SOME (_, _, tv) => SOME tv
End

Definition storable_value_def:
  storable_value cx mid n v ⇔
    ∀tv. storage_type_of cx mid n = SOME tv ⇒
         value_has_type tv v
End

Definition well_formed_layout_def:
  well_formed_layout cx ⇔
    (* Non-overflow: each variable's slot range fits in the address space *)
    (∀mid n b off tv.
      storage_var_info cx mid n = SOME (b, off, tv) ⇒
      off + type_slot_size tv ≤ dimword(:256)) ∧
    (* Disjointness: distinct variables on the same backend have disjoint slots *)
    (∀mid1 n1 mid2 n2 b off1 tv1 off2 tv2.
      storage_var_info cx mid1 n1 = SOME (b, off1, tv1) ∧
      storage_var_info cx mid2 n2 = SOME (b, off2, tv2) ∧
      (mid1, n1) ≠ (mid2, n2) ⇒
      off1 + type_slot_size tv1 ≤ off2 ∨ off2 + type_slot_size tv2 ≤ off1)
End

(* Predicate: slots read during decode_value contain in-range values.
   Captures all conditions needed for decode_value to succeed and
   produce well-typed values. *)
Definition slots_in_range_def:
  slots_in_range storage offset (BaseTV (UintT n)) =
    (w2n (read_slot storage offset) < 2 ** n) ∧
  slots_in_range storage offset (BaseTV (IntT n)) =
    within_int_bound (Signed n) (w2i (read_slot storage offset)) ∧
  slots_in_range storage offset (BaseTV (BytesT (Dynamic max))) =
    (w2n (read_slot storage offset) ≤ max) ∧
  slots_in_range storage offset (BaseTV (StringT max)) =
    (w2n (read_slot storage offset) ≤ max) ∧
  slots_in_range storage offset (BaseTV DecimalT) =
    within_int_bound (Signed 168) (w2i (read_slot storage offset)) ∧
  slots_in_range storage offset (BaseTV _) = T ∧
  slots_in_range storage offset (FlagTV m) =
    (w2n (read_slot storage offset) < 2 ** m) ∧
  slots_in_range storage offset NoneTV = T ∧
  slots_in_range storage offset (TupleTV tvs) =
    tuple_slots_in_range storage offset tvs ∧
  slots_in_range storage offset (ArrayTV tv (Fixed n)) =
    static_slots_in_range storage offset tv n ∧
  slots_in_range storage offset (ArrayTV tv (Dynamic max)) =
    (let len = w2n (read_slot storage offset) in
       if len ≤ max then
         dyn_slots_in_range storage (offset + 1) tv (MIN len max)
       else F) ∧
  slots_in_range storage offset (StructTV ftypes) =
    struct_slots_in_range storage offset ftypes ∧
  tuple_slots_in_range storage offset [] = T ∧
  tuple_slots_in_range storage offset (tv::tvs) =
    (slots_in_range storage offset tv ∧
     tuple_slots_in_range storage (offset + type_slot_size tv) tvs) ∧
  static_slots_in_range storage offset tv 0 = T ∧
  static_slots_in_range storage offset tv (SUC n) =
    (slots_in_range storage offset tv ∧
     static_slots_in_range storage (offset + type_slot_size tv) tv n) ∧
  dyn_slots_in_range storage offset tv 0 = T ∧
  dyn_slots_in_range storage offset tv (SUC n) =
    (slots_in_range storage offset tv ∧
     dyn_slots_in_range storage (offset + type_slot_size tv) tv n) ∧
  struct_slots_in_range storage offset [] = T ∧
  struct_slots_in_range storage offset ((fname,tv)::ftypes) =
    (slots_in_range storage offset tv ∧
     struct_slots_in_range storage (offset + type_slot_size tv) ftypes)
Termination
  WF_REL_TAC `measure (λx. case x of
    | INL (_, _, tv) => type_value_size tv
    | INR (INL (_, _, tvs)) => list_size type_value_size tvs
    | INR (INR (INL (_, _, tv, n))) => type_value_size tv + n
    | INR (INR (INR (INL (_, _, tv, n)))) => type_value_size tv + n
    | INR (INR (INR (INR (_, _, ftypes)))) =>
        list_size (pair_size (list_size char_size) type_value_size) ftypes)` >>
  simp[basicSizeTheory.pair_size_def, arithmeticTheory.MIN_DEF]
End

(* Per-variable invariant: storage slots for variable n are in range *)
Definition storage_var_in_range_def:
  storage_var_in_range cx st mid n ⇔
    ∀is_transient off tv storage st'.
      storage_var_info cx mid n = SOME (is_transient, off, tv) ∧
      get_storage_backend cx is_transient st = (INL storage, st') ⇒
      slots_in_range storage off tv
End

(* State invariant: all storage slots contain values in range for their types *)
Definition well_formed_storage_def:
  well_formed_storage cx st ⇔
    ∀mid n. storage_var_in_range cx st mid n
End

(* =================== Global Storage ============================= *)

Theorem storage_var_info_SOME_storage_type_of:
  storage_var_info cx mid n = SOME (b, off, tv) ⇒
  storage_type_of cx mid n = SOME tv
Proof
  simp[storage_type_of_def]
QED

Theorem storage_type_of_SOME_storage_var_info:
  storage_type_of cx mid n = SOME tv ⇒
  ∃b off. storage_var_info cx mid n = SOME (b, off, tv)
Proof
  simp[storage_type_of_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

(* ===== decode_value produces typed, well-formed values ===== *)

Theorem LENGTH_word_to_bytes_be_256[local]:
  LENGTH (word_to_bytes_be (w : bytes32)) = 32
Proof
  simp[byteTheory.word_to_bytes_be_def, byteTheory.LENGTH_word_to_bytes]
QED

(* wf_values_EVERY and wf_fields_EVERY removed: value_has_type subsumes well_formed_value *)

Theorem LENGTH_slots_to_bytes[local]:
  ∀n slots. LENGTH (slots_to_bytes n slots) ≤ n
Proof
  ho_match_mp_tac slots_to_bytes_ind >>
  simp[slots_to_bytes_def, LET_THM,
       listTheory.LENGTH_TAKE_EQ, LENGTH_word_to_bytes_be_256] >>
  rpt strip_tac >>
  Cases_on `32 ≤ SUC v4` >> gvs[arithmeticTheory.MIN_DEF]
QED

Theorem decode_dyn_bytes_LENGTH[local]:
  ∀storage offset max bs.
    decode_dyn_bytes storage offset max = SOME bs ⇒ LENGTH bs ≤ max
Proof
  rpt gen_tac >>
  simp[decode_dyn_bytes_def, LET_THM, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `w2n (lookup_storage (n2w offset) storage)` >> simp[] >>
  irule LENGTH_slots_to_bytes
QED

Theorem SORTED_enumerate_static_array[local]:
  ∀d i vs. SORTED $< (MAP FST (enumerate_static_array d i vs))
Proof
  gen_tac >> Induct_on `vs` >>
  simp[enumerate_static_array_def, LET_THM] >>
  rpt strip_tac >> rw[] >>
  simp[sortingTheory.less_sorted_eq, listTheory.MEM_MAP,
       PULL_EXISTS, pairTheory.FORALL_PROD,
       MEM_enumerate_static_array_iff]
QED

(* wf_sparse_enumerate removed: value_has_type subsumes well_formed_value *)

Theorem LENGTH_decode_static_array[local]:
  ∀storage offset tv n vs.
    decode_static_array storage offset tv n = SOME vs ⇒ LENGTH vs = n
Proof
  Induct_on `n` >>
  simp[decode_value_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> res_tac
QED

Theorem LENGTH_decode_dyn_array[local]:
  ∀storage offset tv n vs.
    decode_dyn_array storage offset tv n = SOME vs ⇒ LENGTH vs = n
Proof
  Induct_on `n` >>
  simp[decode_value_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> res_tac
QED

Theorem var_in_storage_storage_var_info:
  var_in_storage cx mid n ⇒
  ∃b off tv.
    storage_var_info cx mid n = SOME (b, off, tv) ∧
    well_formed_type_value tv
Proof
  rw[var_in_storage_def, storage_var_info_def] >> gvs[]
QED

Theorem var_in_storage_has_type:
  var_in_storage cx mid n ⇒ IS_SOME (storage_type_of cx mid n)
Proof
  strip_tac >> drule var_in_storage_storage_var_info >> strip_tac >>
  simp[storage_type_of_def]
QED

Theorem var_in_storage_well_formed_type:
  var_in_storage cx mid n ∧ storage_type_of cx mid n = SOME tv ⇒
  well_formed_type_value tv
Proof
  strip_tac >>
  drule var_in_storage_storage_var_info >> strip_tac >>
  gvs[storage_type_of_def]
QED

Theorem decode_value_storable[local]:
  (∀storage offset tv v.
    well_formed_type_value tv ∧
    slots_in_range storage offset tv ∧
    decode_value storage offset tv = SOME v ⇒
    value_has_type tv v) ∧
  (∀storage offset tvs vs.
    EVERY well_formed_type_value tvs ∧
    tuple_slots_in_range storage offset tvs ∧
    decode_tuple storage offset tvs = SOME vs ⇒
    values_have_types tvs vs) ∧
  (∀storage offset tv n vs.
    well_formed_type_value tv ∧
    static_slots_in_range storage offset tv n ∧
    decode_static_array storage offset tv n = SOME vs ⇒
    EVERY (value_has_type tv) vs) ∧
  (∀storage offset tv n vs.
    well_formed_type_value tv ∧
    dyn_slots_in_range storage offset tv n ∧
    decode_dyn_array storage offset tv n = SOME vs ⇒
    EVERY (value_has_type tv) vs) ∧
  (∀storage offset ftypes fields.
    EVERY (well_formed_type_value o SND) ftypes ∧
    struct_slots_in_range storage offset ftypes ∧
    decode_struct storage offset ftypes = SOME fields ⇒
    struct_has_type ftypes fields)
Proof
  ho_match_mp_tac decode_value_ind >>
  rpt conj_tac >> rpt gen_tac >>
  strip_tac >> gvs[decode_value_def, decode_base_from_slot_def,
    AllCaseEqs(), value_has_type_def,
    wordsTheory.w2n_lt, integer_wordTheory.w2i_le,
    integer_wordTheory.w2i_ge, LENGTH_word_to_bytes_be_256] >>
  rpt strip_tac >>
  gvs[value_has_type_def,
      well_formed_type_value_def, within_int_bound_def,
      listTheory.LENGTH_TAKE_EQ, LENGTH_word_to_bytes_be_256,
      all_have_type_EVERY,
      slots_in_range_def] >>
  TRY (metis_tac[decode_dyn_bytes_LENGTH]) >>
  TRY (imp_res_tac LENGTH_decode_static_array >>
       simp[sparse_has_type_enumerate, SORTED_enumerate_static_array] >>
       NO_TAC) >>
  imp_res_tac LENGTH_decode_dyn_array >> simp[]
QED

(* Helper: sparse_has_type on enumerate implies EVERY on the original list,
   given that the default value has the type. *)
Theorem sparse_has_type_enumerate_EVERY_back[local]:
  ∀vs tv n d i.
    sparse_has_type tv n (enumerate_static_array d i vs) ∧
    value_has_type tv d ⇒
    EVERY (value_has_type tv) vs
Proof
  Induct >> simp[enumerate_static_array_def, LET_THM] >>
  rpt gen_tac >> rw[] >> gvs[value_has_type_def] >>
  metis_tac[]
QED

(* Converse of decode_value_storable for the slots_in_range direction:
   if decode_value succeeds and the result has the right type,
   then the slots were in range. *)
Theorem decode_value_typed_slots_in_range[local]:
  (∀storage offset tv v.
    well_formed_type_value tv ∧
    decode_value storage offset tv = SOME v ∧
    value_has_type tv v ⇒
    slots_in_range storage offset tv) ∧
  (∀storage offset tvs vs.
    EVERY well_formed_type_value tvs ∧
    decode_tuple storage offset tvs = SOME vs ∧
    values_have_types tvs vs ⇒
    tuple_slots_in_range storage offset tvs) ∧
  (∀storage offset tv n vs.
    well_formed_type_value tv ∧
    decode_static_array storage offset tv n = SOME vs ∧
    EVERY (value_has_type tv) vs ⇒
    static_slots_in_range storage offset tv n) ∧
  (∀storage offset tv n vs.
    well_formed_type_value tv ∧
    decode_dyn_array storage offset tv n = SOME vs ∧
    EVERY (value_has_type tv) vs ⇒
    dyn_slots_in_range storage offset tv n) ∧
  (∀storage offset ftypes fields.
    EVERY (well_formed_type_value o SND) ftypes ∧
    decode_struct storage offset ftypes = SOME fields ∧
    struct_has_type ftypes fields ⇒
    struct_slots_in_range storage offset ftypes)
Proof
  ho_match_mp_tac decode_value_ind >>
  rpt conj_tac >> rpt gen_tac >>
  strip_tac >> gvs[decode_value_def, decode_base_from_slot_def,
    AllCaseEqs(), value_has_type_def, slots_in_range_def,
    read_slot_def, all_have_type_EVERY, well_formed_type_value_def] >>
  rpt strip_tac >> gvs[value_has_type_def, slots_in_range_def,
    all_have_type_EVERY, well_formed_type_value_def, ETA_AX] >>
  TRY (gvs[decode_dyn_bytes_def, LET_THM, AllCaseEqs()] >> NO_TAC) >>
  TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
  `value_has_type tv (default_value tv)` by
    (irule default_value_well_typed >> simp[]) >>
  drule_all sparse_has_type_enumerate_EVERY_back >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem slots_in_range_offset_cong[local]:
  (∀storage off1 tv off2.
    (n2w off1 : bytes32) = n2w off2 ⇒
    slots_in_range storage off1 tv = slots_in_range storage off2 tv) ∧
  (∀storage off1 tvs off2.
    (n2w off1 : bytes32) = n2w off2 ⇒
    tuple_slots_in_range storage off1 tvs =
    tuple_slots_in_range storage off2 tvs) ∧
  (∀storage off1 tv n off2.
    (n2w off1 : bytes32) = n2w off2 ⇒
    static_slots_in_range storage off1 tv n =
    static_slots_in_range storage off2 tv n) ∧
  (∀storage off1 tv n off2.
    (n2w off1 : bytes32) = n2w off2 ⇒
    dyn_slots_in_range storage off1 tv n =
    dyn_slots_in_range storage off2 tv n) ∧
  (∀storage off1 ftypes off2.
    (n2w off1 : bytes32) = n2w off2 ⇒
    struct_slots_in_range storage off1 ftypes =
    struct_slots_in_range storage off2 ftypes)
Proof
  ho_match_mp_tac slots_in_range_ind >>
  rpt conj_tac >> rpt gen_tac >>
  DISCH_TAC >> rpt gen_tac >> TRY DISCH_TAC >>
  `read_slot storage off1 = read_slot storage off2`
    by simp[read_slot_def] >>
  PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  (* Base cases + simple IH: solve via read_slot equality or drule *)
  TRY (gvs[] >> NO_TAC) >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  (* Recursive cases with conjunction IH *)
  TRY (
    qpat_x_assum `_ ∧ _` strip_assume_tac >>
    `(n2w (off1 + type_slot_size tv) : bytes32) = n2w (off2 + type_slot_size tv)`
      by (gvs[wordsTheory.n2w_11] >>
          simp[Once (GSYM arithmeticTheory.MOD_PLUS)]) >>
    first_x_assum drule >> first_x_assum drule >>
    simp[] >> NO_TAC) >>
  (* DynArray case *)
  Cases_on `w2n (read_slot storage off1) ≤ max` >- (
    `(n2w (off1 + 1) : bytes32) = n2w (off2 + 1)`
      by (gvs[wordsTheory.n2w_11] >>
          simp[Once (GSYM arithmeticTheory.MOD_PLUS)]) >>
    qpat_x_assum `∀len. _`
      (qspec_then `w2n (read_slot storage off1)` mp_tac) >>
    asm_rewrite_tac[] >> strip_tac >>
    pop_assum (qspec_then `off2 + 1` mp_tac) >>
    simp[] >> gvs[]
  ) >>
  gvs[]
QED

Theorem slots_in_range_w2n_n2w[local]:
  ∀storage off tv.
    slots_in_range storage (w2n ((n2w off):bytes32)) tv ⇒
    slots_in_range storage off tv
Proof
  rpt strip_tac >>
  `slots_in_range storage off tv =
   slots_in_range storage (w2n ((n2w off):bytes32)) tv` by
    (irule (CONJUNCT1 slots_in_range_offset_cong) >> simp[]) >>
  gvs[]
QED

Theorem storage_var_in_range_from_typed_lookup:
  ∀cx st mid n v tv.
    well_formed_type_value tv ∧
    storage_type_of cx mid n = SOME tv ∧
    lookup_toplevel_name cx st mid n = SOME (Value v) ∧
    value_has_type tv v ⇒
    storage_var_in_range cx st mid n
Proof
  rpt strip_tac >>
  simp[storage_var_in_range_def] >> rpt strip_tac >>
  `tv = tv'` by gvs[storage_type_of_def, storage_var_info_def, AllCaseEqs()] >>
  gvs[] >>
  (* Extract storage_var_info components from storage_type_of *)
  gvs[storage_type_of_def, storage_var_info_def, AllCaseEqs()] >>
  (* Now unfold lookup *)
  qpat_x_assum `lookup_toplevel_name _ _ _ _ = _` mp_tac >>
  simp[lookup_toplevel_name_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[Once lookup_global_def, bind_def, return_def, LET_THM,
       lift_option_type_def, read_storage_slot_def, lift_option_def,
       raise_def, AllCaseEqs()] >>
  Cases_on `tv` >>
  simp[bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[return_def, raise_def] >>
  irule slots_in_range_w2n_n2w >>
  irule (CONJUNCT1 decode_value_typed_slots_in_range) >>
  simp[]
QED

(* ===== Totality of decode_value under slots_in_range ===== *)

Theorem decode_value_total[local]:
  (∀storage offset tv.
    well_formed_type_value tv ∧
    slots_in_range storage offset tv ⇒
    ∃v. decode_value storage offset tv = SOME v) ∧
  (∀storage offset tvs.
    EVERY well_formed_type_value tvs ∧
    tuple_slots_in_range storage offset tvs ⇒
    ∃vs. decode_tuple storage offset tvs = SOME vs) ∧
  (∀storage offset tv n.
    well_formed_type_value tv ∧
    static_slots_in_range storage offset tv n ⇒
    ∃vs. decode_static_array storage offset tv n = SOME vs) ∧
  (∀storage offset tv n.
    well_formed_type_value tv ∧
    dyn_slots_in_range storage offset tv n ⇒
    ∃vs. decode_dyn_array storage offset tv n = SOME vs) ∧
  (∀storage offset ftypes.
    EVERY (well_formed_type_value o SND) ftypes ∧
    struct_slots_in_range storage offset ftypes ⇒
    ∃fields. decode_struct storage offset ftypes = SOME fields)
Proof
  ho_match_mp_tac decode_value_ind >>
  rpt conj_tac >> rpt gen_tac >>
  strip_tac >> gvs[decode_value_def, slots_in_range_def,
    well_formed_type_value_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> gvs[slots_in_range_def] >>
  TRY (fs[decode_dyn_bytes_def, LET_THM, read_slot_def] >> NO_TAC) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  metis_tac[]
QED

(* ===== Inverse: storage_var_in_range implies typed lookup succeeds ===== *)

Theorem typed_lookup_from_storage_var_in_range_non_array:
  ∀cx st mid n tv.
    var_in_storage cx mid n ∧
    storage_var_in_range cx st mid n ∧
    storage_type_of cx mid n = SOME tv ∧
    (∀elem bd. tv ≠ ArrayTV elem bd) ⇒
    ∃v.
      lookup_toplevel_name cx st mid n = SOME (Value v) ∧
      value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[var_in_storage_def] >>
  (* Unify type variables *)
  `tv' = tv`
    by gvs[storage_type_of_def, storage_var_info_def, AllCaseEqs()] >>
  gvs[] >>
  (* Get storage and slots_in_range from storage_var_in_range *)
  `∃storage. get_storage_backend cx b st = (INL storage, st) ∧
             slots_in_range storage offset tv`
    by (qpat_x_assum `storage_var_in_range _ _ _ _` mp_tac >>
        simp[storage_var_in_range_def, storage_var_info_def, AllCaseEqs()] >>
        strip_tac >>
        Cases_on `b` >>
        fs[get_storage_backend_def, get_accounts_def,
           get_transient_storage_def, bind_def, return_def] >>
        first_x_assum irule >>
        simp[get_storage_backend_def, get_accounts_def,
             get_transient_storage_def, bind_def, return_def]) >>
  (* decode_value succeeds *)
  `w2n ((n2w offset):bytes32) = offset` by simp[wordsTheory.w2n_n2w] >>
  `∃v. decode_value storage offset tv = SOME v`
    by (irule (CONJUNCT1 decode_value_total) >> simp[]) >>
  (* Get typing *)
  `value_has_type tv v`
    by metis_tac[CONJUNCT1 decode_value_storable] >>
  (* Show lookup succeeds *)
  qexists_tac `v` >> simp[] >>
  simp[lookup_toplevel_name_def, Once lookup_global_def, bind_def,
       return_def, LET_THM, lift_option_type_def, lift_option_def,
       read_storage_slot_def, get_storage_backend_def,
       get_accounts_def, get_transient_storage_def] >>
  Cases_on `tv` >> gvs[] >>
  simp[bind_def, return_def, lift_option_def]
QED

(* Helper: get_storage_backend always succeeds *)
Theorem get_storage_backend_INL[local]:
  ∀cx b st. ∃storage. get_storage_backend cx b st = (INL storage, st)
Proof
  rpt gen_tac >> Cases_on `b` >>
  simp[get_storage_backend_def, get_accounts_def,
       get_transient_storage_def, bind_def, return_def]
QED

(* Helper: extract slots_in_range from storage_var_in_range *)
Theorem storage_var_in_range_slots[local]:
  ∀cx st mid n b offset tv storage.
    storage_var_in_range cx st mid n ∧
    storage_var_info cx mid n = SOME (b, offset, tv) ∧
    get_storage_backend cx b st = (INL storage, st) ⇒
    slots_in_range storage offset tv
Proof
  rw[storage_var_in_range_def]
QED

Theorem typed_lookup_from_storage_var_in_range_array:
  ∀cx st mid n elem_tv bd.
    var_in_storage cx mid n ∧
    storage_var_in_range cx st mid n ∧
    storage_type_of cx mid n = SOME (ArrayTV elem_tv bd) ⇒
    ∃ref_v v.
      lookup_toplevel_name cx st mid n = SOME ref_v ∧
      FST (materialise cx ref_v st) = INL v ∧
      value_has_type (ArrayTV elem_tv bd) v
Proof
  rpt strip_tac >>
  gvs[var_in_storage_def] >>
  `tv = ArrayTV elem_tv bd`
    by gvs[storage_type_of_def, storage_var_info_def, AllCaseEqs()] >>
  gvs[] >>
  `storage_var_info cx mid n = SOME (b, offset, ArrayTV elem_tv bd)`
    by simp[storage_var_info_def] >>
  `∃storage. get_storage_backend cx b st = (INL storage, st)`
    by metis_tac[get_storage_backend_INL] >>
  `slots_in_range storage offset (ArrayTV elem_tv bd)`
    by metis_tac[storage_var_in_range_slots] >>
  `w2n ((n2w offset):bytes32) = offset` by simp[wordsTheory.w2n_n2w] >>
  `∃v. decode_value storage offset (ArrayTV elem_tv bd) = SOME v`
    by (irule (CONJUNCT1 decode_value_total) >> simp[]) >>
  `value_has_type (ArrayTV elem_tv bd) v`
    by metis_tac[CONJUNCT1 decode_value_storable] >>
  MAP_EVERY qexists_tac [`ArrayRef b (n2w offset) elem_tv bd`, `v`] >>
  simp[] >>
  conj_tac >- (
    simp[lookup_toplevel_name_def, Once lookup_global_def, bind_def,
         return_def, LET_THM, lift_option_type_def]
  ) >>
  simp[materialise_def, read_storage_slot_def, bind_def, return_def,
       lift_option_def]
QED

Theorem storable_value_from_lookup:
  ∀cx st mid n v.
    var_in_storage cx mid n ∧
    storage_var_in_range cx st mid n ∧
    lookup_toplevel_name cx st mid n = SOME (Value v) ⇒
    storable_value cx mid n v
Proof
  rpt strip_tac >>
  rw[storable_value_def] >> rpt strip_tac >>
  gvs[var_in_storage_def] >>
  `tv = tv'` by gvs[storage_type_of_def, storage_var_info_def, AllCaseEqs()] >>
  gvs[] >>
  `well_formed_type_value tv` by metis_tac[var_in_storage_well_formed_type,
    var_in_storage_def] >>
  qpat_x_assum `lookup_toplevel_name _ _ _ _ = _` mp_tac >>
  simp[lookup_toplevel_name_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[Once lookup_global_def, bind_def, return_def, LET_THM,
       lift_option_type_def, read_storage_slot_def, lift_option_def,
       raise_def, AllCaseEqs()] >>
  `∃is_t off. storage_var_info cx mid n = SOME (is_t, off, tv)`
    by (gvs[storage_type_of_def] >>
        Cases_on `storage_var_info cx mid n` >> gvs[] >>
        PairCases_on `x` >> gvs[]) >>
  `is_t = b ∧ off = offset`
    by gvs[storage_var_info_def, AllCaseEqs()] >>
  gvs[] >>
  Cases_on `tv` >>
  simp[bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[return_def, raise_def] >> (
    qpat_x_assum `storage_var_in_range _ _ _ _` mp_tac >>
    simp[storage_var_in_range_def] >>
    strip_tac >>
    metis_tac[decode_value_storable])
QED

Theorem storable_value_same_type:
  ∀cx mid n v v' tv.
    storable_value cx mid n v ∧
    storage_type_of cx mid n = SOME tv ∧
    value_has_type tv v' ⇒
    storable_value cx mid n v'
Proof
  rw[storable_value_def]
QED

Theorem get_after_set_storage_backend[local]:
  ∀cx is_transient storage' st.
    get_storage_backend cx is_transient
      (SND (set_storage_backend cx is_transient storage' st)) =
    (INL storage', SND (set_storage_backend cx is_transient storage' st))
Proof
  Cases_on `is_transient` >>
  rw[get_storage_backend_def, set_storage_backend_def,
     bind_def, return_def, get_accounts_def, update_accounts_def,
     get_transient_storage_def, update_transient_def,
     vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
     vfmExecutionTheory.lookup_transient_storage_def,
     vfmExecutionTheory.update_transient_storage_def,
     combinTheory.APPLY_UPDATE_THM]
QED

Theorem get_after_set_other_backend[local]:
  ∀cx b1 b2 storage' st.
    b1 ≠ b2 ⇒
    FST (get_storage_backend cx b2
      (SND (set_storage_backend cx b1 storage' st))) =
    FST (get_storage_backend cx b2 st)
Proof
  Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
  simp[get_storage_backend_def, set_storage_backend_def,
       bind_def, return_def, get_accounts_def, update_accounts_def,
       get_transient_storage_def, update_transient_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def]
QED

Theorem get_storage_backend_INL[local]:
  ∀cx b st. ∃storage. get_storage_backend cx b st = (INL storage, st)
Proof
  Cases_on `b` >>
  simp[get_storage_backend_def, bind_def, return_def,
       get_accounts_def, get_transient_storage_def]
QED

Theorem lookup_toplevel_name_after_update_core[local]:
  ∀cx st mid n v.
    var_in_storage cx mid n ∧
    storable_value cx mid n v ⇒
    ∃ref_v.
      lookup_toplevel_name cx (update_toplevel_name cx st mid n v) mid n = SOME ref_v ∧
      FST (materialise cx ref_v (update_toplevel_name cx st mid n v)) = INL v ∧
      ((∀av. v ≠ ArrayV av) ⇒ ref_v = Value v)
Proof
  rpt strip_tac >>
  fs[storable_value_def] >>
  `IS_SOME (storage_type_of cx mid n)` by metis_tac[var_in_storage_has_type] >>
  Cases_on `storage_type_of cx mid n` >> gvs[] >>
  rename1 `storage_type_of cx mid n = SOME tv` >>
  `IS_SOME (encode_value tv v)` by gvs[value_has_type_equiv] >>
  `well_formed_type_value tv` by metis_tac[var_in_storage_well_formed_type] >>
  `bounds_compat tv v` by metis_tac[value_has_type_implies_bounds_compat] >>
  `encode_decode_roundtrip_ok tv v` by (irule encode_decode_roundtrip_all >> simp[]) >>
  fs[var_in_storage_def, storage_type_of_def, storage_var_info_def, AllCaseEqs()] >>
  Cases_on `encode_value tv v` >> gvs[] >>
  simp[lookup_toplevel_name_def, update_toplevel_name_def] >>
  simp[Once set_global_def, write_storage_slot_def,
       bind_def, lift_option_type_def, lift_option_def,
       return_def, LET_THM, raise_def] >>
  `∃storage0. get_storage_backend cx b st = (INL storage0, st)` by
    metis_tac[get_storage_backend_INL] >>
  simp[Once lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM, raise_def] >>
  Cases_on `tv` >>
  gvs[read_storage_slot_def, lift_option_def, bind_def,
      get_after_set_storage_backend, return_def, raise_def,
      encode_decode_roundtrip_ok_def, materialise_def] >>
  (* ArrayTV case: unfold set_global in materialise side *)
  simp[Once set_global_def, write_storage_slot_def,
       bind_def, lift_option_type_def, lift_option_def,
       return_def, LET_THM, raise_def,
       get_after_set_storage_backend] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem lookup_toplevel_name_materialise_after_update:
  ∀cx st mid n v.
    var_in_storage cx mid n ∧
    storable_value cx mid n v ⇒
    ∃ref_v.
      lookup_toplevel_name cx (update_toplevel_name cx st mid n v) mid n = SOME ref_v ∧
      FST (materialise cx ref_v (update_toplevel_name cx st mid n v)) = INL v
Proof
  rpt strip_tac >>
  drule_all lookup_toplevel_name_after_update_core >> strip_tac >>
  first_x_assum (qspec_then `st` strip_assume_tac) >>
  qexists_tac `ref_v` >> simp[]
QED

Theorem lookup_toplevel_name_after_update:
  ∀cx st mid n v.
    var_in_storage cx mid n ∧
    (∀av. v ≠ ArrayV av) ∧
    storable_value cx mid n v ⇒
    lookup_toplevel_name cx (update_toplevel_name cx st mid n v) mid n = SOME (Value v)
Proof
  rpt strip_tac >>
  drule_all lookup_toplevel_name_after_update_core >> strip_tac >>
  first_x_assum (qspec_then `st` strip_assume_tac) >> gvs[]
QED

Theorem decode_value_disjoint_from_encode:
  ∀tv1 tv2 v off1 off2 writes storage0.
    encode_value tv1 v = SOME writes ∧
    value_has_type tv1 v ∧
    off1 + type_slot_size tv1 ≤ dimword(:256) ∧
    off2 + type_slot_size tv2 ≤ dimword(:256) ∧
    (off1 + type_slot_size tv1 ≤ off2 ∨ off2 + type_slot_size tv2 ≤ off1) ⇒
    decode_value (apply_writes (n2w off1) writes storage0)
       (w2n ((n2w off2):bytes32)) tv2 =
    decode_value storage0 (w2n ((n2w off2):bytes32)) tv2
Proof
  rpt strip_tac >>
  irule decode_value_disjoint_apply_writes >> simp[] >>
  qexists_tac `type_slot_size tv1` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  drule_all (CONJUNCT1 encode_writes_bounded) >> simp[]
QED

Theorem lookup_toplevel_name_preserved_after_update:
  ∀cx st mid1 mid2 n1 n2 v.
    well_formed_layout cx ∧
    storable_value cx mid1 n1 v ∧
    (mid1,n1) ≠ (mid2,n2) ∧
    var_in_storage cx mid1 n1 ∧ var_in_storage cx mid2 n2 ⇒
    lookup_toplevel_name cx (update_toplevel_name cx st mid1 n1 v) mid2 n2 =
    lookup_toplevel_name cx st mid2 n2
Proof
  rpt gen_tac \\ strip_tac
  \\ `∃b1 off1 tv1. storage_var_info cx mid1 n1 = SOME (b1, off1, tv1) ∧
    well_formed_type_value tv1` by metis_tac[var_in_storage_storage_var_info]
  \\ `∃b2 off2 tv2. storage_var_info cx mid2 n2 = SOME (b2, off2, tv2) ∧
    well_formed_type_value tv2` by metis_tac[var_in_storage_storage_var_info]
  \\ `off1 + type_slot_size tv1 ≤ dimword(:256)` by
    (fs[well_formed_layout_def] >> res_tac)
  \\ `off2 + type_slot_size tv2 ≤ dimword(:256)` by
    (fs[well_formed_layout_def] >> res_tac)
  \\ `b1 = b2 ⇒
    off1 + type_slot_size tv1 ≤ off2 ∨ off2 + type_slot_size tv2 ≤ off1` by (
    strip_tac >> gvs[well_formed_layout_def] >>
    first_x_assum drule_all >> simp[])
  \\ `value_has_type tv1 v` by (
    fs[storable_value_def] >>
    first_x_assum irule >>
    simp[storage_type_of_def])
  \\ gvs[storage_var_info_def, AllCaseEqs()]
  \\ simp[update_toplevel_name_def]
  \\ simp[Once set_global_def, write_storage_slot_def,
       bind_def, lift_option_type_def, lift_option_def,
       return_def, LET_THM, raise_def]
  \\ `∃storage0. get_storage_backend cx b1 st = (INL storage0, st)` by
    metis_tac[get_storage_backend_INL]
  \\ qpat_x_assum `get_storage_backend _ _ _ = _`
    (fn th => simp[th] >> assume_tac th)
  \\ Cases_on `encode_value tv1 v` \\ simp[raise_def, return_def]
  \\ rename1 `encode_value tv1 v = SOME writes`
  \\ simp[lookup_toplevel_name_def, lookup_global_def, bind_def,
       lift_option_type_def, lift_option_def, return_def, LET_THM, raise_def]
  \\ Cases_on `b1 = b2`
  >- (
    pop_assum SUBST_ALL_TAC
    >> qpat_x_assum `(_ ⇔ _) ⇒ _` (assume_tac o REWRITE_RULE [])
    >> RULE_ASSUM_TAC (REWRITE_RULE [GSYM (EVAL ``dimword(:256)``)])
    >> `decode_value (apply_writes (n2w off1) writes storage0)
         (w2n ((n2w off2) : 256 word)) tv2 =
       decode_value storage0 (w2n ((n2w off2) : 256 word)) tv2`
    by (irule decode_value_disjoint_from_encode >> metis_tac[])
    >> Cases_on `tv2` >> simp[return_def]
    >> simp[read_storage_slot_def, bind_def, lift_option_def,
         return_def, raise_def]
    >> REWRITE_TAC [get_after_set_storage_backend] >> simp[]
    >> qpat_x_assum `get_storage_backend _ _ st = _` (fn th => simp[th])
    >> TRY (qpat_x_assum `decode_value _ _ _ = decode_value _ _ _`
      (fn th => REWRITE_TAC [SIMP_RULE (srw_ss()) [] th]))
    >> rpt (BasicProvers.PURE_CASE_TAC >> simp[return_def, raise_def])
  )
  \\ Cases_on `tv2` \\ simp[return_def]
  \\ simp[read_storage_slot_def, bind_def, lift_option_def, return_def]
  \\ `∃s2. get_storage_backend cx b2 st = (INL s2, st)` by
    metis_tac[get_storage_backend_INL]
  \\ `∃s2'. get_storage_backend cx b2
    (SND (set_storage_backend cx b1
      (apply_writes (n2w off1) writes storage0) st)) =
    (INL s2', SND (set_storage_backend cx b1
      (apply_writes (n2w off1) writes storage0) st))` by
    metis_tac[get_storage_backend_INL]
  \\ `s2' = s2` by (
    `FST (get_storage_backend cx b2
      (SND (set_storage_backend cx b1
        (apply_writes (n2w off1) writes storage0) st))) =
     FST (get_storage_backend cx b2 st)` by
      (irule get_after_set_other_backend >> simp[]) >>
    gvs[])
  \\ gvs[]
  \\ qpat_x_assum `get_storage_backend cx b2 (SND _) = _` (fn th => simp[th])
  \\ qpat_x_assum `get_storage_backend cx b2 st = _` (fn th => simp[th])
  \\ ntac 8 (BasicProvers.PURE_CASE_TAC >> simp[return_def, raise_def])
QED

(* ============================================================
   storable_value transfer: prove storable_value for a new value
   from a lookup of an old value of the same type.

   General theorem + specialized versions for integer types.
   ============================================================ *)

Theorem storable_value_transfer:
  ∀cx mid n new_v tv.
    storage_type_of cx mid n = SOME tv ∧
    value_has_type tv new_v ⇒
    storable_value cx mid n new_v
Proof
  simp[storable_value_def]
QED

Theorem storable_value_transfer_uint:
  ∀cx mid n b new_val.
    storage_type_of cx mid n = SOME (BaseTV (UintT b)) ∧
    within_int_bound (Unsigned b) new_val ∧ b ≤ 256 ⇒
    storable_value cx mid n (IntV new_val)
Proof
  rpt strip_tac >>
  irule storable_value_transfer >>
  qexists_tac `BaseTV (UintT b)` >>
  gvs[value_has_type_inv, within_int_bound_def]
QED

Theorem storable_value_transfer_int:
  ∀cx mid n b new_val.
    storage_type_of cx mid n = SOME (BaseTV (IntT b)) ∧
    within_int_bound (Signed b) new_val ∧ b ≤ 256 ⇒
    storable_value cx mid n (IntV new_val)
Proof
  rpt strip_tac >>
  irule storable_value_transfer >>
  qexists_tac `BaseTV (IntT b)` >>
  gvs[value_has_type_inv]
QED

(* Specialized lookup_toplevel_name_after_update for integer types.
   These combine storable_value_transfer with lookup_toplevel_name_after_update
   into a single conditional rewrite whose conditions are more easily
   checkable. *)

Theorem lookup_toplevel_name_after_update_uint:
  ∀cx st mid n b new_val.
    var_in_storage cx mid n ∧
    storage_type_of cx mid n = SOME (BaseTV (UintT b)) ∧
    within_int_bound (Unsigned b) new_val ∧ b ≤ 256 ⇒
    lookup_toplevel_name cx
      (update_toplevel_name cx st mid n (IntV new_val))
      mid n = SOME (Value (IntV new_val))
Proof
  rpt strip_tac >>
  irule lookup_toplevel_name_after_update >> simp[] >>
  irule storable_value_transfer_uint >>
  simp[]
QED

Theorem lookup_toplevel_name_after_update_int:
  ∀cx st mid n b new_val.
    var_in_storage cx mid n ∧
    storage_type_of cx mid n = SOME (BaseTV (IntT b)) ∧
    within_int_bound (Signed b) new_val ∧ b ≤ 256 ⇒
    lookup_toplevel_name cx
      (update_toplevel_name cx st mid n (IntV new_val))
      mid n = SOME (Value (IntV new_val))
Proof
  rpt strip_tac >>
  irule lookup_toplevel_name_after_update >> simp[] >>
  irule storable_value_transfer_int >>
  simp[]
QED
