Theory vyperLookupStorage

Ancestors
  vyperLookup vyperMisc vyperContext vyperState vyperStorage vyperStorageBackend
  vyperInterpreter vyperStatePreservation
  vyperValue vyperValueOperation vyperTyping vyperEncodeDecode
Libs
  wordsLib

Definition lookup_toplevel_name_def:
  lookup_toplevel_name cx st mid n =
  case lookup_global cx mid n st of
  | (INL v, st) => SOME v
  | _ => NONE
End

Definition update_toplevel_name_def:
  update_toplevel_name cx st mid n v =
  SND (set_global cx mid n v st)
End

Definition lookup_toplevel_name_target_def:
  lookup_toplevel_name_target cx st n = lookup_base_target cx st (TopLevelNameTarget n)
End

Definition var_in_storage_def:
  var_in_storage cx mid n ⇔
  ∃code b t id offset tv.
    get_module_code cx mid = SOME code ∧
    find_var_decl_by_name n code = SOME (StorageVarDecl b t, id) ∧
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
        case find_var_decl_by_name n code of
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

(* A one-slot value's word is canonical: it is the encoding of the value
   it decodes to, so decoding does not truncate it.  Only for well-formed
   types: a bytesM wider than a slot decodes to 32 bytes, which do not
   encode back. *)
Definition word_slot_canonical_def:
  word_slot_canonical (w : bytes32) tv <=>
    well_formed_type_value tv ==>
    encode_base_to_slot (decode_base_from_slot w tv) tv = SOME w
End

Theorem word_of_bytes_zeros[local]:
  !n a. word_of_bytes T a (REPLICATE n (0w:word8)) = (0w : bytes32)
Proof
  Induct_on `n` >> simp[byteTheory.word_of_bytes_def] >>
  simp[byteTheory.set_byte_def, LET_THM, byteTheory.word_slice_alt_zero]
QED

Theorem word_slot_canonical_zero:
  word_slot_canonical 0w (BaseTV (UintT n)) /\
  word_slot_canonical 0w (BaseTV (IntT n)) /\
  word_slot_canonical 0w (BaseTV DecimalT) /\
  word_slot_canonical 0w (BaseTV BoolT) /\
  word_slot_canonical 0w (BaseTV AddressT) /\
  word_slot_canonical 0w (BaseTV (BytesT (Fixed n))) /\
  word_slot_canonical 0w (FlagTV n)
Proof
  `word_to_bytes_be (0w : bytes32) = REPLICATE 32 0w` by EVAL_TAC >>
  rw[word_slot_canonical_def, encode_base_to_slot_def,
     decode_base_from_slot_def, bool_to_slot_def, slot_to_bool_def,
     integer_wordTheory.i2w_0]
  >~ [`PAD_LEFT _ _ _`] >- EVAL_TAC >>
  `TAKE n (REPLICATE 32 (0w:word8)) = REPLICATE n 0w`
    by gvs[well_formed_type_value_def, listTheory.LIST_EQ_REWRITE,
           listTheory.EL_TAKE, rich_listTheory.EL_REPLICATE] >>
  simp[byteTheory.word_of_bytes_be_def, word_of_bytes_zeros]
QED

(* Predicate: slots read during decode_value contain in-range values.
   Captures all conditions needed for decode_value to succeed and
   produce well-typed values, and keeps one-slot values canonical. *)
Definition slots_in_range_def:
  slots_in_range storage offset (BaseTV (UintT n)) =
    word_slot_canonical (read_slot storage offset) (BaseTV (UintT n)) ∧
  slots_in_range storage offset (BaseTV (IntT n)) =
    word_slot_canonical (read_slot storage offset) (BaseTV (IntT n)) ∧
  slots_in_range storage offset (BaseTV (BytesT (Dynamic max))) =
    (w2n (read_slot storage offset) ≤ max) ∧
  slots_in_range storage offset (BaseTV (StringT max)) =
    (w2n (read_slot storage offset) ≤ max) ∧
  slots_in_range storage offset (BaseTV DecimalT) =
    word_slot_canonical (read_slot storage offset) (BaseTV DecimalT) ∧
  slots_in_range storage offset (BaseTV BoolT) =
    word_slot_canonical (read_slot storage offset) (BaseTV BoolT) ∧
  slots_in_range storage offset (BaseTV AddressT) =
    word_slot_canonical (read_slot storage offset) (BaseTV AddressT) ∧
  slots_in_range storage offset (BaseTV (BytesT (Fixed n))) =
    word_slot_canonical (read_slot storage offset) (BaseTV (BytesT (Fixed n))) ∧
  slots_in_range storage offset (FlagTV m) =
    word_slot_canonical (read_slot storage offset) (FlagTV m) ∧
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
    LENGTH_word_to_bytes_be_256] >>
  rpt strip_tac >>
  gvs[value_has_type_def,
      well_formed_type_value_def, within_int_bound_def,
      listTheory.LENGTH_TAKE_EQ, LENGTH_word_to_bytes_be_256,
      all_have_type_EVERY,
      slots_in_range_def] >>
  TRY (simp[SIMP_RULE (srw_ss()) [within_int_bound_def, LET_THM]
              truncate_signed_range] >> NO_TAC) >>
  TRY (metis_tac[decode_dyn_bytes_LENGTH]) >>
  TRY (imp_res_tac LENGTH_decode_static_array >>
       simp[sparse_has_type_enumerate, SORTED_enumerate_static_array] >>
       NO_TAC) >>
  TRY (imp_res_tac LENGTH_decode_dyn_array >> simp[] >> NO_TAC) >>
  simp[SIMP_RULE (srw_ss()) [within_int_bound_def, LET_THM]
         (Q.SPEC `168` truncate_signed_range)]
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

Theorem slots_in_range_offset_cong:
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

Theorem struct_slots_in_range_field[local]:
  !fs off id foff ftv storage.
    struct_slots_in_range storage off fs /\
    struct_field_slot fs id = SOME (foff, ftv) ==>
    slots_in_range storage (off + foff) ftv
Proof
  Induct >- simp[struct_field_slot_def] >> Cases >> rpt gen_tac >>
  simp[struct_field_slot_def, Once slots_in_range_def] >>
  IF_CASES_TAC >> rpt strip_tac >> gvs[] >>
  Cases_on `struct_field_slot fs id` >> gvs[] >>
  rename1 `struct_field_slot fs id = SOME p` >> PairCases_on `p` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

(* A struct field's slots are in range when the struct's are. *)
Theorem storage_field_slots_in_range:
  !storage w fs id foff ftv.
    slots_in_range storage (w2n (w:bytes32)) (StructTV fs) /\
    struct_field_slot fs id = SOME (foff, ftv) ==>
    slots_in_range storage (w2n (w + n2w foff)) ftv
Proof
  rpt strip_tac >>
  `slots_in_range storage (w2n w + foff) ftv` by
    (irule struct_slots_in_range_field >>
     gvs[Once slots_in_range_def] >> metis_tac[]) >>
  `slots_in_range storage (w2n w + foff) ftv =
   slots_in_range storage (w2n (w + n2w foff)) ftv` by
    (irule (CONJUNCT1 slots_in_range_offset_cong) >>
     `w + n2w foff = n2w (w2n w + foff)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     simp[wordsTheory.w2n_n2w]) >>
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

(* apply_writes leaves storage lookups outside its write set unchanged. *)
Theorem apply_writes_lookup_other[local]:
  ∀writes (base : bytes32) storage (addr : bytes32).
    (∀off. MEM off (MAP FST writes) ⇒ n2w (w2n base + off) ≠ addr) ⇒
    lookup_storage addr (apply_writes base writes storage) =
    lookup_storage addr storage
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> simp[apply_writes_def] >>
  rpt strip_tac >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem nwn_eq_apply_writes[local]:
  ∀(base : num) (k : num).
    n2w (w2n (n2w base : bytes32) + k) = n2w (base + k) : bytes32
Proof
  REWRITE_TAC [GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n]
QED
Theorem read_slot_disjoint_apply_writes[local]:
  (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
  off1 + sz1 ≤ dimword(:256) ∧
  read_off < dimword(:256) ∧
  (off1 + sz1 ≤ read_off ∨ read_off < off1) ⇒
  read_slot (apply_writes (n2w off1) writes storage) read_off =
  read_slot storage read_off
Proof
  rpt strip_tac >>
  simp[read_slot_def] >>
  irule apply_writes_lookup_other >>
  REWRITE_TAC [nwn_eq_apply_writes] >>
  rpt strip_tac >>
  `off < sz1` by res_tac >>
  gvs[wordsTheory.n2w_11]
QED

Theorem slots_in_range_disjoint_apply_writes_mutual[local]:
  (∀storage off2 tv2.
    slots_in_range storage off2 tv2 ⇒
    ∀off1 sz1 writes.
      (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
      off1 + sz1 ≤ dimword(:256) ∧
      off2 + type_slot_size tv2 ≤ dimword(:256) ∧
      (off1 + sz1 ≤ off2 ∨ off2 + type_slot_size tv2 ≤ off1) ⇒
      slots_in_range (apply_writes (n2w off1) writes storage) off2 tv2) ∧
  (∀storage off2 tvs.
    tuple_slots_in_range storage off2 tvs ⇒
    ∀off1 sz1 writes.
      (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
      off1 + sz1 ≤ dimword(:256) ∧
      off2 + type_slot_size_list tvs ≤ dimword(:256) ∧
      (off1 + sz1 ≤ off2 ∨ off2 + type_slot_size_list tvs ≤ off1) ⇒
      tuple_slots_in_range (apply_writes (n2w off1) writes storage) off2 tvs) ∧
  (∀storage off2 tv n.
    static_slots_in_range storage off2 tv n ⇒
    ∀off1 sz1 writes.
      (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
      off1 + sz1 ≤ dimword(:256) ∧
      off2 + n * type_slot_size tv ≤ dimword(:256) ∧
      (off1 + sz1 ≤ off2 ∨ off2 + n * type_slot_size tv ≤ off1) ⇒
      static_slots_in_range (apply_writes (n2w off1) writes storage) off2 tv n) ∧
  (∀storage off2 tv n.
    dyn_slots_in_range storage off2 tv n ⇒
    ∀off1 sz1 writes.
      (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
      off1 + sz1 ≤ dimword(:256) ∧
      off2 + n * type_slot_size tv ≤ dimword(:256) ∧
      (off1 + sz1 ≤ off2 ∨ off2 + n * type_slot_size tv ≤ off1) ⇒
      dyn_slots_in_range (apply_writes (n2w off1) writes storage) off2 tv n) ∧
  (∀storage off2 ftypes.
    struct_slots_in_range storage off2 ftypes ⇒
    ∀off1 sz1 writes.
      (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
      off1 + sz1 ≤ dimword(:256) ∧
      off2 + type_slot_size_fields ftypes ≤ dimword(:256) ∧
      (off1 + sz1 ≤ off2 ∨ off2 + type_slot_size_fields ftypes ≤ off1) ⇒
      struct_slots_in_range (apply_writes (n2w off1) writes storage) off2 ftypes)
Proof
  ho_match_mp_tac slots_in_range_ind >>
  rpt conj_tac >> rpt gen_tac >>
  DISCH_TAC >> rpt gen_tac >> strip_tac >>
  PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
  simp_tac (srw_ss()) [LET_THM, type_slot_size_def]
  >>~- ([`word_slot_canonical _ _`],
        rpt strip_tac >> gvs[type_slot_size_def] >>
        mp_tac (Q.INST [`read_off` |-> `off2`]
                  read_slot_disjoint_apply_writes) >>
        impl_tac >- gvs[] >>
        strip_tac >> gvs[slots_in_range_def])
  >- (`read_slot (apply_writes (n2w off1) writes storage) off2 =
       read_slot storage off2` by
        (irule read_slot_disjoint_apply_writes >>
         conj_tac >- gvs[type_slot_size_def] >>
         qexists_tac `sz1` >> simp[]) >>
      gvs[slots_in_range_def])
  >- (`read_slot (apply_writes (n2w off1) writes storage) off2 =
       read_slot storage off2` by
        (irule read_slot_disjoint_apply_writes >>
         conj_tac >- gvs[type_slot_size_def] >>
         qexists_tac `sz1` >> gvs[type_slot_size_def]) >>
      gvs[slots_in_range_def])
  >- (`read_slot (apply_writes (n2w off1) writes storage) off2 =
       read_slot storage off2` by
        (irule read_slot_disjoint_apply_writes >>
         conj_tac >- gvs[type_slot_size_def] >>
         qexists_tac `sz1` >> simp[]) >>
      gvs[slots_in_range_def])
  >- (`read_slot (apply_writes (n2w off1) writes storage) off2 =
       read_slot storage off2` by
        (irule read_slot_disjoint_apply_writes >>
         conj_tac >- gvs[type_slot_size_def] >>
         qexists_tac `sz1` >> gvs[type_slot_size_def]) >>
      gvs[slots_in_range_def])
  >- (rpt strip_tac >>
      qpat_x_assum `slots_in_range _ _ (TupleTV _)`
        (assume_tac o PURE_ONCE_REWRITE_RULE [slots_in_range_def]) >>
      qpat_x_assum `_ ⇒ ∀off1 sz1 writes. _` (fn ih =>
        first_assum (fn range => match_mp_tac
          (Q.SPECL [`off1`, `sz1`, `writes`] (MP ih range)))) >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `slots_in_range _ _ (ArrayTV _ (Fixed _))`
        (assume_tac o PURE_ONCE_REWRITE_RULE [slots_in_range_def]) >>
      qpat_x_assum `_ ⇒ ∀off1 sz1 writes. _` (fn ih =>
        first_assum (fn range => match_mp_tac
          (Q.SPECL [`off1`, `sz1`, `writes`] (MP ih range)))) >> simp[])
  >- (rpt strip_tac >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [type_slot_size_def]) >>
      `read_slot (apply_writes (n2w off1) writes storage) off2 =
       read_slot storage off2` by
        (irule read_slot_disjoint_apply_writes >>
         conj_tac >- simp[] >>
         qexists_tac `sz1` >> simp[]) >>
      qpat_x_assum `slots_in_range _ _ (ArrayTV _ (Dynamic _))`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [slots_in_range_def, LET_THM]) >>
      qpat_x_assum `∀len. len = _ ∧ _ ⇒ _`
        (qspec_then `w2n (read_slot storage off2)` mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[] >>
      first_x_assum (qspecl_then [`off1`, `sz1`, `writes`] mp_tac) >>
      disch_then match_mp_tac >>
      `w2n (read_slot storage off2) * type_slot_size tv ≤
       max * type_slot_size tv` by
        (irule arithmeticTheory.LESS_MONO_MULT >> simp[]) >>
      asm_rewrite_tac[arithmeticTheory.MIN_DEF, EVAL ``dimword(:256)``] >>
      POP_ASSUM_LIST (MAP_EVERY assume_tac o filter (numSyntax.is_leq o concl)) >>
      decide_tac)

  >- (rpt strip_tac >>
      qpat_x_assum `slots_in_range _ _ (StructTV _)`
        (assume_tac o PURE_ONCE_REWRITE_RULE [slots_in_range_def]) >>
      qpat_x_assum `_ ⇒ ∀off1 sz1 writes. _` (fn ih =>
        first_assum (fn range => match_mp_tac
          (Q.SPECL [`off1`, `sz1`, `writes`] (MP ih range)))) >> simp[])
  (* Unfold only the concrete range fact, then specialize the matching IH
     before simplifying the resulting numeric bounds. *)
  >> (rpt strip_tac >>
      FIRST (map (fn pat => qpat_x_assum pat
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [slots_in_range_def]))
        [`tuple_slots_in_range _ _ (_::_)`,
         `static_slots_in_range _ _ _ (SUC _)`,
         `dyn_slots_in_range _ _ _ (SUC _)`,
         `struct_slots_in_range _ _ (_::_)`]) >>
      qpat_x_assum `_ ∧ _` (fn ihs =>
        FIRST (map (fn ih => first_assum (fn range =>
          match_mp_tac (Q.SPECL [`off1`, `sz1`, `writes`] (MP ih range))))
          (CONJUNCTS ihs))) >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [arithmeticTheory.MULT]) >>
      asm_rewrite_tac[arithmeticTheory.MULT, EVAL ``dimword(:256)``] >>
      (* Coverage is discharged; arithmetic needs only the numeric bounds. *)
      POP_ASSUM_LIST (MAP_EVERY assume_tac o filter (numSyntax.is_leq o concl)) >>
      decide_tac)
QED

Theorem slots_in_range_disjoint_apply_writes:
  slots_in_range storage off2 tv2 ∧
  (∀wr_off. MEM wr_off (MAP FST writes) ⇒ wr_off < sz1) ∧
  off1 + sz1 ≤ dimword(:256) ∧
  off2 + type_slot_size tv2 ≤ dimword(:256) ∧
  (off1 + sz1 ≤ off2 ∨ off2 + type_slot_size tv2 ≤ off1) ⇒
  slots_in_range (apply_writes (n2w off1) writes storage) off2 tv2
Proof
  rpt strip_tac >>
  irule (CONJUNCT1 slots_in_range_disjoint_apply_writes_mutual) >>
  simp[] >> qexists_tac `sz1` >> gvs[]
QED

Theorem slots_in_range_read_agree:
  (!s b tv t c.
    (!i. i < type_slot_size tv ==> read_slot s (b+i) = read_slot t (c+i)) ==>
    (slots_in_range s b tv <=> slots_in_range t c tv)) /\
  (!s b tvs t c.
    (!i. i < type_slot_size_list tvs ==> read_slot s (b+i) = read_slot t (c+i)) ==>
    (tuple_slots_in_range s b tvs <=> tuple_slots_in_range t c tvs)) /\
  (!s b tv n t c.
    (!i. i < n * type_slot_size tv ==> read_slot s (b+i) = read_slot t (c+i)) ==>
    (static_slots_in_range s b tv n <=> static_slots_in_range t c tv n)) /\
  (!s b tv n t c.
    (!i. i < n * type_slot_size tv ==> read_slot s (b+i) = read_slot t (c+i)) ==>
    (dyn_slots_in_range s b tv n <=> dyn_slots_in_range t c tv n)) /\
  (!s b fields t c.
    (!i. i < type_slot_size_fields fields ==> read_slot s (b+i) = read_slot t (c+i)) ==>
    (struct_slots_in_range s b fields <=> struct_slots_in_range t c fields))
Proof
  ho_match_mp_tac slots_in_range_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
  simp_tac std_ss [type_slot_size_def, LET_THM] >>
  (all_tac >>~- ([`word_slot_canonical _ _`],
    first_x_assum (qspec_then `0` mp_tac) >> simp[type_slot_size_def])) >>
  (all_tac >>~- ([`w2n _ <= _ <=> _`],
    first_x_assum (qspec_then `0` mp_tac) >> simp[type_slot_size_def])) >>
  TRY (first_x_assum irule >> gvs[type_slot_size_def] >> NO_TAC) >>
  TRY (
    qpat_assum `!len. len = _ /\ _ ==> _` kall_tac >>
    `read_slot s b = read_slot t c` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[type_slot_size_def]) >>
    Cases_on `w2n (read_slot s b) <= max` >- (
      qpat_x_assum `!len. len = _ /\ _ ==> _`
        (qspec_then `w2n (read_slot s b)` mp_tac) >>
      asm_rewrite_tac[] >>
      disch_then (qspecl_then [`t`, `c+1`] mp_tac) >>
      impl_tac >- (
        rpt strip_tac >>
        `MIN (w2n (read_slot t c)) max * type_slot_size tv <=
         max * type_slot_size tv` by simp[arithmeticTheory.LE_MULT_RCANCEL] >>
        qpat_x_assum `!i. i < type_slot_size _ ==> _`
          (qspec_then `1+i` mp_tac) >>
        pure_rewrite_tac[type_slot_size_def, GSYM arithmeticTheory.ADD_ASSOC] >>
        (impl_tac >- decide_tac) >> simp[]) >> gvs[]) >> gvs[] >> NO_TAC) >>
  (qpat_x_assum `!t c. (!i. _ ==> read_slot s (b + type_slot_size tv + i) = _) ==> _`
    (markerLib.mk_asm "tail") >>
  qpat_x_assum `!t c. (!i. _ ==> read_slot s (b+i) = _) ==> _`
    (markerLib.mk_asm "head") >>
  BINOP_TAC
  >- (markerLib.asm "head" irule >> rpt strip_tac >>
      qpat_x_assum `!i. i < _ ==> _` (qspec_then `i` mp_tac) >>
      pure_rewrite_tac[type_slot_size_def, arithmeticTheory.MULT_CLAUSES] >>
      (impl_tac >- decide_tac) >> simp[]) >>
  markerLib.asm "tail" irule >> rpt strip_tac >>
  qpat_x_assum `!i. i < _ ==> _` (qspec_then `type_slot_size tv + i` mp_tac) >>
  pure_rewrite_tac[type_slot_size_def, arithmeticTheory.MULT_CLAUSES,
                   GSYM arithmeticTheory.ADD_ASSOC] >>
  (impl_tac >- decide_tac) >> simp[])
QED

Theorem slots_in_range_relative_frame:
  !ws (addr:num) lo hi tv s.
  slots_in_range s (addr+lo) tv /\ hi <= dimword(:256) /\
  lo + type_slot_size tv <= hi /\
  (!j w. MEM (j,w) ws ==> j < hi /\ (j < lo \/ lo+type_slot_size tv <= j)) ==>
  slots_in_range (apply_writes (n2w addr) ws s) (addr+lo) tv
Proof
  rpt strip_tac >>
  `slots_in_range (apply_writes (n2w addr) ws s) (addr+lo) tv =
   slots_in_range s (addr+lo) tv` suffices_by simp[] >>
  irule (CONJUNCT1 slots_in_range_read_agree) >>
  rpt strip_tac >>
  pure_rewrite_tac[read_slot_def, GSYM arithmeticTheory.ADD_ASSOC] >>
  irule apply_writes_lookup_miss_num >>
  gen_tac >> disch_tac >>
  qpat_x_assum `MEM _ (MAP FST _)` mp_tac >>
  simp_tac std_ss [listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  strip_tac >>
  qpat_x_assum `!j w. _` drule >> strip_tac >>
  irule n2w_add_cancel >> decide_tac
QED

Theorem array_slots_in_range_indexed:
  (!n s (addr:num) tv.
    static_slots_in_range s addr tv n <=>
    !k. k < n ==> slots_in_range s (addr+k*type_slot_size tv) tv) /\
  (!n s (addr:num) tv.
    dyn_slots_in_range s addr tv n <=>
    !k. k < n ==> slots_in_range s (addr+k*type_slot_size tv) tv)
Proof
  conj_tac >> (Induct_on `n` >> rpt gen_tac >>
    simp[Once slots_in_range_def] >>
    simp[arithmeticTheory.LT_SUC, arithmeticTheory.ADD_CLAUSES] >>
    simp[DISJ_IMP_THM, FORALL_AND_THM] >>
    CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV) >>
    simp[FORALL_AND_THM, arithmeticTheory.MULT_CLAUSES,
         GSYM arithmeticTheory.ADD_ASSOC] >>
    metis_tac[])
QED

Theorem slots_in_range_zero_reads:
  (!s b tv.
    (!i. i < type_slot_size tv ==> read_slot s (b+i) = 0w) ==>
    slots_in_range s b tv) /\
  (!s b tvs.
    (!i. i < type_slot_size_list tvs ==> read_slot s (b+i) = 0w) ==>
    tuple_slots_in_range s b tvs) /\
  (!s b tv n.
    (!i. i < n * type_slot_size tv ==> read_slot s (b+i) = 0w) ==>
    static_slots_in_range s b tv n) /\
  (!s b tv n.
    (!i. i < n * type_slot_size tv ==> read_slot s (b+i) = 0w) ==>
    dyn_slots_in_range s b tv n) /\
  (!s b fields.
    (!i. i < type_slot_size_fields fields ==> read_slot s (b+i) = 0w) ==>
    struct_slots_in_range s b fields)
Proof
  ho_match_mp_tac slots_in_range_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
  simp_tac std_ss [type_slot_size_def, LET_THM] >>
  TRY (first_x_assum (qspec_then `0` mp_tac) >>
       simp[type_slot_size_def, word_slot_canonical_zero, slots_in_range_def] >> NO_TAC) >>
  TRY (first_x_assum irule >> gvs[type_slot_size_def] >> NO_TAC) >>
  (conj_tac
  >- (first_x_assum irule >> rpt strip_tac >>
      qpat_x_assum `!i. _` (qspec_then `i` mp_tac) >>
      pure_rewrite_tac[type_slot_size_def, arithmeticTheory.MULT_CLAUSES] >>
      (impl_tac >- decide_tac) >> simp[]) >>
  first_x_assum irule >> rpt strip_tac >>
  qpat_x_assum `!i. _` (qspec_then `type_slot_size tv + i` mp_tac) >>
  pure_rewrite_tac[type_slot_size_def, arithmeticTheory.MULT_CLAUSES,
                   GSYM arithmeticTheory.ADD_ASSOC] >>
  (impl_tac >- decide_tac) >> simp[])
QED

Theorem encode_tuple_slots_in_range:
  !tvs offset vs writes base storage.
    EVERY (\tv. !v ws b s. value_has_type tv v /\
      encode_value tv v = SOME ws ==>
      slots_in_range (apply_writes (n2w b) ws s) b tv) tvs /\
    values_have_types tvs vs /\ EVERY well_formed_type_value tvs /\
    offset + type_slot_size_list tvs <= dimword(:256) /\
    encode_tuple offset tvs vs = SOME writes ==>
    tuple_slots_in_range (apply_writes (n2w base) writes storage)
      (base+offset) tvs
Proof
  Induct
  >- (Cases_on `vs` >>
      simp[encode_value_def, slots_in_range_def, value_has_type_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `vs` >- gvs[encode_value_def, value_has_type_def] >>
  gvs[value_has_type_def] >>
  qpat_x_assum `encode_tuple _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  rename1 `encode_value htv hv = SOME hslots` >>
  rename1 `encode_tuple _ _ _ = SOME rslots` >>
  qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
  rewrite_tac[apply_writes_append] >>
  simp[Once slots_in_range_def] >>
  conj_tac
  >- (irule slots_in_range_relative_frame >>
      conj_tac
      >- (qexists_tac `offset + type_slot_size_list (htv::tvs)` >>
          simp_tac std_ss [type_slot_size_def] >>
          conj_tac
          >- (rpt strip_tac >>
              drule (el 2 (CONJUNCTS encode_writes_bounded)) >>
              simp[] >> disch_then (qspec_then `j` mp_tac) >>
              (impl_tac >- (simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST])) >>
              decide_tac) >>
          gvs[type_slot_size_def]) >>
      rewrite_tac[apply_writes_shift] >>
      first_x_assum irule >> qexists_tac `hv` >> simp[]) >>
  first_x_assum irule >>
  gvs[type_slot_size_def] >> qexists_tac `t` >> simp[]
QED

Theorem encode_struct_slots_in_range:
  !ftypes offset fields writes base storage.
    EVERY (\(nm,tv). !v ws b s. value_has_type tv v /\
      encode_value tv v = SOME ws ==>
      slots_in_range (apply_writes (n2w b) ws s) b tv) ftypes /\
    struct_has_type ftypes fields /\
    EVERY (well_formed_type_value o SND) ftypes /\
    offset + type_slot_size_fields ftypes <= dimword(:256) /\
    encode_struct offset ftypes fields = SOME writes ==>
    struct_slots_in_range (apply_writes (n2w base) writes storage)
      (base+offset) ftypes
Proof
  Induct
  >- (Cases_on `fields` >>
      simp[encode_value_def, slots_in_range_def, value_has_type_def]) >>
  Cases >> rpt gen_tac >> strip_tac >>
  Cases_on `fields` >- gvs[encode_value_def, value_has_type_def] >>
  Cases_on `h` >> gvs[value_has_type_def, pairTheory.FORALL_PROD] >>
  qpat_x_assum `encode_struct _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  rename1 `encode_value tv v = SOME elem_slots` >>
  rename1 `encode_struct _ _ _ = SOME rest_writes` >>
  rename1 `(fname, tv)` >>
  rewrite_tac[apply_writes_append] >>
  simp[Once slots_in_range_def] >>
  conj_tac
  >- (irule slots_in_range_relative_frame >> conj_tac
      >- (qexists_tac `offset + type_slot_size_fields ((fname,tv)::ftypes)` >>
          simp_tac std_ss [type_slot_size_def] >> conj_tac
          >- (rpt strip_tac >>
              drule (el 5 (CONJUNCTS encode_writes_bounded)) >>
              simp[] >> disch_then (qspec_then `j` mp_tac) >>
              (impl_tac >- (simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST])) >>
              decide_tac) >>
          gvs[type_slot_size_def]) >>
      rewrite_tac[apply_writes_shift] >>
      first_x_assum irule >> qexists_tac `v` >> simp[]) >>
  first_x_assum irule >>
  gvs[type_slot_size_def] >> qexists_tac `t` >> simp[]
QED

Theorem encode_dyn_array_slots_in_range:
  !vs offset tv writes base storage.
    (!v ws b s. value_has_type tv v /\ encode_value tv v = SOME ws ==>
      slots_in_range (apply_writes (n2w b) ws s) b tv) /\
    all_have_type tv vs /\ well_formed_type_value tv /\
    offset + LENGTH vs * type_slot_size tv <= dimword(:256) /\
    encode_dyn_array tv offset vs = SOME writes ==>
    dyn_slots_in_range (apply_writes (n2w base) writes storage)
      (base+offset) tv (LENGTH vs)
Proof
  Induct
  >- simp[encode_value_def, slots_in_range_def, value_has_type_def] >>
  rpt gen_tac >> strip_tac >> gvs[value_has_type_def] >>
  qpat_x_assum `encode_dyn_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  rename1 `encode_value tv h = SOME elem_slots` >>
  rename1 `encode_dyn_array _ _ _ = SOME rest_writes` >>
  qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
  rewrite_tac[apply_writes_append] >>
  simp[Once slots_in_range_def] >> conj_tac
  >- (irule slots_in_range_relative_frame >> conj_tac
      >- (qexists_tac `offset + SUC (LENGTH vs) * type_slot_size tv` >>
          simp_tac std_ss [arithmeticTheory.MULT_CLAUSES] >> conj_tac
          >- (rpt strip_tac >>
              drule (el 4 (CONJUNCTS encode_writes_bounded)) >>
              simp[] >> disch_then (qspec_then `j` mp_tac) >>
              (impl_tac >- (simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST])) >>
              decide_tac) >> gvs[arithmeticTheory.MULT_CLAUSES]) >>
      rewrite_tac[apply_writes_shift] >>
      first_x_assum irule >> qexists_tac `h` >> simp[]) >>
  first_x_assum irule >>
  gvs[arithmeticTheory.MULT_CLAUSES] >> simp[arithmeticTheory.ADD_ASSOC] >>
  first_assum ACCEPT_TAC
QED

Theorem encode_dynamic_array_slots_in_range:
  !tv max vs slots base storage.
    (!v ws b s. value_has_type tv v /\ encode_value tv v = SOME ws ==>
      slots_in_range (apply_writes (n2w b) ws s) b tv) /\
    all_have_type tv vs /\ LENGTH vs <= max /\
    well_formed_type_value (ArrayTV tv (Dynamic max)) /\
    encode_dyn_array tv 1 vs = SOME slots ==>
    slots_in_range
      (apply_writes (n2w base) ((0,n2w (LENGTH vs))::slots) storage)
      base (ArrayTV tv (Dynamic max))
Proof
  rpt strip_tac >>
  gvs[well_formed_type_value_def, type_slot_size_def] >>
  `LENGTH vs * type_slot_size tv <= max * type_slot_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  rename1 `slots_in_range (apply_writes (n2w addr) _ st) addr _` >>
  `read_slot (apply_writes (n2w addr)
      ((0,n2w (LENGTH vs))::slots) st) addr = n2w (LENGTH vs)` by
    (irule read_slot_cons_0 >> gen_tac >> strip_tac >>
     irule n2w_add_cancel_0 >>
     drule (el 4 (CONJUNCTS encode_writes_bounded)) >>
     disch_then drule >> strip_tac >> pop_assum drule >> strip_tac >>
     conj_tac >- simp[] >> simp[] >> decide_tac) >>
  `MIN (LENGTH vs) max = LENGTH vs` by gvs[arithmeticTheory.MIN_DEF] >>
  simp[Once slots_in_range_def] >>
  `((0:num,n2w (LENGTH vs):bytes32)::slots) =
    [(0,n2w (LENGTH vs))] ++ slots` by simp[] >>
  pop_assum SUBST_ALL_TAC >> rewrite_tac[apply_writes_append] >>
  irule encode_dyn_array_slots_in_range >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem array_index_element_end_bound:
  i < n ==> i * sz + sz <= n * sz
Proof
  strip_tac >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists `(i + 1) * sz` >>
  simp[arithmeticTheory.LEFT_ADD_DISTRIB, arithmeticTheory.ADD_COMM,
       arithmeticTheory.LESS_MONO_MULT]
QED

Theorem encode_static_array_preserves_slots_in_range:
  !sparse tv offset n writes base storage.
    (!v ws b s. value_has_type tv v /\ encode_value tv v = SOME ws ==>
      slots_in_range (apply_writes (n2w b) ws s) b tv) /\
    static_slots_in_range storage (base+offset) tv n /\
    sparse_has_type tv n sparse /\ well_formed_type_value tv /\
    offset + n * type_slot_size tv <= dimword(:256) /\
    encode_static_array tv offset sparse = SOME writes ==>
    static_slots_in_range (apply_writes (n2w base) writes storage)
      (base+offset) tv n
Proof
  Induct >- simp[encode_value_def, apply_writes_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  gvs[value_has_type_def] >>
  qpat_x_assum `encode_static_array _ _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  rename1 `encode_value tv v = SOME elem_slots` >>
  rename1 `encode_static_array _ _ _ = SOME rest_writes` >>
  qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
  rewrite_tac[apply_writes_append] >>
  first_x_assum irule >> simp[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  rewrite_tac[CONJUNCT1 array_slots_in_range_indexed] >>
  rpt strip_tac >>
  rename1 `static_slots_in_range st (addr+offset) tv n` >>
  Cases_on `k=q`
  >- (gvs[] >> rewrite_tac[apply_writes_shift, GSYM arithmeticTheory.ADD_ASSOC] >>
      first_x_assum irule >> qexists_tac `v` >> simp[]) >>
  `k * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `q * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  irule slots_in_range_relative_frame >> conj_tac
  >- (qexists_tac `offset+n*type_slot_size tv` >>
      simp[] >> rpt gen_tac >> disch_tac >>
      gvs[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
      rename1 `MEM (r,_) elem_slots` >>
      `r < type_slot_size tv` by
        (drule (CONJUNCT1 encode_writes_bounded) >> simp[] >>
         disch_then (qspec_then `r` mp_tac) >>
         (impl_tac >- (simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST])) >>
         simp[]) >>
      conj_tac >- decide_tac >>
      Cases_on `k<q`
      >- (`k*type_slot_size tv+type_slot_size tv <= q*type_slot_size tv` by
            (irule array_index_element_end_bound >> simp[]) >> decide_tac) >>
      `q*type_slot_size tv+type_slot_size tv <= k*type_slot_size tv` by
        (irule array_index_element_end_bound >> decide_tac) >> decide_tac) >>
  qpat_x_assum `static_slots_in_range _ _ _ _` mp_tac >>
  pure_rewrite_tac[CONJUNCT1 array_slots_in_range_indexed] >>
  disch_then (qspec_then `k` mp_tac) >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> asm_rewrite_tac[]
QED

Theorem encode_fixed_array_slots_in_range:
  !tv n sparse writes base storage.
    (!v ws b s. value_has_type tv v /\ encode_value tv v = SOME ws ==>
      slots_in_range (apply_writes (n2w b) ws s) b tv) /\
    value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) /\
    well_formed_type_value (ArrayTV tv (Fixed n)) /\
    encode_value (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) = SOME writes ==>
    slots_in_range (apply_writes (n2w base) writes storage) base
      (ArrayTV tv (Fixed n))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[value_has_type_def, well_formed_type_value_def, type_slot_size_def] >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  qpat_x_assum `_ = writes` (SUBST1_TAC o SYM) >>
  rewrite_tac[apply_writes_append, slots_in_range_def] >>
  qspecl_then [`sparse`, `tv`, `0`] mp_tac
    encode_static_array_preserves_slots_in_range >>
  simp_tac std_ss [arithmeticTheory.ADD_CLAUSES] >> disch_then irule >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  irule (el 3 (CONJUNCTS slots_in_range_zero_reads)) >>
  rpt strip_tac >> rewrite_tac[read_slot_def] >>
  irule genlist_zeros_lookup >> simp[]
QED

Theorem encode_base_to_slot_canonical:
  value_has_type tv v /\ well_formed_type_value tv /\
  encode_base_to_slot v tv = SOME w ==> word_slot_canonical w tv
Proof
  rpt strip_tac >>
  drule_all encode_decode_roundtrip_all >>
  rewrite_tac[encode_decode_roundtrip_ok_def] >>
  disch_then (qspecl_then [`[(0,w)]`, `0`, `ARB`] mp_tac) >>
  Cases_on `tv`
  >- (Cases_on `b` >>
      gvs[encode_value_def, decode_value_def,
          read_slot_after_apply_writes_single, word_slot_canonical_def] >>
      Cases_on `v` >> gvs[encode_base_to_slot_def] >>
      rename1 `BytesT bnd` >> Cases_on `bnd` >>
      gvs[encode_value_def, decode_value_def,
          read_slot_after_apply_writes_single, word_slot_canonical_def,
          encode_base_to_slot_def])
  >> Cases_on `v` >>
  gvs[encode_base_to_slot_def, encode_value_def, decode_value_def,
      read_slot_after_apply_writes_single, word_slot_canonical_def,
      decode_base_from_slot_def]
QED

Theorem encode_base_slots_in_range:
  !bt v writes (addr:num) storage.
  value_has_type (BaseTV bt) v /\ well_formed_type_value (BaseTV bt) /\
  encode_value (BaseTV bt) v = SOME writes ==>
  slots_in_range (apply_writes (n2w addr) writes storage) addr (BaseTV bt)
Proof
  rpt strip_tac >>
  drule_all encode_decode_roundtrip_all >>
  rewrite_tac[encode_decode_roundtrip_ok_def] >>
  disch_then (qspecl_then [`writes`, `addr`, `storage`] mp_tac) >>
  simp[] >>
  Cases_on `bt` >> simp[slots_in_range_def, decode_value_def] >>
  (all_tac >>~- ([`word_slot_canonical _ _`],
    strip_tac >> gvs[encode_value_def, AllCaseEqs(),
                       read_slot_after_apply_writes_single] >>
    irule encode_base_to_slot_canonical >> metis_tac[])) >>
  (all_tac >>~- ([`w2n _ <= _`],
    simp[decode_dyn_bytes_def, AllCaseEqs(), read_slot_def] >> rpt strip_tac >> gvs[])) >>
  rename1 `BytesT bnd` >> Cases_on `bnd` >>
  gvs[slots_in_range_def, decode_value_def]
  >- (strip_tac >> gvs[encode_value_def, AllCaseEqs(),
                       read_slot_after_apply_writes_single] >>
      irule encode_base_to_slot_canonical >> metis_tac[]) >>
  simp[decode_dyn_bytes_def, AllCaseEqs(), read_slot_def] >> rpt strip_tac >> gvs[]
QED

Theorem encode_flag_slots_in_range:
  !m v writes (addr:num) storage.
  value_has_type (FlagTV m) v /\ well_formed_type_value (FlagTV m) /\
  encode_value (FlagTV m) v = SOME writes ==>
  slots_in_range (apply_writes (n2w addr) writes storage) addr (FlagTV m)
Proof
  rpt strip_tac >>
  gvs[encode_value_def, AllCaseEqs(), slots_in_range_def,
      read_slot_after_apply_writes_single] >>
  irule encode_base_to_slot_canonical >> metis_tac[]
QED

Theorem encode_implies_slots_in_range:
  ∀tv v writes (base : num) storage.
    value_has_type tv v ∧
    well_formed_type_value tv ∧
    encode_value tv v = SOME writes ⇒
    slots_in_range (apply_writes (n2w base) writes storage) base tv
Proof
  completeInduct_on `type_value_size tv` >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  Cases_on `tv`
  >- (irule encode_base_slots_in_range >> metis_tac[])
  >- (rename1 `TupleTV tvs` >>
      Cases_on `v'` >> gvs[encode_value_def] >>
      Cases_on `a` >> gvs[encode_value_def] >>
      simp[Once slots_in_range_def] >>
      qspecl_then [`tvs`, `0`] mp_tac encode_tuple_slots_in_range >>
      simp[] >> disch_then irule >>
      gvs[value_has_type_def, well_formed_type_value_def, type_slot_size_def] >>
      gvs[listTheory.EVERY_MEM] >>
      reverse conj_tac >- (qexists_tac `l` >> simp[]) >>
      rpt strip_tac >>
      `type_value_size tv < type_value_size (TupleTV tvs)` by
        (irule MEM_TupleTV_type_value_size >> simp[]) >>
      gvs[type_value_size_def] >>
      qpat_x_assum `!m. _` (qspec_then `type_value_size tv` mp_tac) >>
      simp[] >> disch_then (qspec_then `tv` mp_tac) >>
      simp[] >> disch_then irule >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >- (`!x ws b s. value_has_type t x /\ encode_value t x = SOME ws ==>
         slots_in_range (apply_writes (n2w b) ws s) b t` by
        (rpt strip_tac >>
         qpat_x_assum `!m. _` (qspec_then `type_value_size t` mp_tac) >>
         gvs[type_value_size_def] >>
         disch_then (qspec_then `t` mp_tac) >> simp[] >>
         disch_then irule >> simp[] >>
         gvs[well_formed_type_value_def] >> metis_tac[]) >>
      Cases_on `b`
      >- (Cases_on `v'` >> gvs[encode_value_def] >>
          Cases_on `a` >> gvs[encode_value_def] >>
          irule encode_fixed_array_slots_in_range >> simp[] >>
          conj_tac >- metis_tac[] >>
          qexists_tac `l` >> simp[encode_value_def]) >>
      Cases_on `v'` >> gvs[encode_value_def] >>
      Cases_on `a` >> gvs[encode_value_def, AllCaseEqs()] >>
      irule encode_dynamic_array_slots_in_range >>
      gvs[value_has_type_def] >> metis_tac[])
  >- (rename1 `StructTV ftypes` >>
      Cases_on `v'` >> gvs[encode_value_def] >>
      simp[Once slots_in_range_def] >>
      qspecl_then [`ftypes`, `0`] mp_tac encode_struct_slots_in_range >>
      simp[] >> disch_then irule >>
      gvs[value_has_type_def, well_formed_type_value_def, type_slot_size_def] >>
      gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >>
      reverse conj_tac >- (conj_tac >- metis_tac[] >>
                           qexists_tac `l` >> simp[]) >>
      rpt strip_tac >>
      `type_value_size p_2 < type_value_size (StructTV ftypes)` by
        (irule MEM_StructTV_type_value_size >> metis_tac[]) >>
      gvs[type_value_size_def] >>
      qpat_x_assum `!m. _` (qspec_then `type_value_size p_2` mp_tac) >>
      simp[] >> disch_then (qspec_then `p_2` mp_tac) >>
      simp[] >> disch_then irule >> metis_tac[])
  >- (irule encode_flag_slots_in_range >> metis_tac[]) >>
  simp[slots_in_range_def]
QED

(* Keep this encoding boundary free of admitted facts and extra assumptions. *)
val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag encode_implies_slots_in_range) in
    if null (Thm.hyp encode_implies_slots_in_range) andalso null axioms andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "encode_implies_slots_in_range is not closed"
  end;

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

(* Public decoder boundary: current in-range slots decode to a current,
   well-typed value.  Consumers need not unfold the mutually recursive
   decoder or retain a witness from an earlier state. *)
Theorem decode_value_from_slots_in_range:
  well_formed_type_value tv /\
  slots_in_range storage offset tv ==>
  ?v. decode_value storage offset tv = SOME v /\
      value_has_type tv v
Proof
  rpt strip_tac >>
  `?v. decode_value storage offset tv = SOME v` by
    metis_tac[CONJUNCT1 decode_value_total] >>
  qexists_tac `v` >> simp[] >>
  metis_tac[CONJUNCT1 decode_value_storable]
QED

(* ===== Inverse: storage_var_in_range implies typed lookup succeeds ===== *)

Theorem typed_lookup_from_storage_var_in_range_non_array:
  ∀cx st mid n tv.
    var_in_storage cx mid n ∧
    storage_var_in_range cx st mid n ∧
    storage_type_of cx mid n = SOME tv ∧
    (∀elem bd. tv ≠ ArrayTV elem bd) ⇒
    ?pv v.
      lookup_toplevel_name cx st mid n = SOME pv /\
      read_result cx pv st = (INL v,st) /\
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
  (* Resolution captures the storage location; loading is explicit. *)
  qexistsl_tac [`PlaceR (StoragePlace b (n2w offset) tv)`, `v`] >>
  simp[lookup_toplevel_name_def, Once lookup_global_def,
       read_result_def, read_place_def, bind_def,
       return_def, LET_THM, lift_option_type_def, lift_option_def,
       read_storage_slot_def]
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
      FST (read_result cx ref_v st) = INL v ∧
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
  MAP_EVERY qexists_tac [`PlaceR (StoragePlace b (n2w offset) (ArrayTV elem_tv bd))`, `v`] >>
  simp[] >>
  conj_tac >- (
    simp[lookup_toplevel_name_def, Once lookup_global_def, bind_def,
         return_def, LET_THM, lift_option_type_def]
  ) >>
  simp[read_result_def, read_place_def, read_storage_slot_def, bind_def, return_def,
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

Theorem lookup_toplevel_name_after_update_core[local]:
  ∀cx st mid n v.
    var_in_storage cx mid n ∧
    storable_value cx mid n v ⇒
    ∃ref_v.
      lookup_toplevel_name cx (update_toplevel_name cx st mid n v) mid n = SOME ref_v ∧
      FST (read_result cx ref_v (update_toplevel_name cx st mid n v)) = INL v
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
      encode_decode_roundtrip_ok_def, read_result_def, read_place_def] >>
  (* ArrayTV case: unfold set_global in read_result side *)
  simp[Once set_global_def, write_storage_slot_def,
       bind_def, lift_option_type_def, lift_option_def,
       return_def, LET_THM, raise_def,
       get_after_set_storage_backend] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem lookup_toplevel_name_read_result_after_update:
  ∀cx st mid n v.
    var_in_storage cx mid n ∧
    storable_value cx mid n v ⇒
    ∃ref_v.
      lookup_toplevel_name cx (update_toplevel_name cx st mid n v) mid n = SOME ref_v ∧
      FST (read_result cx ref_v (update_toplevel_name cx st mid n v)) = INL v
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
    ?pv. lookup_toplevel_name cx (update_toplevel_name cx st mid n v) mid n = SOME pv /\
      read_result cx pv (update_toplevel_name cx st mid n v) =
        (INL v, update_toplevel_name cx st mid n v)
Proof
  rpt strip_tac >>
  drule_all lookup_toplevel_name_after_update_core >> strip_tac >>
  first_x_assum (qspec_then `st` strip_assume_tac) >>
  qexists_tac `ref_v` >> simp[] >>
  Cases_on `read_result cx ref_v (update_toplevel_name cx st mid n v)` >>
  gvs[] >> drule read_result_state >> simp[]
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
QED

Theorem update_toplevel_name_preserves_well_formed_storage:
  well_formed_storage cx st ∧
  well_formed_layout cx ∧
  storable_value cx mid n v ∧
  var_in_storage cx mid n ⇒
  well_formed_storage cx (update_toplevel_name cx st mid n v)
Proof
  strip_tac >>
  `∃b1 off1 tv1.
     storage_var_info cx mid n = SOME (b1, off1, tv1) ∧
     well_formed_type_value tv1`
    by metis_tac[var_in_storage_storage_var_info] >>
  `off1 + type_slot_size tv1 ≤ dimword(:256)` by
    (fs[well_formed_layout_def] >> res_tac) >>
  `value_has_type tv1 v` by
    (fs[storable_value_def] >> first_x_assum irule >>
     simp[storage_type_of_def]) >>
  `IS_SOME (encode_value tv1 v)` by gvs[value_has_type_equiv] >>
  Cases_on `encode_value tv1 v` >> gvs[] >>
  rename1 `encode_value tv1 v = SOME writes` >>
  `∃storage0. get_storage_backend cx b1 st = (INL storage0, st)` by
    metis_tac[get_storage_backend_INL] >>
  `update_toplevel_name cx st mid n v =
     SND (set_storage_backend cx b1
       (apply_writes (n2w off1) writes storage0) st)` by (
    qpat_x_assum `storage_var_info cx mid n = _` mp_tac >>
    simp[storage_var_info_def, AllCaseEqs()] >> strip_tac >>
    simp[update_toplevel_name_def, Once set_global_def,
         write_storage_slot_def, bind_def, lift_option_type_def,
         lift_option_def, return_def, LET_THM, raise_def] >>
    qpat_x_assum `get_storage_backend cx b1 st = _` (fn th => simp[th])) >>
  simp[well_formed_storage_def] >>
  qx_gen_tac `mid2` >> qx_gen_tac `n2` >>
  simp[storage_var_in_range_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `b1 = is_transient`
  >- (
    pop_assum SUBST_ALL_TAC >>
    qpat_x_assum `get_storage_backend cx is_transient (SND _) = _` mp_tac >>
    simp[get_after_set_storage_backend] >> strip_tac >> gvs[] >>
    Cases_on `(mid,n) = (mid2,n2)`
    >- (
      gvs[] >>
      irule encode_implies_slots_in_range >>
      simp[] >> qexists_tac `v` >> simp[]
    ) >>
    `off + type_slot_size tv ≤ dimword(:256)` by
      (fs[well_formed_layout_def] >> res_tac) >>
    `off1 + type_slot_size tv1 ≤ off ∨
     off + type_slot_size tv ≤ off1` by (
      fs[well_formed_layout_def] >>
      first_x_assum drule_all >> simp[]) >>
    `slots_in_range storage0 off tv` by (
      qpat_x_assum `well_formed_storage cx st` mp_tac >>
      simp[well_formed_storage_def, storage_var_in_range_def] >>
      metis_tac[]) >>
    irule slots_in_range_disjoint_apply_writes >>
    simp[] >> qexists_tac `type_slot_size tv1` >> simp[] >>
    rpt strip_tac >>
    drule_all (CONJUNCT1 encode_writes_bounded) >> simp[]
  ) >>
  `∃storage2. get_storage_backend cx is_transient st = (INL storage2, st)` by
    metis_tac[get_storage_backend_INL] >>
  `storage2 = storage` by (
    `FST (get_storage_backend cx is_transient
       (SND (set_storage_backend cx b1
         (apply_writes (n2w off1) writes storage0) st))) =
     FST (get_storage_backend cx is_transient st)` by
      (irule get_after_set_other_backend >> simp[]) >>
    gvs[]) >>
  gvs[] >>
  qpat_x_assum `well_formed_storage cx st` mp_tac >>
  simp[well_formed_storage_def, storage_var_in_range_def] >>
  metis_tac[]
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
    ?pv. lookup_toplevel_name cx
      (update_toplevel_name cx st mid n (IntV new_val)) mid n = SOME pv /\
      read_result cx pv (update_toplevel_name cx st mid n (IntV new_val)) =
        (INL (IntV new_val), update_toplevel_name cx st mid n (IntV new_val))
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
    ?pv. lookup_toplevel_name cx
      (update_toplevel_name cx st mid n (IntV new_val)) mid n = SOME pv /\
      read_result cx pv (update_toplevel_name cx st mid n (IntV new_val)) =
        (INL (IntV new_val), update_toplevel_name cx st mid n (IntV new_val))
Proof
  rpt strip_tac >>
  irule lookup_toplevel_name_after_update >> simp[] >>
  irule storable_value_transfer_int >>
  simp[]
QED

Theorem get_module_code_stk:
  ∀cx s mid. get_module_code (cx with stk := s) mid = get_module_code cx mid
Proof
  simp[get_module_code_def]
QED

Theorem get_tenv_stk:
  ∀cx s. get_tenv (cx with stk := s) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem lookup_var_slot_from_layout_stk:
  ∀cx s is_transient mid id.
    lookup_var_slot_from_layout (cx with stk := s) is_transient mid id =
    lookup_var_slot_from_layout cx is_transient mid id
Proof
  simp[lookup_var_slot_from_layout_def]
QED

Theorem get_address_immutables_stk:
  ∀cx s st.
    get_address_immutables (cx with stk := s) st = get_address_immutables cx st
Proof
  simp[get_address_immutables_def]
QED

Theorem get_immutables_stk:
  ∀cx s mid st. get_immutables (cx with stk := s) mid st = get_immutables cx mid st
Proof
  simp[get_immutables_def, bind_def, get_address_immutables_stk]
QED

Theorem get_immutables_stk_fun[local]:
  ∀cx s mid. get_immutables (cx with stk := s) mid = get_immutables cx mid
Proof
  simp[FUN_EQ_THM, get_immutables_stk]
QED

Theorem get_storage_backend_stk:
  ∀cx s is_transient st.
    get_storage_backend (cx with stk := s) is_transient st =
    get_storage_backend cx is_transient st
Proof
  Cases_on `is_transient` >> simp[get_storage_backend_def]
QED

Theorem read_storage_slot_stk:
  ∀cx s is_transient slot tv st.
    read_storage_slot (cx with stk := s) is_transient slot tv st =
    read_storage_slot cx is_transient slot tv st
Proof
  simp[read_storage_slot_def, bind_def, get_storage_backend_stk]
QED

Theorem read_storage_slot_stk_fun[local]:
  ∀cx s is_transient slot tv.
    read_storage_slot (cx with stk := s) is_transient slot tv =
    read_storage_slot cx is_transient slot tv
Proof
  simp[FUN_EQ_THM, read_storage_slot_stk]
QED

Theorem lookup_global_stk:
  ∀cx s mid id st.
    lookup_global (cx with stk := s) mid id st =
    lookup_global cx mid id st
Proof
  rpt gen_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, ignore_bind_def,
       get_module_code_stk, get_tenv_stk,
       lookup_var_slot_from_layout_stk, get_immutables_stk_fun,
       read_storage_slot_stk_fun] >>
  rpt BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def] >>
  simp[get_immutables_stk_fun, read_storage_slot_stk_fun,
       get_storage_backend_def, get_address_immutables_def,
       bind_def, get_accounts_def, get_transient_storage_def,
       lift_option_def, return_def, raise_def]
QED

(* lookup_toplevel_name is independent of cx.stk *)
Theorem lookup_toplevel_name_stk:
  ∀cx s st mid m.
    lookup_toplevel_name (cx with stk := s) st mid m =
    lookup_toplevel_name cx st mid m
Proof
  rpt gen_tac >>
  simp[lookup_toplevel_name_def, lookup_global_stk]
QED

(* ===== Connecting lookup_toplevel_name with lookup_global ===== *)

Theorem lookup_toplevel_name_lookup_global:
  ∀cx st src_id_opt n href0.
    lookup_toplevel_name cx st src_id_opt n = SOME href0 ⇒
    lookup_global cx src_id_opt n st = (INL href0, st)
Proof
  rw[lookup_toplevel_name_def] >>
  Cases_on `lookup_global cx src_id_opt n st` >>
  Cases_on `q` >> gvs[] >>
  drule lookup_global_state >> simp[]
QED

Theorem lookup_global_get_module_code:
  ∀cx src_id_opt n st href0.
    lookup_global cx src_id_opt n st = (INL href0, st) ⇒
    ∃code. get_module_code cx src_id_opt = SOME code
Proof
  rw[lookup_global_def, bind_def, lift_option_type_def, raise_def] >>
  Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]
QED
