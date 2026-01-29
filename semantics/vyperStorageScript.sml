(*
 * vyperStorageScript.sml
 *
 * Storage encoding/decoding for Vyper values to/from EVM storage slots.
 *)

Theory vyperStorage
Ancestors
  vyperTypeValue vfmState vfmTypes vfmConstants
  vyperMisc
Libs
  cv_transLib wordsLib

(* ===== Basic Slot Encoding/Decoding ===== *)

Definition int_to_slot_def:
  int_to_slot (i : int) : bytes32 = i2w i
End
val () = cv_auto_trans int_to_slot_def;

Definition slot_to_uint_def:
  slot_to_uint (w : bytes32) : int = &(w2n w)
End
val () = cv_auto_trans slot_to_uint_def;

Definition slot_to_int_def:
  slot_to_int (bits : num) (w : bytes32) : int =
    let n = w2n w in
    let bound = 2 ** (bits - 1) in
    if n < bound then &n else &n - &(2 ** bits)
End
val () = cv_auto_trans slot_to_int_def;

Definition bool_to_slot_def:
  bool_to_slot (b : bool) : bytes32 = if b then 1w else 0w
End
val () = cv_auto_trans bool_to_slot_def;

Definition slot_to_bool_def:
  slot_to_bool (w : bytes32) : bool = (w <> 0w)
End
val () = cv_auto_trans slot_to_bool_def;

(* ===== Bytes/String Slot Helpers ===== *)

Definition bytes_to_slots_aux_def:
  bytes_to_slots_aux acc ([]:byte list) = REVERSE acc /\
  bytes_to_slots_aux acc bs =
    let chunk = TAKE 32 bs in
    let rest = DROP 32 bs in
    let padded = chunk ++ REPLICATE (32 - LENGTH chunk) 0w in
    bytes_to_slots_aux (word_of_bytes F (0w: bytes32) padded :: acc) rest
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ >> gvs[]
End

Definition bytes_to_slots_def:
  bytes_to_slots bs = bytes_to_slots_aux [] bs
End

val () = cv_auto_trans bytes_to_slots_aux_def;
val () = cv_auto_trans bytes_to_slots_def;

Definition slots_to_bytes_def:
  slots_to_bytes 0 _ = ([]:byte list) /\
  slots_to_bytes _ [] = [] /\
  slots_to_bytes len ((slot:bytes32)::slots) =
    let bs = word_to_bytes slot F in
    let take_n = MIN 32 len in
    TAKE take_n bs ++ slots_to_bytes (len - take_n) slots
End
val () = cv_auto_trans slots_to_bytes_def;

(* ===== Slot Size Computation ===== *)

Definition base_type_slot_size_def:
  base_type_slot_size (UintT _) = 1 /\
  base_type_slot_size (IntT _) = 1 /\
  base_type_slot_size DecimalT = 1 /\
  base_type_slot_size BoolT = 1 /\
  base_type_slot_size AddressT = 1 /\
  base_type_slot_size (BytesT (Fixed _)) = 1 /\
  base_type_slot_size (BytesT (Dynamic n)) = 1 + word_size n /\
  base_type_slot_size (StringT n) = 1 + word_size n
End
val () = cv_auto_trans base_type_slot_size_def;

Definition type_slot_size_def:
  type_slot_size (BaseTV (BytesT (Dynamic n))) = 1 + word_size n /\
  type_slot_size (BaseTV (StringT n)) = 1 + word_size n /\
  type_slot_size (BaseTV _) = 1 /\
  type_slot_size (FlagTV _) = 1 /\
  type_slot_size NoneTV = 0 /\
  type_slot_size (TupleTV tvs) = type_slot_size_list tvs /\
  type_slot_size (ArrayTV tv (Fixed n)) = n * type_slot_size tv /\
  type_slot_size (ArrayTV tv (Dynamic n)) = 1 + n * type_slot_size tv /\
  type_slot_size (StructTV fields) = type_slot_size_fields fields /\
  type_slot_size_list [] = 0 /\
  type_slot_size_list (tv::tvs) = type_slot_size tv + type_slot_size_list tvs /\
  type_slot_size_fields [] = 0 /\
  type_slot_size_fields ((_, tv)::fields) = type_slot_size tv + type_slot_size_fields fields
End
val () = cv_auto_trans type_slot_size_def;

(* ===== Base Type Encoding ===== *)

Definition encode_base_to_slot_def:
  encode_base_to_slot (IntV (Unsigned n) i) (BaseTV (UintT m)) =
    (if n = m then SOME (int_to_slot i) else NONE) /\
  encode_base_to_slot (IntV (Signed n) i) (BaseTV (IntT m)) =
    (if n = m then SOME (int_to_slot i) else NONE) /\
  encode_base_to_slot (DecimalV i) (BaseTV DecimalT) = SOME (int_to_slot i) /\
  encode_base_to_slot (BoolV b) (BaseTV BoolT) = SOME (bool_to_slot b) /\
  encode_base_to_slot (BytesV (Fixed m) bs) (BaseTV AddressT) =
    (if LENGTH bs = m /\ m = 20 then SOME (word_of_bytes T 0w bs) else NONE) /\
  encode_base_to_slot (BytesV (Fixed m) bs) (BaseTV (BytesT (Fixed n))) =
    (if m = n /\ LENGTH bs = n /\ n ≤ 32 then
       SOME (word_of_bytes F 0w (bs ++ REPLICATE (32 - n) 0w))
     else NONE) /\
  encode_base_to_slot (FlagV m k) (FlagTV m') =
    (if m = m' then SOME (n2w k) else NONE) /\
  encode_base_to_slot NoneV NoneTV = SOME 0w /\
  encode_base_to_slot _ _ = NONE
End
val () = cv_auto_trans encode_base_to_slot_def;

Definition decode_base_from_slot_def:
  decode_base_from_slot (slot : bytes32) (BaseTV (UintT n)) =
    IntV (Unsigned n) (slot_to_uint slot) /\
  decode_base_from_slot slot (BaseTV (IntT n)) =
    IntV (Signed n) (slot_to_int n slot) /\
  decode_base_from_slot slot (BaseTV DecimalT) = DecimalV (slot_to_int 168 slot) /\
  decode_base_from_slot slot (BaseTV BoolT) = BoolV (slot_to_bool slot) /\
  decode_base_from_slot slot (BaseTV AddressT) =
    BytesV (Fixed 20) (DROP 12 (word_to_bytes slot T)) /\
  decode_base_from_slot slot (BaseTV (BytesT (Fixed n))) =
    BytesV (Fixed n) (TAKE n (word_to_bytes slot F)) /\
  decode_base_from_slot slot (FlagTV m) = FlagV m (w2n slot) /\
  decode_base_from_slot slot NoneTV = NoneV /\
  decode_base_from_slot slot _ = NoneV
End
val () = cv_auto_trans decode_base_from_slot_def;

(* ===== Dynamic Bytes/String Encoding ===== *)

Definition encode_dyn_bytes_slots_def:
  encode_dyn_bytes_slots max bs =
    if LENGTH bs ≤ max then
      SOME ((0:num, n2w (LENGTH bs)) :: MAPi (λi s. (i + 1, s)) (bytes_to_slots bs))
    else NONE
End
val () = cv_auto_trans encode_dyn_bytes_slots_def;

(* First-order helper: read n consecutive slots starting at offset *)
Definition read_slots_def:
  read_slots storage offset 0 = ([]:bytes32 list) /\
  read_slots storage offset (SUC n) =
    lookup_storage (n2w offset : bytes32) storage :: read_slots storage (offset + 1) n
End
val () = cv_auto_trans read_slots_def;

Definition decode_dyn_bytes_def:
  decode_dyn_bytes storage offset max =
    let len = w2n (lookup_storage (n2w offset : bytes32) storage) in
    if len ≤ max then
      let n_slots = word_size len in
      let slots = read_slots storage (offset + 1) n_slots in
      SOME (slots_to_bytes len slots, 1 + n_slots)
    else NONE
End
val () = cv_auto_trans decode_dyn_bytes_def;

(* ===== Storage Helpers ===== *)

Definition apply_writes_def:
  apply_writes (base_slot : bytes32) [] storage = storage /\
  apply_writes base_slot ((offset, val)::writes) storage =
    let slot : bytes32 = n2w (w2n base_slot + offset) in
    apply_writes base_slot writes (update_storage slot val storage)
End
val () = cv_trans apply_writes_def;

(* Helper to read a slot at a given offset from storage *)
Definition read_slot_def:
  read_slot storage offset = lookup_storage (n2w offset : bytes32) storage
End
val () = cv_auto_trans read_slot_def;

(* ===== Termination helper lemmas for encode_value ===== *)

Theorem struct_fields_size_lt[local]:
  ∀fields. list_size (pair_size (λx. 0) value_size) fields <
           list_size (pair_size (list_size char_size) value_size) fields + 1
Proof
  Induct >> rw[] >> Cases_on ‘h’ >> rw[]
QED

Theorem list_size_pair_0_le[local]:
  ∀sparse. list_size (pair_size (λx:num. 0) value_size) sparse ≤
           list_size (pair_size (λx. x) value_size) sparse
Proof
  Induct >> rw[] >> Cases_on ‘h’ >> rw[]
QED

Theorem sparse_size_lt[local]:
  ∀sparse n tv. list_size (pair_size (λx. 0) value_size) sparse <
    n + (type_value_size tv + (list_size (pair_size (λx. x) value_size) sparse + 2))
Proof
  rw[] >>
  ‘list_size (pair_size (λx. 0) value_size) sparse ≤
   list_size (pair_size (λx. x) value_size) sparse’ by rw[list_size_pair_0_le] >>
  simp[]
QED

(* ===== Full Value Encoding ===== *)

Definition encode_value_def:
  (* Dynamic bytes - special multi-slot encoding *)
  encode_value (BaseTV (BytesT (Dynamic max))) (BytesV (Dynamic m) bs) =
    (if max = m then encode_dyn_bytes_slots max bs else NONE) /\
  (* String - encode as bytes *)
  encode_value (BaseTV (StringT max)) (StringV m s) =
    (if max = m then encode_dyn_bytes_slots max (MAP (n2w o ORD) s) else NONE) /\
  (* Other base types - single slot *)
  encode_value (BaseTV bt) v =
    (case encode_base_to_slot v (BaseTV bt) of
     | SOME slot => SOME [(0:num, slot)]
     | NONE => NONE) /\
  encode_value (FlagTV m) v =
    (case encode_base_to_slot v (FlagTV m) of
     | SOME slot => SOME [(0, slot)]
     | NONE => NONE) /\
  encode_value NoneTV v = SOME [] /\
  encode_value (TupleTV tvs) (ArrayV (TupleV vs)) =
    encode_tuple 0 tvs vs /\
  encode_value (ArrayTV tv (Fixed n)) (ArrayV (SArrayV tv' m sparse)) =
    (if tv = tv' /\ n = m then encode_static_array tv 0 sparse else NONE) /\
  encode_value (ArrayTV tv (Dynamic max)) (ArrayV (DynArrayV tv' m vs)) =
    (if tv = tv' /\ max = m then
       (case encode_dyn_array tv 1 vs of
        | SOME slots => SOME ((0, n2w (LENGTH vs)) :: slots)
        | NONE => NONE)
     else NONE) /\
  encode_value (StructTV ftypes) (StructV fields) =
    encode_struct 0 ftypes fields /\
  encode_value _ _ = NONE /\

  encode_tuple offset [] [] = SOME [] /\
  encode_tuple offset (tv::tvs) (v::vs) =
    (case encode_value tv v of
     | SOME slots =>
         let shifted = MAP (λ(off,s). (off + offset, s)) slots in
         (case encode_tuple (offset + type_slot_size tv) tvs vs of
          | SOME rest => SOME (shifted ++ rest)
          | NONE => NONE)
     | NONE => NONE) /\
  encode_tuple offset _ _ = NONE /\

  encode_static_array tv offset [] = SOME [] /\
  encode_static_array tv offset ((k,v)::rest) =
    (case encode_value tv v of
     | SOME slots =>
         let shifted = MAP (λ(off,s). (off + offset + k * type_slot_size tv, s)) slots in
         (case encode_static_array tv offset rest of
          | SOME rest_slots => SOME (shifted ++ rest_slots)
          | NONE => NONE)
     | NONE => NONE) /\

  encode_dyn_array tv offset [] = SOME [] /\
  encode_dyn_array tv offset (v::vs) =
    (case encode_value tv v of
     | SOME slots =>
         let shifted = MAP (λ(off,s). (off + offset, s)) slots in
         (case encode_dyn_array tv (offset + type_slot_size tv) vs of
          | SOME rest => SOME (shifted ++ rest)
          | NONE => NONE)
     | NONE => NONE) /\

  encode_struct offset [] [] = SOME [] /\
  encode_struct offset ((fname,tv)::ftypes) ((vname,v)::fields) =
    (if fname = vname then
       (case encode_value tv v of
        | SOME slots =>
            let shifted = MAP (λ(off,s). (off + offset, s)) slots in
            (case encode_struct (offset + type_slot_size tv) ftypes fields of
             | SOME rest => SOME (shifted ++ rest)
             | NONE => NONE)
        | NONE => NONE)
     else NONE) /\
  encode_struct offset _ _ = NONE
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (_, v) => value_size v
    | INR (INL (_, _, vs)) => list_size value_size vs
    | INR (INR (INL (_, _, sparse))) => list_size (pair_size (λx.0) value_size) sparse
    | INR (INR (INR (INL (_, _, vs)))) => list_size value_size vs
    | INR (INR (INR (INR (_, _, fields)))) => list_size (pair_size (λx.0) value_size) fields)’ >>
  rw[struct_fields_size_lt, sparse_size_lt]
End

val encode_value_pre_def =
  cv_auto_trans_pre
    "encode_value_pre encode_tuple_pre encode_static_array_pre encode_dyn_array_pre encode_struct_pre"
    encode_value_def;

Theorem encode_value_pre[cv_pre]:
  (∀tv v. encode_value_pre tv v) ∧
  (∀offset tvs vs. encode_tuple_pre offset tvs vs) ∧
  (∀tv offset sparse. encode_static_array_pre tv offset sparse) ∧
  (∀tv offset vs. encode_dyn_array_pre tv offset vs) ∧
  (∀offset ftypes fields. encode_struct_pre offset ftypes fields)
Proof
  ho_match_mp_tac encode_value_ind
  \\ rw[]
  \\ rw[Once encode_value_pre_def]
QED

(* ===== Termination helper lemmas for decode_value ===== *)

Theorem type_value1_size_le[local]:
  ∀ftypes. type_value1_size ftypes ≤
    list_size (pair_size (list_size char_size) type_value_size) ftypes
Proof
  Induct >> rw[type_value_size_def] >> Cases_on ‘h’ >> rw[type_value_size_def]
QED

(* ===== Full Value Decoding (First-Order) ===== *)

(* decode_value returns SOME (value, slots_consumed) or NONE *)
Definition decode_value_def:
  (* Dynamic bytes - special multi-slot decoding *)
  decode_value storage offset (BaseTV (BytesT (Dynamic max))) =
    (case decode_dyn_bytes storage offset max of
     | SOME (bs, n) => SOME (BytesV (Dynamic max) bs, n)
     | NONE => NONE) /\
  (* String - decode as bytes then convert to chars *)
  decode_value storage offset (BaseTV (StringT max)) =
    (case decode_dyn_bytes storage offset max of
     | SOME (bs, n) => SOME (StringV max (MAP (CHR o w2n) bs), n)
     | NONE => NONE) /\
  (* Other base types - single slot *)
  decode_value storage offset (BaseTV bt) =
    SOME (decode_base_from_slot (read_slot storage offset) (BaseTV bt), 1) /\
  decode_value storage offset (FlagTV m) =
    SOME (decode_base_from_slot (read_slot storage offset) (FlagTV m), 1) /\
  decode_value storage offset NoneTV = SOME (NoneV, 0) /\
  decode_value storage offset (TupleTV tvs) =
    (case decode_tuple storage offset tvs of
     | SOME (vs, n) => SOME (ArrayV (TupleV vs), n)
     | NONE => NONE) /\
  decode_value storage offset (ArrayTV tv (Fixed n)) =
    (case decode_static_array storage offset tv n of
     | SOME (vs, slots) => SOME (ArrayV (SArrayV tv n (enumerate_static_array (default_value tv) 0 vs)), slots)
     | NONE => NONE) /\
  decode_value storage offset (ArrayTV tv (Dynamic max)) =
    (let len = w2n (read_slot storage offset) in
     if len ≤ max then
       (case decode_dyn_array storage (offset + 1) tv (MIN len max) of
        | SOME (vs, slots) => SOME (ArrayV (DynArrayV tv max vs), 1 + slots)
        | NONE => NONE)
     else NONE) /\
  decode_value storage offset (StructTV ftypes) =
    (case decode_struct storage offset ftypes of
     | SOME (fields, n) => SOME (StructV fields, n)
     | NONE => NONE) /\

  decode_tuple storage offset [] = SOME ([], 0) /\
  decode_tuple storage offset (tv::tvs) =
    (case decode_value storage offset tv of
     | SOME (v, n) =>
         (case decode_tuple storage (offset + n) tvs of
          | SOME (vs, m) => SOME (v :: vs, n + m)
          | NONE => NONE)
     | NONE => NONE) /\

  decode_static_array storage offset tv 0 = SOME ([], 0) /\
  decode_static_array storage offset tv (SUC n) =
    (case decode_value storage offset tv of
     | SOME (v, slots) =>
         (case decode_static_array storage (offset + slots) tv n of
          | SOME (vs, rest) => SOME (v :: vs, slots + rest)
          | NONE => NONE)
     | NONE => NONE) /\

  decode_dyn_array storage offset tv 0 = SOME ([], 0) /\
  decode_dyn_array storage offset tv (SUC n) =
    (case decode_value storage offset tv of
     | SOME (v, slots) =>
         (case decode_dyn_array storage (offset + slots) tv n of
          | SOME (vs, rest) => SOME (v :: vs, slots + rest)
          | NONE => NONE)
     | NONE => NONE) /\

  decode_struct storage offset [] = SOME ([], 0) /\
  decode_struct storage offset ((fname,tv)::ftypes) =
    (case decode_value storage offset tv of
     | SOME (v, n) =>
         (case decode_struct storage (offset + n) ftypes of
          | SOME (fields, m) => SOME ((fname, v) :: fields, n + m)
          | NONE => NONE)
     | NONE => NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (_, _, tv) => type_value_size tv
    | INR (INL (_, _, tvs)) => list_size type_value_size tvs
    | INR (INR (INL (_, _, tv, n))) => type_value_size tv + n
    | INR (INR (INR (INL (_, _, tv, n)))) => type_value_size tv + n
    | INR (INR (INR (INR (_, _, ftypes)))) => type_value1_size ftypes)’ >>
  rw[type_value_size_def] >>
  ‘type_value1_size ftypes ≤
   list_size (pair_size (list_size char_size) type_value_size) ftypes’
   by rw[type_value1_size_le] >> simp[arithmeticTheory.MIN_DEF]
End

(* TODO: refactor helper theorems into a shared library
   (duplicated from vyperABIScript.sml) *)

Theorem c2n_le_cv_size:
  !x. cv$c2n x <= cv_size x
Proof
  Cases >> rw[cvTheory.c2n_def, cvTheory.cv_size_def]
QED

val decode_value_pre_def =
  cv_auto_trans_pre_rec
    "decode_value_pre decode_tuple_pre decode_static_array_pre decode_dyn_array_pre decode_struct_pre"
    (decode_value_def |> REWRITE_RULE[GSYM CHR_o_w2n_eq])
    (WF_REL_TAC `inv_image $<
       (λx. case x of
         | INL (storage, offset, tv) => cv_size tv
         | INR (INL (storage, offset, tvs)) => cv_size tvs
         | INR (INR (INL (storage, offset, tv, n))) => cv_size tv + cv$c2n n
         | INR (INR (INR (INL (storage, offset, tv, n)))) => cv_size tv + cv$c2n n
         | INR (INR (INR (INR (storage, offset, ftypes)))) => cv_size ftypes)`
     \\ rw[]
     \\ TRY (gvs[cv_repTheory.cv_termination_simp, cvTheory.cv_size_def,
                 cvTheory.cv_snd_def, cvTheory.cv_fst_def]
             \\ decide_tac \\ NO_TAC)
     (* Handle ArrayTV Dynamic cases - need case splits to expose Pair overhead *)
     \\ rpt strip_tac
     \\ Cases_on `cv_v`
     >> gvs[cvTheory.cv_ispair_def, cvTheory.c2b_def]
     \\ rename1 `cv_size (cv_fst rest1)`
     \\ Cases_on `rest1`
     >> gvs[cvTheory.cv_ispair_def, cvTheory.c2b_def, cvTheory.cv_lt_def,
            cvTheory.cv_fst_def, cvTheory.cv_snd_def, cvTheory.cv_size_def]
     \\ (rename1 `cv_ispair rest2` ORELSE rename1 `cv_fst rest2`)
     \\ Cases_on `rest2`
     >> gvs[cvTheory.cv_ispair_def, cvTheory.c2b_def, cvTheory.cv_lt_def,
            cvTheory.cv_fst_def, cvTheory.cv_snd_def, cvTheory.cv_size_def]
     \\ rename1`cv_lt (cv$Num _) nn = cv$Num _`
     \\ Cases_on`nn` \\ gvs[CaseEq"bool"]
     \\ rename1`cv_lt (cv$Num _) nn = cv$Num _`
     \\ Cases_on`nn` \\ gvs[CaseEq"bool"]
     \\ qmatch_goalsub_abbrev_tac`cv$c2n nn`
     \\ qspec_then`nn`assume_tac c2n_le_cv_size
     \\ gvs[cv_primTheory.cv_min_def]
     \\ rename1`cv_lt n1 n2`
     \\ Cases_on`cv_lt n1 n2` \\ gvs[]
     \\ TRY(Cases_on`n1` \\ Cases_on `n2` \\ gvs[cvTheory.cv_lt_def] \\ NO_TAC)
     \\ rename1`cv$c2b (cv$Num bb)`
     \\ Cases_on`bb` \\ gvs[]
     \\ Cases_on`n1` \\ Cases_on `n2` \\ gvs[cvTheory.cv_lt_def]
    );

Theorem decode_value_pre[cv_pre]:
  (∀storage offset tv. decode_value_pre storage offset tv) ∧
  (∀storage offset tvs. decode_tuple_pre storage offset tvs) ∧
  (∀storage offset tv n. decode_static_array_pre storage offset tv n) ∧
  (∀storage offset tv n. decode_dyn_array_pre storage offset tv n) ∧
  (∀storage offset ftypes. decode_struct_pre storage offset ftypes)
Proof
  ho_match_mp_tac decode_value_ind
  \\ rw[]
  \\ rw[Once decode_value_pre_def]
  \\ gvs[]
QED

(* ===== HashMap Slot Computation ===== *)

(* Basic hashmap slot: keccak256(key ++ base_slot)
   Both key and base_slot are 32 bytes, big-endian encoded *)
Definition hashmap_slot_def:
  hashmap_slot (base_slot : bytes32) (key : bytes32) : bytes32 =
    word_of_bytes T 0w (Keccak_256_w64 (word_to_bytes key T ++ word_to_bytes base_slot T))
End

(* Encode a Vyper value as a 32-byte hashmap key.
   Integers: encoded as 256-bit big-endian
   Addresses: left-padded to 32 bytes
   Fixed bytes32: as-is
   Booleans: 0 or 1 *)
Definition encode_hashmap_key_def:
  encode_hashmap_key (IntV _ i) = SOME (int_to_slot i) ∧
  encode_hashmap_key (BytesV (Fixed n) bs) =
    (if LENGTH bs = n ∧ (n = 32 ∨ n = 20)
     then SOME (word_of_bytes T 0w bs) else NONE) ∧
  encode_hashmap_key (BoolV b) = SOME (if b then 1w else 0w) ∧
  encode_hashmap_key _ = NONE
End

val () = cv_trans encode_hashmap_key_def;

(* Compute slot for a hashmap value given base slot and key value *)
Definition hashmap_value_slot_def:
  hashmap_value_slot base_slot key_val =
    case encode_hashmap_key key_val of
    | SOME key => SOME (hashmap_slot base_slot key)
    | NONE => NONE
End

(* For nested hashmaps HashMap[K1, HashMap[K2, V]],
   compute: hashmap_slot (hashmap_slot base k1) k2 *)
Definition nested_hashmap_slot_def:
  nested_hashmap_slot base_slot [] = SOME base_slot ∧
  nested_hashmap_slot base_slot (k::ks) =
    case encode_hashmap_key k of
    | SOME key => nested_hashmap_slot (hashmap_slot base_slot key) ks
    | NONE => NONE
End

(* ===== Top-Level Variable Access ===== *)

(* Storage layout: maps variable names to their base slot numbers.
   This is a simplified representation - the full json_storage_layout
   from jsonAST includes additional info like n_slots and type_str,
   but for storage access we only need the base slot. *)
Type storage_layout = “:(string # num) list”

(* Enriched storage layout entry: slot number and type for a variable *)
Datatype:
  var_storage_info = <|
    var_slot : num;
    var_type : type_value
  |>
End

(* Enriched storage layout: maps variable keys (num) to storage info.
   Used at runtime for reading/writing variables to EVM storage. *)
Type var_layout = “:var_storage_info spt”

(* Look up base slot for a variable name *)
Definition lookup_var_slot_def:
  lookup_var_slot (layout : storage_layout) (var_name : string) : num option =
    ALOOKUP layout var_name
End

(* Read a top-level variable from storage *)
Definition read_storage_var_def:
  read_storage_var layout (storage : storage) var_name tv =
    case lookup_var_slot layout var_name of
    | NONE => NONE
    | SOME slot =>
        case decode_value storage slot tv of
        | SOME (v, _) => SOME v
        | NONE => NONE
End

(* Write a top-level variable to storage *)
Definition write_storage_var_def:
  write_storage_var layout (storage : storage) var_name tv v =
    case lookup_var_slot layout var_name of
    | NONE => NONE
    | SOME slot =>
        (case encode_value tv v of
         | NONE => NONE
         | SOME writes =>
             let base_slot : bytes32 = n2w slot in
             SOME (apply_writes base_slot writes storage))
End

(* ===== HashMap Variable Access ===== *)

(* Read a HashMap entry: HashMap[K, V] at var_name with key *)
Definition read_hashmap_var_def:
  read_hashmap_var layout (storage : storage) var_name key_val value_tv =
    case lookup_var_slot layout var_name of
    | NONE => NONE
    | SOME slot =>
        let base_slot : bytes32 = n2w slot in
        case hashmap_value_slot base_slot key_val of
        | NONE => NONE
        | SOME entry_slot =>
            case decode_value storage (w2n entry_slot) value_tv of
            | SOME (v, _) => SOME v
            | NONE => NONE
End

(* Write a HashMap entry *)
Definition write_hashmap_var_def:
  write_hashmap_var layout (storage : storage) var_name key_val value_tv v =
    case lookup_var_slot layout var_name of
    | NONE => NONE
    | SOME slot =>
        let base_slot : bytes32 = n2w slot in
        (case hashmap_value_slot base_slot key_val of
         | NONE => NONE
         | SOME entry_slot =>
             (case encode_value value_tv v of
              | NONE => NONE
              | SOME writes => SOME (apply_writes entry_slot writes storage)))
End

(* Read a nested HashMap entry: HashMap[K1, HashMap[K2, V]] *)
Definition read_nested_hashmap_var_def:
  read_nested_hashmap_var layout (storage : storage) var_name keys value_tv =
    case lookup_var_slot layout var_name of
    | NONE => NONE
    | SOME slot =>
        let base_slot : bytes32 = n2w slot in
        case nested_hashmap_slot base_slot keys of
        | NONE => NONE
        | SOME entry_slot =>
            case decode_value storage (w2n entry_slot) value_tv of
            | SOME (v, _) => SOME v
            | NONE => NONE
End

(* Write a nested HashMap entry *)
Definition write_nested_hashmap_var_def:
  write_nested_hashmap_var layout (storage : storage) var_name keys value_tv v =
    case lookup_var_slot layout var_name of
    | NONE => NONE
    | SOME slot =>
        let base_slot : bytes32 = n2w slot in
        (case nested_hashmap_slot base_slot keys of
         | NONE => NONE
         | SOME entry_slot =>
             (case encode_value value_tv v of
              | NONE => NONE
              | SOME writes => SOME (apply_writes entry_slot writes storage)))
End
