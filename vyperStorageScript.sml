(*
 * vyperStorageScript.sml
 *
 * Storage encoding/decoding for Vyper values to/from EVM storage slots.
 *)

Theory vyperStorage
Ancestors
  vyperInterpreter vfmState vfmTypes vfmConstants
Libs
  cv_transLib

(* ===== Basic Slot Encoding/Decoding ===== *)

Definition int_to_slot_def:
  int_to_slot (i : int) : bytes32 = n2w (Num (i % &(2 ** 256)))
End

Definition slot_to_uint_def:
  slot_to_uint (w : bytes32) : int = &(w2n w)
End

Definition slot_to_int_def:
  slot_to_int (bits : num) (w : bytes32) : int =
    let n = w2n w in
    let bound = 2 ** (bits - 1) in
    if n < bound then &n else &n - &(2 ** bits)
End

Definition bool_to_slot_def:
  bool_to_slot (b : bool) : bytes32 = if b then 1w else 0w
End

Definition slot_to_bool_def:
  slot_to_bool (w : bytes32) : bool = (w <> 0w)
End

(* ===== Bytes/String Slot Helpers ===== *)

Definition bytes_to_slots_def:
  bytes_to_slots (bs : word8 list) : bytes32 list =
    if NULL bs then []
    else
      let chunk = TAKE 32 bs in
      let rest = DROP 32 bs in
      let padded = chunk ++ REPLICATE (32 - LENGTH chunk) 0w in
      word_of_bytes F 0w padded :: bytes_to_slots rest
Termination
  WF_REL_TAC ‘measure LENGTH’ >> Cases_on ‘bs’ >> gvs[]
End

Definition slots_to_bytes_def:
  slots_to_bytes 0 _ = [] /\
  slots_to_bytes _ [] = [] /\
  slots_to_bytes len (slot::slots) =
    let bs = word_to_bytes slot F in
    let take_n = MIN 32 len in
    TAKE take_n bs ++ slots_to_bytes (len - take_n) slots
End

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

Definition type_slot_size_def:
  type_slot_size (BaseTV (BytesT (Dynamic n))) = 1 + word_size n /\
  type_slot_size (BaseTV (StringT n)) = 1 + word_size n /\
  type_slot_size (BaseTV _) = 1 /\
  type_slot_size (FlagTV _) = 1 /\
  type_slot_size NoneTV = 0 /\
  type_slot_size (TupleTV tvs) = SUM (MAP type_slot_size tvs) /\
  type_slot_size (ArrayTV tv (Fixed n)) = n * type_slot_size tv /\
  type_slot_size (ArrayTV tv (Dynamic n)) = 1 + n * type_slot_size tv /\
  type_slot_size (StructTV fields) = SUM (MAP (type_slot_size o SND) fields)
Termination
  WF_REL_TAC ‘measure type_value_size’ >> rw[type_value_size_def]
End

(* ===== Base Type Encoding ===== *)

Definition encode_base_to_slot_def:
  encode_base_to_slot (IntV (Unsigned n) i) (BaseTV (UintT m)) =
    (if n = m then SOME (int_to_slot i) else NONE) /\
  encode_base_to_slot (IntV (Signed n) i) (BaseTV (IntT m)) =
    (if n = m then SOME (int_to_slot i) else NONE) /\
  encode_base_to_slot (DecimalV i) (BaseTV DecimalT) = SOME (int_to_slot i) /\
  encode_base_to_slot (BoolV b) (BaseTV BoolT) = SOME (bool_to_slot b) /\
  encode_base_to_slot (BytesV (Fixed 20) bs) (BaseTV AddressT) =
    (if LENGTH bs = 20 then SOME (word_of_bytes T 0w bs) else NONE) /\
  encode_base_to_slot (BytesV (Fixed m) bs) (BaseTV (BytesT (Fixed n))) =
    (if m = n /\ LENGTH bs = n /\ n ≤ 32 then
       SOME (word_of_bytes F 0w (bs ++ REPLICATE (32 - n) 0w))
     else NONE) /\
  encode_base_to_slot (FlagV m k) (FlagTV m') =
    (if m = m' then SOME (n2w k) else NONE) /\
  encode_base_to_slot NoneV NoneTV = SOME 0w /\
  encode_base_to_slot _ _ = NONE
End

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

(* ===== Dynamic Bytes/String Encoding ===== *)

Definition encode_dyn_bytes_slots_def:
  encode_dyn_bytes_slots max bs =
    if LENGTH bs ≤ max then
      SOME ((0:num, n2w (LENGTH bs)) :: MAPi (λi s. (i + 1, s)) (bytes_to_slots bs))
    else NONE
End

Definition decode_dyn_bytes_slots_def:
  decode_dyn_bytes_slots max (reader : num -> bytes32) =
    let len = w2n (reader 0) in
    if len ≤ max then
      let n_slots = word_size len in
      let slots = GENLIST (λi. reader (i + 1)) n_slots in
      SOME (slots_to_bytes len slots)
    else NONE
End

(* ===== Storage Helpers ===== *)

Definition apply_writes_def:
  apply_writes (base_slot : bytes32) [] storage = storage /\
  apply_writes base_slot ((offset, val)::writes) storage =
    let slot : bytes32 = n2w (w2n base_slot + offset) in
    apply_writes base_slot writes (update_storage slot val storage)
End

Definition make_reader_def:
  make_reader (base_slot : bytes32) storage offset =
    lookup_storage (n2w (w2n base_slot + offset) : bytes32) storage
End

Definition offset_reader_def:
  offset_reader (reader : num -> bytes32) off = λn. reader (off + n)
End

(* ===== Termination helper lemmas for encode_value ===== *)

Theorem struct_fields_size_lt:
  ∀fields. list_size (pair_size (λx. 0) value_size) fields <
           list_size (pair_size (list_size char_size) value_size) fields + 1
Proof
  Induct >> rw[] >> Cases_on ‘h’ >> rw[]
QED

Theorem list_size_pair_0_le:
  ∀sparse. list_size (pair_size (λx:num. 0) value_size) sparse ≤
           list_size (pair_size (λx. x) value_size) sparse
Proof
  Induct >> rw[] >> Cases_on ‘h’ >> rw[]
QED

Theorem sparse_size_lt:
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

(* ===== Termination helper lemmas for decode_value ===== *)

Theorem type_value1_size_le:
  ∀ftypes. type_value1_size ftypes ≤
    list_size (pair_size (list_size char_size) type_value_size) ftypes
Proof
  Induct >> rw[type_value_size_def] >> Cases_on ‘h’ >> rw[type_value_size_def]
QED

(* ===== Full Value Decoding ===== *)

Definition decode_value_def:
  (* Dynamic bytes - special multi-slot decoding *)
  decode_value (BaseTV (BytesT (Dynamic max))) reader =
    (case decode_dyn_bytes_slots max reader of
     | SOME bs => SOME (BytesV (Dynamic max) bs)
     | NONE => NONE) /\
  (* String - decode as bytes then convert to chars *)
  decode_value (BaseTV (StringT max)) reader =
    (case decode_dyn_bytes_slots max reader of
     | SOME bs => SOME (StringV max (MAP (CHR o w2n) bs))
     | NONE => NONE) /\
  (* Other base types - single slot *)
  decode_value (BaseTV bt) reader =
    SOME (decode_base_from_slot (reader 0) (BaseTV bt)) /\
  decode_value (FlagTV m) reader =
    SOME (decode_base_from_slot (reader 0) (FlagTV m)) /\
  decode_value NoneTV reader = SOME NoneV /\
  decode_value (TupleTV tvs) reader =
    (case decode_tuple 0 tvs reader of
     | SOME vs => SOME (ArrayV (TupleV vs))
     | NONE => NONE) /\
  decode_value (ArrayTV tv (Fixed n)) reader =
    (case decode_static_array tv 0 n reader of
     | SOME vs => SOME (ArrayV (SArrayV tv n (enumerate_static_array (default_value tv) 0 vs)))
     | NONE => NONE) /\
  decode_value (ArrayTV tv (Dynamic max)) reader =
    (let len = w2n (reader 0) in
     if len ≤ max then
       (case decode_dyn_array tv 1 len reader of
        | SOME vs => SOME (ArrayV (DynArrayV tv max vs))
        | NONE => NONE)
     else NONE) /\
  decode_value (StructTV ftypes) reader =
    (case decode_struct 0 ftypes reader of
     | SOME fields => SOME (StructV fields)
     | NONE => NONE) /\

  decode_tuple offset [] reader = SOME [] /\
  decode_tuple offset (tv::tvs) reader =
    (case decode_value tv (offset_reader reader offset) of
     | SOME v =>
         (case decode_tuple (offset + type_slot_size tv) tvs reader of
          | SOME vs => SOME (v :: vs)
          | NONE => NONE)
     | NONE => NONE) /\

  decode_static_array tv offset 0 reader = SOME [] /\
  decode_static_array tv offset (SUC n) reader =
    (case decode_value tv (offset_reader reader offset) of
     | SOME v =>
         (case decode_static_array tv (offset + type_slot_size tv) n reader of
          | SOME vs => SOME (v :: vs)
          | NONE => NONE)
     | NONE => NONE) /\

  decode_dyn_array tv offset 0 reader = SOME [] /\
  decode_dyn_array tv offset (SUC n) reader =
    (case decode_value tv (offset_reader reader offset) of
     | SOME v =>
         (case decode_dyn_array tv (offset + type_slot_size tv) n reader of
          | SOME vs => SOME (v :: vs)
          | NONE => NONE)
     | NONE => NONE) /\

  decode_struct offset [] reader = SOME [] /\
  decode_struct offset ((fname,tv)::ftypes) reader =
    (case decode_value tv (offset_reader reader offset) of
     | SOME v =>
         (case decode_struct (offset + type_slot_size tv) ftypes reader of
          | SOME fields => SOME ((fname, v) :: fields)
          | NONE => NONE)
     | NONE => NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (tv, _) => type_value_size tv
    | INR (INL (_, tvs, _)) => list_size type_value_size tvs
    | INR (INR (INL (tv, _, n, _))) => type_value_size tv + n
    | INR (INR (INR (INL (tv, _, n, _)))) => type_value_size tv + n
    | INR (INR (INR (INR (_, ftypes, _)))) => type_value1_size ftypes)’ >>
  rw[type_value_size_def] >>
  ‘type_value1_size ftypes ≤
   list_size (pair_size (list_size char_size) type_value_size) ftypes’
   by rw[type_value1_size_le] >> simp[]
End

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
  encode_hashmap_key (BytesV (Fixed 20) bs) = 
    (if LENGTH bs = 20 then SOME (word_of_bytes T 0w bs) else NONE) ∧
  encode_hashmap_key (BytesV (Fixed 32) bs) =
    (if LENGTH bs = 32 then SOME (word_of_bytes T 0w bs) else NONE) ∧
  encode_hashmap_key (BoolV b) = SOME (if b then 1w else 0w) ∧
  encode_hashmap_key _ = NONE
End

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
        let base_slot : bytes32 = n2w slot in
        let reader = make_reader base_slot storage in
        decode_value tv reader
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
        (case hashmap_value_slot base_slot key_val of
         | NONE => NONE
         | SOME entry_slot =>
             let reader = make_reader entry_slot storage in
             decode_value value_tv reader)
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
        (case nested_hashmap_slot base_slot keys of
         | NONE => NONE
         | SOME entry_slot =>
             let reader = make_reader entry_slot storage in
             decode_value value_tv reader)
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
