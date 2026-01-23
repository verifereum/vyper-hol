(*
 * vyperStorageScript.sml
 *
 * Storage encoding/decoding for Vyper values to/from EVM storage slots.
 *)

Theory vyperStorage
Ancestors
  vyperInterpreter vfmState vfmTypes
Libs
  cv_transLib

(* ===== Basic Slot Encoding/Decoding ===== *)

(* Encode an integer to bytes32 (right-aligned, two's complement) *)
Definition int_to_slot_def:
  int_to_slot (i : int) : bytes32 =
    n2w (Num (i % &(2 ** 256)))
End

(* Decode bytes32 to unsigned integer *)
Definition slot_to_uint_def:
  slot_to_uint (w : bytes32) : int = &(w2n w)
End

(* Decode bytes32 to signed integer (two's complement) *)
Definition slot_to_int_def:
  slot_to_int (bits : num) (w : bytes32) : int =
    let n = w2n w in
    let bound = 2 ** (bits - 1) in
    if n < bound then &n
    else &n - &(2 ** bits)
End

(* Bool encoding *)
Definition bool_to_slot_def:
  bool_to_slot (b : bool) : bytes32 = if b then 1w else 0w
End

Definition slot_to_bool_def:
  slot_to_bool (w : bytes32) : bool = (w <> 0w)
End

(* ===== Bytes/String Slot Helpers ===== *)

(* Split bytes into 32-byte chunks, padding last chunk *)
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

(* Extract bytes from slots, taking specified length *)
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
  base_type_slot_size (BytesT (Dynamic n)) = 1 + (n + 31) DIV 32 /\
  base_type_slot_size (StringT n) = 1 + (n + 31) DIV 32
End

Definition type_slot_size_def:
  type_slot_size (BaseTV bt) = base_type_slot_size bt /\
  type_slot_size (FlagTV _) = 1 /\
  type_slot_size NoneTV = 0 /\
  type_slot_size (TupleTV tvs) = SUM (MAP type_slot_size tvs) /\
  type_slot_size (ArrayTV tv (Fixed n)) = n * type_slot_size tv /\
  type_slot_size (ArrayTV tv (Dynamic n)) = 1 + n * type_slot_size tv /\
  type_slot_size (StructTV fields) = SUM (MAP (type_slot_size o SND) fields)
Termination
  WF_REL_TAC ‘measure type_value_size’ >> rw[type_value_size_def]
End

(* ===== Base Type Encoding (single slot) ===== *)

(* Encode base value to single slot - returns NONE on type mismatch *)
Definition encode_base_to_slot_def:
  encode_base_to_slot (IntV (Unsigned n) i) (BaseTV (UintT m)) =
    (if n = m then SOME (int_to_slot i) else NONE) /\
  encode_base_to_slot (IntV (Signed n) i) (BaseTV (IntT m)) =
    (if n = m then SOME (int_to_slot i) else NONE) /\
  encode_base_to_slot (DecimalV i) (BaseTV DecimalT) = 
    SOME (int_to_slot i) /\
  encode_base_to_slot (BoolV b) (BaseTV BoolT) = 
    SOME (bool_to_slot b) /\
  encode_base_to_slot (BytesV (Fixed 20) bs) (BaseTV AddressT) =
    (if LENGTH bs = 20 then SOME (word_of_bytes T 0w bs) else NONE) /\
  encode_base_to_slot (BytesV (Fixed m) bs) (BaseTV (BytesT (Fixed n))) =
    (if m = n /\ LENGTH bs = n /\ n <= 32 then
       SOME (word_of_bytes F 0w (bs ++ REPLICATE (32 - n) 0w))
     else NONE) /\
  encode_base_to_slot (FlagV m k) (FlagTV m') =
    (if m = m' then SOME (n2w k) else NONE) /\
  encode_base_to_slot NoneV NoneTV = SOME 0w /\
  encode_base_to_slot _ _ = NONE
End

(* Decode base value from single slot *)
Definition decode_base_from_slot_def:
  decode_base_from_slot (slot : bytes32) (BaseTV (UintT n)) =
    IntV (Unsigned n) (slot_to_uint slot) /\
  decode_base_from_slot slot (BaseTV (IntT n)) =
    IntV (Signed n) (slot_to_int n slot) /\
  decode_base_from_slot slot (BaseTV DecimalT) = 
    DecimalV (slot_to_int 168 slot) /\
  decode_base_from_slot slot (BaseTV BoolT) = 
    BoolV (slot_to_bool slot) /\
  decode_base_from_slot slot (BaseTV AddressT) =
    BytesV (Fixed 20) (DROP 12 (word_to_bytes slot T)) /\
  decode_base_from_slot slot (BaseTV (BytesT (Fixed n))) =
    BytesV (Fixed n) (TAKE n (word_to_bytes slot F)) /\
  decode_base_from_slot slot (FlagTV m) =
    FlagV m (w2n slot) /\
  decode_base_from_slot slot NoneTV = NoneV /\
  decode_base_from_slot slot _ = NoneV  (* should not happen *)
End

(* ===== Dynamic Bytes/String Encoding (multiple slots) ===== *)

Definition encode_dyn_bytes_def:
  encode_dyn_bytes max bs =
    if LENGTH bs <= max then
      SOME ((0, n2w (LENGTH bs)) :: MAPi (\i s. (i + 1, s)) (bytes_to_slots bs))
    else NONE
End

Definition decode_dyn_bytes_def:
  decode_dyn_bytes max (reader : num -> bytes32) =
    let len = w2n (reader 0) in
    if len <= max then
      let n_slots = (len + 31) DIV 32 in
      let slots = GENLIST (\i. reader (i + 1)) n_slots in
      SOME (slots_to_bytes len slots)
    else NONE
End

(* ===== Storage Read/Write Helpers ===== *)

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

(* Offset a reader by a given amount *)
Definition offset_reader_def:
  offset_reader (reader : num -> bytes32) off = \n. reader (off + n)
End
