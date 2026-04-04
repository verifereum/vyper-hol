(*
 * Value Encoding: Vyper values ↔ Venom bytes32 / memory regions
 *
 * TOP-LEVEL:
 *   val_to_w256     : value → bytes32 (primitive word encoding)
 *   w256_to_val     : bytes32 → type_value → value (decode)
 *   val_in_memory   : value → num → byte list → bool (compound types in memory)
 *   val_wf          : type_value → value → bool (value fits type's memory footprint)
 *
 * Helper:
 *   bool_to_w256, int_to_w256 — sub-cases of val_to_w256
 *
 * Consistent with vyperStorage encode_base_to_slot / decode_base_from_slot.
 * word_of_bytes_be = word_of_bytes T 0w (HOL4 byteTheory).
 * Venom mload uses word_of_bytes T 0w — same encoding.
 *)

Theory valueEncoding
Ancestors
  vyperValue vyperStorage venomState

(* ===== Primitive Value → bytes32 ===== *)

(* Encode a primitive Vyper value to a 256-bit word.
   Matches what the Python codegen puts into Venom IR registers
   (i.e., what VenomCodegenContext.unwrap returns for primitive types).

   For compound types (arrays, structs, bytes/strings), returns 0w —
   those live in memory, not registers. *)

Definition val_to_w256_def:
  val_to_w256 (BoolV b) = (if b then 1w else 0w : bytes32) ∧
  val_to_w256 (IntV n) = (i2w n : bytes32) ∧
  val_to_w256 (FlagV k) = (n2w k : bytes32) ∧
  val_to_w256 (DecimalV n) = (i2w n : bytes32) ∧
  (* Bytes: left-aligned (PAD_RIGHT) per ABI. Length=20 is treated as address
     (right-aligned) by heuristic — use typed_val_to_w256 when type is known. *)
  val_to_w256 (BytesV bs) =
    (if LENGTH bs = 20 then word_of_bytes_be (PAD_LEFT 0w 32 bs)
     else word_of_bytes_be (PAD_RIGHT 0w 32 bs)) ∧
  (* Dynamic bytes/strings and compound types have no word encoding *)
  val_to_w256 _ = 0w
End

(* Type-dispatched encoding: uses type to distinguish address (right-aligned)
   from bytesN (left-aligned). Use this in proofs when type info is available. *)
Definition typed_val_to_w256_def:
  typed_val_to_w256 (BaseTV AddressT) (BytesV bs) =
    word_of_bytes_be (PAD_LEFT 0w 32 bs) ∧
  typed_val_to_w256 (BaseTV (BytesT _)) (BytesV bs) =
    word_of_bytes_be (PAD_RIGHT 0w 32 bs) ∧
  typed_val_to_w256 _ v = val_to_w256 v
End

(* Decode bytes32 to a Vyper value given a type.
   Inverse of val_to_w256 for primitive types.
   Reuses vyperStorage's decode_base_from_slot. *)

Definition w256_to_val_def:
  w256_to_val (w : bytes32) (tv : type_value) = decode_base_from_slot w tv
End

(* ===== Agreement with vyperStorage ===== *)

(* val_to_w256 agrees with encode_base_to_slot for well-typed primitives.
   This is stated as a Props theorem, proved in proofs/. *)

(* ===== Memory Layout for Compound Types ===== *)

(* Check that a Vyper value is correctly laid out in memory starting
   at the given offset. Uses Venom's mload (= word_of_bytes T 0w).

   Memory layout matches Python codegen (VenomCodegenContext):
   - Primitives: 32 bytes big-endian at offset
   - DynArray: [length:32][elem0:sz][elem1:sz]...
   - SArray:   [elem0:sz][elem1:sz]...
   - Struct:   [field0:sz0][field1:sz1]...
   - Bytes/String (dynamic): [length:32][data:ceil32(len)]
   - Tuple: [elem0:sz0][elem1:sz1]...
*)

(* Read 32-byte word from memory at offset (with zero-padding if short).
   Same as venomState mload but takes memory directly. *)
Definition mem_word_at_def:
  mem_word_at offset (mem : byte list) : bytes32 =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP offset mem ++ REPLICATE 32 0w))
End

(* Read raw bytes from memory *)
Definition mem_bytes_at_def:
  mem_bytes_at offset len (mem : byte list) : byte list =
    TAKE len (DROP offset mem ++ REPLICATE len 0w)
End

(* Memory size of a type_value (in bytes), matching Python typ.memory_bytes_required *)
Definition type_memory_size_def:
  type_memory_size (BaseTV (BytesT (Dynamic n))) = 32 + 32 * word_size n ∧
  type_memory_size (BaseTV (StringT n)) = 32 + 32 * word_size n ∧
  type_memory_size (BaseTV _) = 32 ∧
  type_memory_size (FlagTV _) = 32 ∧
  type_memory_size NoneTV = 0 ∧
  type_memory_size (TupleTV tvs) = type_memory_size_list tvs ∧
  type_memory_size (ArrayTV tv (Fixed n)) = n * type_memory_size tv ∧
  type_memory_size (ArrayTV tv (Dynamic n)) = 32 + n * type_memory_size tv ∧
  type_memory_size (StructTV fields) = type_memory_size_fields fields ∧
  type_memory_size_list [] = 0 ∧
  type_memory_size_list (tv::tvs) = type_memory_size tv + type_memory_size_list tvs ∧
  type_memory_size_fields [] = 0 ∧
  type_memory_size_fields ((_,tv)::rest) =
    type_memory_size tv + type_memory_size_fields rest
End

(* Compute memory size of a value (runtime).
   For well-typed values, val_memory_size v = type_memory_size (typeof v). *)
Definition val_memory_size_def:
  val_memory_size (BoolV _) = 32 ∧
  val_memory_size (IntV _) = 32 ∧
  val_memory_size (FlagV _) = 32 ∧
  val_memory_size (DecimalV _) = 32 ∧
  (* TODO: BytesV lost Fixed/Dynamic bound; using LENGTH bs as approximation.
     Was: BytesV (Fixed _) _ = 32; BytesV (Dynamic maxlen) _ = 32 + 32 * word_size maxlen.
     This function may need a type parameter to recover maxlen. *)
  val_memory_size (BytesV bs) = 32 + 32 * word_size (LENGTH bs) ∧
  (* TODO: StringV lost maxlen; using LENGTH s as approximation.
     Was: StringV maxlen _ = 32 + 32 * word_size maxlen *)
  val_memory_size (StringV s) = 32 + 32 * word_size (LENGTH s) ∧
  val_memory_size NoneV = 0 ∧
  val_memory_size (StructV fields) = fields_memory_size fields ∧
  (* Array memory sizes: DynArrayV/SArrayV lost type_value and bound.
     Use sum of element sizes as conservative estimate. *)
  val_memory_size (ArrayV (DynArrayV vs)) = 32 + elems_memory_size vs ∧
  val_memory_size (ArrayV (SArrayV kvs)) = kvs_memory_size kvs ∧
  val_memory_size (ArrayV (TupleV vs)) = tuple_memory_size vs ∧
  fields_memory_size [] = 0 ∧
  fields_memory_size ((_,v)::rest) = val_memory_size v + fields_memory_size rest ∧
  tuple_memory_size [] = 0 ∧
  tuple_memory_size (v::vs) = val_memory_size v + tuple_memory_size vs ∧
  elems_memory_size [] = 0 ∧
  elems_memory_size (v::vs) = val_memory_size v + elems_memory_size vs ∧
  kvs_memory_size [] = 0 ∧
  kvs_memory_size ((_:num,v)::rest) = val_memory_size v + kvs_memory_size rest
End

(* Core predicate: value v of type ty is encoded at memory offset in mem.
   ty parameter resolves BytesV layout: fixed bytes (bytes1-32) use word
   encoding; dynamic bytes (Bytes[N]) use length-prefixed layout.
   For non-BytesV values, ty is only used in recursive calls. *)
Definition val_in_memory_def:
  (* Primitive word types: 32 bytes big-endian *)
  (val_in_memory ty (BoolV b) offset mem =
    (mem_word_at offset mem = val_to_w256 (BoolV b))) ∧

  (val_in_memory ty (IntV n) offset mem =
    (mem_word_at offset mem = val_to_w256 (IntV n))) ∧

  (val_in_memory ty (FlagV k) offset mem =
    (mem_word_at offset mem = val_to_w256 (FlagV k))) ∧

  (val_in_memory ty (DecimalV n) offset mem =
    (mem_word_at offset mem = val_to_w256 (DecimalV n))) ∧

  (* BytesV: dispatch on type.
     Fixed bytes (bytes1-bytes32): 32-byte word encoding (left-aligned).
     AddressT: 20-byte address stored as right-aligned word.
     Dynamic bytes (Bytes[N]): length-prefixed [len:32][data...]. *)
  (val_in_memory ty (BytesV bs) offset mem =
    case ty of
      BaseTV (BytesT (Fixed _)) =>
        (mem_word_at offset mem = typed_val_to_w256 ty (BytesV bs))
    | BaseTV AddressT =>
        (mem_word_at offset mem = typed_val_to_w256 ty (BytesV bs))
    | _ =>
        (mem_word_at offset mem = n2w (LENGTH bs) ∧
         mem_bytes_at (offset + 32) (LENGTH bs) mem = bs)) ∧

  (* String: same layout as dynamic bytes *)
  (val_in_memory ty (StringV s) offset mem =
    (let bs = MAP (n2w o ORD) s in
     mem_word_at offset mem = n2w (LENGTH bs) ∧
     mem_bytes_at (offset + 32) (LENGTH bs) mem = bs)) ∧

  (val_in_memory ty NoneV offset mem = T) ∧

  (* Struct: fields concatenated. Thread field types from StructTV. *)
  (val_in_memory ty (StructV fields) offset mem =
    (case ty of
       StructTV field_tvs =>
         fields_in_memory fields field_tvs offset mem
     | _ => F)) ∧

  (* DynArray: [length:32][elements...].
     Element type extracted from ty (must be ArrayTV). *)
  (val_in_memory ty (ArrayV (DynArrayV vs)) offset mem =
    (mem_word_at offset mem = n2w (LENGTH vs) ∧
     case ty of
       ArrayTV elem_tv _ =>
         elems_in_memory vs (offset + 32) elem_tv mem
     | _ => F)) ∧

  (* SArray: elements in index order, no length word. *)
  (val_in_memory ty (ArrayV (SArrayV kvs)) offset mem =
    (case ty of
       ArrayTV elem_tv _ =>
         kvs_in_memory kvs offset elem_tv mem
     | _ => F)) ∧

  (* Tuple: elements concatenated. Thread element types from TupleTV. *)
  (val_in_memory ty (ArrayV (TupleV vs)) offset mem =
    (case ty of
       TupleTV tvs => tuple_in_memory vs tvs offset mem
     | _ => F)) ∧

  (* Fields: concatenated at consecutive offsets with per-field types.
     Zips value fields with type info from StructTV. If type list is
     shorter (mismatch), remaining fields are unchecked. *)
  (fields_in_memory [] _ offset mem = T) ∧
  (fields_in_memory ((name, v)::rest) field_tvs offset mem =
    (let (ftv, rest_tvs) =
       case field_tvs of
         (_, tv)::tvs => (tv, tvs)
       | [] => (BaseTV BoolT, [])  (* fallback: should not happen *)
     in
     val_in_memory ftv v offset mem ∧
     fields_in_memory rest rest_tvs (offset + type_memory_size ftv) mem)) ∧

  (* Element list in memory (homogeneous type) *)
  (elems_in_memory [] offset tv mem = T) ∧
  (elems_in_memory (v::vs) offset tv mem =
    (val_in_memory tv v offset mem ∧
     elems_in_memory vs (offset + type_memory_size tv) tv mem)) ∧

  (* Key-value element list (SArray): use key for offset computation.
     Element at index k lives at base + k * elem_size.
     Mirrors Python: codegen/core.py _get_element_ptr_array. *)
  (kvs_in_memory ([] : (num # value) list) base_offset tv mem = T) ∧
  (kvs_in_memory ((k:num, v)::rest) base_offset tv mem =
    (val_in_memory tv v (base_offset + k * type_memory_size tv) mem ∧
     kvs_in_memory rest base_offset tv mem)) ∧

  (* Tuple elements in memory (heterogeneous, typed by TupleTV list) *)
  (tuple_in_memory [] _ offset mem = T) ∧
  (tuple_in_memory (v::vs) tvs offset mem =
    (let (etv, rest_tvs) =
       case tvs of
         tv::tvs' => (tv, tvs')
       | [] => (BaseTV BoolT, [])  (* fallback: should not happen *)
     in
     val_in_memory etv v offset mem ∧
     tuple_in_memory vs rest_tvs (offset + type_memory_size etv) mem))
Termination
  WF_REL_TAC `measure $ λx.
    case x of
    (* val_in_memory *)
      INL (_, v, _, _) => value_size v
    (* fields_in_memory *)
    | INR (INL (fields, _, _, _)) =>
        list_size (pair_size (list_size char_size) value_size) fields
    (* elems_in_memory *)
    | INR (INR (INL (vs, _, _, _))) => list_size value_size vs
    (* kvs_in_memory *)
    | INR (INR (INR (INL (kvs, _, _, _)))) =>
        list_size (pair_size (K 0) value_size) kvs
    (* tuple_in_memory *)
    | INR (INR (INR (INR (vs, _, _, _)))) => list_size value_size vs`
  >> simp[basicSizeTheory.pair_size_def, listTheory.list_size_def,
          value_size_def]
  >> Induct >> simp[listTheory.list_size_def, basicSizeTheory.pair_size_def]
  >> Cases >> simp[basicSizeTheory.pair_size_def]
End

(* ===== Value Well-Formedness for Memory Layout ===== *)

(* val_wf ty v: value v fits within type_memory_size ty bytes.
   Needed as precondition for disjointness preservation (mstore_preserves_val_in_memory).
   The issue: for dynamic BytesT/StringT, val_in_memory permits data of any LENGTH,
   but type_memory_size computes from the declared capacity.
   Similarly, DynArray length and SArray indices must fit the declared bound.
   For well-typed programs this always holds; val_wf makes it explicit. *)
Definition val_wf_def:
  val_wf ty (BoolV _) = (32 ≤ type_memory_size ty) ∧
  val_wf ty (IntV _) = (32 ≤ type_memory_size ty) ∧
  val_wf ty (FlagV _) = (32 ≤ type_memory_size ty) ∧
  val_wf ty (DecimalV _) = (32 ≤ type_memory_size ty) ∧
  (* BytesV: fixed/address → 32-byte word, always fits.
     Dynamic bytes → actual data must fit type capacity. *)
  val_wf ty (BytesV bs) =
    (case ty of
       BaseTV (BytesT (Fixed _)) => T
     | BaseTV AddressT => T
     | _ => LENGTH bs + 32 ≤ type_memory_size ty) ∧
  (* StringV: length-prefixed layout, data must fit *)
  val_wf ty (StringV s) = (LENGTH s + 32 ≤ type_memory_size ty) ∧
  val_wf ty NoneV = T ∧
  (* Compound types: recursive well-formedness on sub-values *)
  val_wf ty (StructV fields) =
    (case ty of
       StructTV field_tvs => fields_val_wf fields field_tvs
     | _ => F) ∧
  val_wf ty (ArrayV (DynArrayV vs)) =
    (case ty of
       ArrayTV elem_tv (Dynamic n) =>
         LENGTH vs ≤ n ∧ elems_val_wf vs elem_tv
     | _ => F) ∧
  val_wf ty (ArrayV (SArrayV kvs)) =
    (case ty of
       ArrayTV elem_tv (Fixed bound) =>
         kvs_val_wf kvs elem_tv bound
     | _ => F) ∧
  val_wf ty (ArrayV (TupleV vs)) =
    (case ty of
       TupleTV tvs => tuple_val_wf vs tvs
     | _ => F) ∧
  (* fields: each field well-formed with its type — F if types run out *)
  fields_val_wf [] _ = T ∧
  fields_val_wf ((_, v) :: rest) field_tvs =
    (case field_tvs of
       (_, tv) :: tvs => val_wf tv v ∧ fields_val_wf rest tvs
     | [] => F) ∧
  (* elements: homogeneous type *)
  elems_val_wf [] _ = T ∧
  elems_val_wf (v :: vs) tv = (val_wf tv v ∧ elems_val_wf vs tv) ∧
  (* kv elements: index < bound, value well-formed *)
  kvs_val_wf ([] : (num # value) list) _ _ = T ∧
  kvs_val_wf ((k:num, v) :: rest) tv bound =
    (k < bound ∧ val_wf tv v ∧ kvs_val_wf rest tv bound) ∧
  (* tuple: heterogeneous types — F if types run out *)
  tuple_val_wf [] _ = T ∧
  tuple_val_wf (v :: vs) tvs =
    (case tvs of
       tv :: tvs' => val_wf tv v ∧ tuple_val_wf vs tvs'
     | [] => F)
Termination
  WF_REL_TAC `measure $ λx.
    case x of
    (* val_wf *)
      INL (_, v) => value_size v
    (* fields_val_wf *)
    | INR (INL (fields, _)) =>
        list_size (pair_size (list_size char_size) value_size) fields
    (* elems_val_wf *)
    | INR (INR (INL (vs, _))) => list_size value_size vs
    (* kvs_val_wf *)
    | INR (INR (INR (INL (kvs, _, _)))) =>
        list_size (pair_size (K 0) value_size) kvs
    (* tuple_val_wf *)
    | INR (INR (INR (INR (vs, _)))) => list_size value_size vs`
  >> simp[basicSizeTheory.pair_size_def, listTheory.list_size_def,
          value_size_def]
  >> Induct >> simp[listTheory.list_size_def, basicSizeTheory.pair_size_def]
  >> Cases >> simp[basicSizeTheory.pair_size_def]
End
