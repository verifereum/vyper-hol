(*
 * Value Encoding: Vyper values ↔ Venom bytes32 / memory regions
 *
 * TOP-LEVEL:
 *   val_to_w256       : value → bytes32 (primitive word encoding)
 *   typed_val_to_w256 : the same, with address/bytesN told apart by type
 *   type_memory_size  : memory footprint of a type_value
 *
 * The memory-layout predicates (val_in_memory, val_wf, ...) are in
 * lowering/proofs/valueEncodingDefs.
 *
 * Consistent with vyperStorage encode_base_to_slot / decode_base_from_slot.
 * word_of_bytes_be = word_of_bytes T 0w (HOL4 byteTheory).
 * Venom mload uses word_of_bytes T 0w — same encoding.
 *)

Theory valueEncoding
Ancestors
  vyperValue vyperStorage venomState bitstring byte integer_word list rich_list

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
