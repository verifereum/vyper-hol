(*
 * Memory Location Types for Alias Analysis
 *
 * Ported from vyper/venom/memory_location.py.
 *
 * TOP-LEVEL:
 *   allocation, ptr, mem_loc,
 *   ml_empty, ml_undefined,
 *   completely_contains, may_overlap, mk_volatile,
 *   offset_ptr,
 *   inst_write_ops, inst_read_ops
 *)

Theory memLocDefs
Ancestors
  venomInst

(* ===== Allocation and Pointer Types ===== *)

(* An allocation is identified by the alloca/palloca instruction that created it *)
Datatype:
  allocation = Allocation num   (* inst_id *)
End

(* A pointer: base allocation + optional known offset *)
Datatype:
  ptr = Ptr allocation (num option)
End

(* ===== Memory Location ===== *)

(* A memory location for alias analysis.
 * Tracks offset, size, base allocation, and volatility.
 * Note: ml_volatile is not checked in may_overlap (matching Python);
 * callers must check volatility separately at a higher level. *)
Datatype:
  mem_loc = <|
    ml_offset   : num option;         (* byte offset, NONE = unknown *)
    ml_size     : num option;         (* size in bytes, NONE = unknown *)
    ml_alloca   : allocation option;  (* base allocation, NONE = global memory *)
    ml_volatile : bool                (* volatile = conservatively may-alias everything *)
  |>
End

(* ===== Constants ===== *)

Definition ml_empty_def:
  ml_empty = <| ml_offset := SOME 0; ml_size := SOME 0;
                ml_alloca := NONE; ml_volatile := F |>
End

Definition ml_undefined_def:
  ml_undefined = <| ml_offset := NONE; ml_size := NONE;
                    ml_alloca := NONE; ml_volatile := F |>
End

(* ===== Containment ===== *)

(* outer completely contains inner *)
Definition completely_contains_def:
  completely_contains outer inner <=>
    (* empty is always contained *)
    (inner.ml_size = SOME 0) \/
    (* both must have fixed offset, size, and same alloca *)
    (IS_SOME outer.ml_offset /\ IS_SOME outer.ml_size /\
     IS_SOME inner.ml_offset /\ IS_SOME inner.ml_size /\
     outer.ml_alloca = inner.ml_alloca /\
     THE outer.ml_offset <= THE inner.ml_offset /\
     THE inner.ml_offset + THE inner.ml_size <=
       THE outer.ml_offset + THE outer.ml_size)
End

(* ===== May-Overlap (conservative alias check) ===== *)

Definition may_overlap_def:
  may_overlap loc1 loc2 <=>
    (* empty never overlaps *)
    loc1.ml_size <> SOME 0 /\ loc2.ml_size <> SOME 0 /\
    (* concrete vs abstract mismatch -> may overlap (conservative) *)
    (if IS_SOME loc1.ml_alloca <> IS_SOME loc2.ml_alloca then T
     (* different allocas -> no overlap *)
     else if IS_SOME loc1.ml_alloca /\ IS_SOME loc2.ml_alloca /\
             loc1.ml_alloca <> loc2.ml_alloca then F
     (* unknown offsets -> may overlap *)
     else if loc1.ml_offset = NONE \/ loc2.ml_offset = NONE then T
     (* both offsets known: check interval overlap *)
     else
       case (loc1.ml_size, loc2.ml_size) of
         (SOME s1, SOME s2) =>
           let o1 = THE loc1.ml_offset in
           let o2 = THE loc2.ml_offset in
           ~(o1 + s1 <= o2 \/ o2 + s2 <= o1)
       | (SOME s1, NONE) => ~(THE loc1.ml_offset + s1 <= THE loc2.ml_offset)
       | (NONE, SOME s2) => ~(THE loc2.ml_offset + s2 <= THE loc1.ml_offset)
       | (NONE, NONE) => T)
End

(* ===== Helpers ===== *)

Definition mk_volatile_def:
  mk_volatile loc = loc with ml_volatile := T
End

Definition offset_ptr_def:
  offset_ptr (Lit n) (Ptr alloc (SOME base_off)) =
    Ptr alloc (SOME (w2n n + base_off)) /\
  offset_ptr _ (Ptr alloc _) = Ptr alloc NONE
End

(* ===== Memory Access Dispatch Tables ===== *)

(* Extract (dst_operand, size_option) for memory-writing instructions.
 * Matches Python memory_write_ops in memory_location.py. *)
Definition inst_write_ops_def:
  inst_write_ops inst =
    case inst.inst_opcode of
      MSTORE =>
        (case inst.inst_operands of
           [_; dst] => SOME (dst, SOME 32)
         | _ => NONE)
    | ISTORE =>
        (case inst.inst_operands of
           [dst; _] => SOME (dst, SOME 32)
         | _ => NONE)
    | MCOPY =>
        (case inst.inst_operands of
           [sz; _; dst] => SOME (dst, NONE)
         | _ => NONE)
    | CALLDATACOPY =>
        (case inst.inst_operands of
           [sz; _; dst] => SOME (dst, NONE)
         | _ => NONE)
    | DLOADBYTES =>
        (case inst.inst_operands of
           [sz; _; dst] => SOME (dst, NONE)
         | _ => NONE)
    | CODECOPY =>
        (case inst.inst_operands of
           [sz; _; dst] => SOME (dst, NONE)
         | _ => NONE)
    | RETURNDATACOPY =>
        (case inst.inst_operands of
           [sz; _; dst] => SOME (dst, NONE)
         | _ => NONE)
    | EXTCODECOPY =>
        (case inst.inst_operands of
           [sz; _; dst; _] => SOME (dst, NONE)
         | _ => NONE)
    | CALL =>
        (case inst.inst_operands of
           [maxsz; dst; _; _; _; _; _] => SOME (dst, NONE)
         | _ => NONE)
    | DELEGATECALL =>
        (case inst.inst_operands of
           [maxsz; dst; _; _; _; _] => SOME (dst, NONE)
         | _ => NONE)
    | STATICCALL =>
        (case inst.inst_operands of
           [maxsz; dst; _; _; _; _] => SOME (dst, NONE)
         | _ => NONE)
    | _ => NONE
End

(* Extract (src_operand, size_option) for memory-reading instructions.
 * Matches Python memory_read_ops in memory_location.py. *)
Definition inst_read_ops_def:
  inst_read_ops inst =
    case inst.inst_opcode of
      MLOAD =>
        (case inst.inst_operands of
           [src] => SOME (src, SOME 32)
         | _ => NONE)
    | ILOAD =>
        (case inst.inst_operands of
           [src] => SOME (src, SOME 32)
         | _ => NONE)
    | MCOPY =>
        (case inst.inst_operands of
           [sz; src; _] => SOME (src, NONE)
         | _ => NONE)
    | CALL =>
        (case inst.inst_operands of
           [_; _; sz; src; _; _; _] => SOME (src, NONE)
         | _ => NONE)
    | DELEGATECALL =>
        (case inst.inst_operands of
           [_; _; sz; src; _; _] => SOME (src, NONE)
         | _ => NONE)
    | STATICCALL =>
        (case inst.inst_operands of
           [_; _; sz; src; _; _] => SOME (src, NONE)
         | _ => NONE)
    | RETURN =>
        (case inst.inst_operands of
           [sz; src] => SOME (src, NONE)
         | _ => NONE)
    | CREATE =>
        (case inst.inst_operands of
           [sz; src; _] => SOME (src, NONE)
         | _ => NONE)
    | CREATE2 =>
        (case inst.inst_operands of
           [_; sz; src; _] => SOME (src, NONE)
         | _ => NONE)
    | SHA3 =>
        (case inst.inst_operands of
           [sz; ofst] => SOME (ofst, NONE)
         | _ => NONE)
    | LOG =>
        (case inst.inst_operands of
           [] => NONE
         | ops => SOME (LAST ops, NONE))
    | REVERT =>
        (case inst.inst_operands of
           [sz; src] => SOME (src, NONE)
         | _ => NONE)
    | _ => NONE
End

