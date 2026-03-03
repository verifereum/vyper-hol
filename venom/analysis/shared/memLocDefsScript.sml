(*
 * Memory Location Types for Alias Analysis
 *
 * Ported from vyper/venom/memory_location.py.
 *
 * TOP-LEVEL:
 *   allocation, mem_loc,
 *   ml_empty, ml_undefined,
 *   completely_contains, may_overlap, mk_volatile,
 *   inst_access_ops, mem_write_ops, mem_read_ops
 *
 * Divergences from Python:
 *   - allocation uses inst_id (num) instead of instruction object (no object identity in HOL)
 *)

Theory memLocDefs
Ancestors
  venomInst

(* ===== Allocation and Pointer Types ===== *)

(* An allocation is identified by the alloca/palloca instruction that created it *)
Datatype:
  allocation = Allocation num   (* inst_id *)
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

(* ===== Memory Access Dispatch Tables ===== *)

(* Matches Python InstAccessOps from memory_location.py.
 * ofst/size/max_size are all operand option, matching Python's Optional[IROperand].
 * Functions always return a record (Python always returns InstAccessOps). *)
Datatype:
  inst_access_ops = <|
    iao_ofst : operand option;
    iao_size : operand option;
    iao_max_size : operand option
  |>
End

Definition empty_access_ops_def:
  empty_access_ops = <| iao_ofst := NONE; iao_size := NONE; iao_max_size := NONE |>
End

(* Matches Python memory_write_ops in memory_location.py. *)
Definition mem_write_ops_def:
  mem_write_ops inst =
    case inst.inst_opcode of
      MSTORE =>
        (case inst.inst_operands of
           [_; dst] =>
             <| iao_ofst := SOME dst; iao_size := SOME (Lit 32w);
                iao_max_size := SOME (Lit 32w) |>
         | _ => empty_access_ops)
    | ISTORE =>
        (case inst.inst_operands of
           [dst; _] =>
             <| iao_ofst := SOME dst; iao_size := SOME (Lit 32w);
                iao_max_size := SOME (Lit 32w) |>
         | _ => empty_access_ops)
    | MCOPY =>
        (case inst.inst_operands of
           [sz; _; dst] =>
             <| iao_ofst := SOME dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | CALLDATACOPY =>
        (case inst.inst_operands of
           [sz; _; dst] =>
             <| iao_ofst := SOME dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | DLOADBYTES =>
        (case inst.inst_operands of
           [sz; _; dst] =>
             <| iao_ofst := SOME dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | CODECOPY =>
        (case inst.inst_operands of
           [sz; _; dst] =>
             <| iao_ofst := SOME dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | RETURNDATACOPY =>
        (case inst.inst_operands of
           [sz; _; dst] =>
             <| iao_ofst := SOME dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | EXTCODECOPY =>
        (case inst.inst_operands of
           [sz; _; dst; _] =>
             <| iao_ofst := SOME dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | CALL =>
        (case inst.inst_operands of
           [maxsz; dst; _; _; _; _; _] =>
             <| iao_ofst := SOME dst; iao_size := NONE; iao_max_size := SOME maxsz |>
         | _ => empty_access_ops)
    | DELEGATECALL =>
        (case inst.inst_operands of
           [maxsz; dst; _; _; _; _] =>
             <| iao_ofst := SOME dst; iao_size := NONE; iao_max_size := SOME maxsz |>
         | _ => empty_access_ops)
    | STATICCALL =>
        (case inst.inst_operands of
           [maxsz; dst; _; _; _; _] =>
             <| iao_ofst := SOME dst; iao_size := NONE; iao_max_size := SOME maxsz |>
         | _ => empty_access_ops)
    | _ => empty_access_ops
End

(* Matches Python memory_read_ops in memory_location.py. *)
Definition mem_read_ops_def:
  mem_read_ops inst =
    case inst.inst_opcode of
      MLOAD =>
        (case inst.inst_operands of
           [src] =>
             <| iao_ofst := SOME src; iao_size := SOME (Lit 32w);
                iao_max_size := SOME (Lit 32w) |>
         | _ => empty_access_ops)
    | ILOAD =>
        (case inst.inst_operands of
           [src] =>
             <| iao_ofst := SOME src; iao_size := SOME (Lit 32w);
                iao_max_size := SOME (Lit 32w) |>
         | _ => empty_access_ops)
    | MCOPY =>
        (case inst.inst_operands of
           [sz; src; _] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | CALL =>
        (case inst.inst_operands of
           [_; _; sz; src; _; _; _] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | DELEGATECALL =>
        (case inst.inst_operands of
           [_; _; sz; src; _; _] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | STATICCALL =>
        (case inst.inst_operands of
           [_; _; sz; src; _; _] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | RETURN =>
        (case inst.inst_operands of
           [sz; src] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | CREATE =>
        (case inst.inst_operands of
           [sz; src; _] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | CREATE2 =>
        (case inst.inst_operands of
           [_; sz; src; _] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | SHA3 =>
        (case inst.inst_operands of
           [sz; ofst] =>
             <| iao_ofst := SOME ofst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | LOG =>
        (case inst.inst_operands of
           _::_::_ =>
             let ops = inst.inst_operands in
             <| iao_ofst := SOME (LAST ops);
                iao_size := SOME (LAST (FRONT ops));
                iao_max_size := SOME (LAST (FRONT ops)) |>
         | _ => empty_access_ops)
    | REVERT =>
        (case inst.inst_operands of
           [sz; src] =>
             <| iao_ofst := SOME src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => empty_access_ops)
    | _ => empty_access_ops
End

