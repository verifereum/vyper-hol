(*
 * Memory Location Types for Alias Analysis
 *
 * Upstream: vyperlang/vyper@8780b3134 (remove alloca_id)
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

(* An allocation is identified by the alloca instruction that created it *)
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
 * size is NONE when actual bytes accessed is indeterminate (e.g. CALL writes).
 * max_size defaults to size (matching Python __post_init__).
 *
 * Divergence: Python always returns InstAccessOps (crashes on malformed operands).
 * HOL returns NONE for non-memory opcodes and malformed operand counts. *)
Datatype:
  inst_access_ops = <|
    iao_ofst : operand;
    iao_size : operand option;
    iao_max_size : operand option
  |>
End

(* Matches Python memory_write_ops in memory_location.py.
 * SOME record: valid memory-writing instruction with well-formed operands.
 *   Within the record, iao_size = NONE means indeterminate byte count.
 * NONE (outer): opcode doesn't write memory, or operand count is wrong
 *   (the latter would be a compiler bug in Python). *)
(* Operand order: EVM semantic order (matching step_inst_base).
 * MSTORE [addr; val], MCOPY [dst; src; sz], CALL [gas; addr; val; ao; as; ro; rs]
 * Note: Python uses reversed (stack push) order — this was ported and corrected. *)
Definition mem_write_ops_def:
  mem_write_ops inst =
    case inst.inst_opcode of
      MSTORE =>
        (case inst.inst_operands of
           [dst; _] =>
             SOME <| iao_ofst := dst; iao_size := SOME (Lit 32w);
                     iao_max_size := SOME (Lit 32w) |>
         | _ => NONE)
    | MSTORE8 =>
        (case inst.inst_operands of
           [dst; _] =>
             SOME <| iao_ofst := dst; iao_size := SOME (Lit 1w);
                     iao_max_size := SOME (Lit 1w) |>
         | _ => NONE)
    | ISTORE =>
        (case inst.inst_operands of
           [dst; _] =>
             SOME <| iao_ofst := dst; iao_size := SOME (Lit 32w);
                     iao_max_size := SOME (Lit 32w) |>
         | _ => NONE)
    | MCOPY =>
        (case inst.inst_operands of
           [dst; _; sz] =>
             SOME <| iao_ofst := dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | CALLDATACOPY =>
        (case inst.inst_operands of
           [dst; _; sz] =>
             SOME <| iao_ofst := dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | DLOADBYTES =>
        (case inst.inst_operands of
           [dst; _; sz] =>
             SOME <| iao_ofst := dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | CODECOPY =>
        (case inst.inst_operands of
           [dst; _; sz] =>
             SOME <| iao_ofst := dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | RETURNDATACOPY =>
        (case inst.inst_operands of
           [dst; _; sz] =>
             SOME <| iao_ofst := dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | EXTCODECOPY =>
        (* EVM: EXTCODECOPY addr dst src size *)
        (case inst.inst_operands of
           [_; dst; _; sz] =>
             SOME <| iao_ofst := dst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | CALL =>
        (* EVM: CALL gas addr val argsOff argsLen retOff retLen *)
        (case inst.inst_operands of
           [_; _; _; _; _; dst; maxsz] =>
             SOME <| iao_ofst := dst; iao_size := NONE; iao_max_size := SOME maxsz |>
         | _ => NONE)
    | DELEGATECALL =>
        (* EVM: DELEGATECALL gas addr argsOff argsLen retOff retLen *)
        (case inst.inst_operands of
           [_; _; _; _; dst; maxsz] =>
             SOME <| iao_ofst := dst; iao_size := NONE; iao_max_size := SOME maxsz |>
         | _ => NONE)
    | STATICCALL =>
        (* EVM: STATICCALL gas addr argsOff argsLen retOff retLen *)
        (case inst.inst_operands of
           [_; _; _; _; dst; maxsz] =>
             SOME <| iao_ofst := dst; iao_size := NONE; iao_max_size := SOME maxsz |>
         | _ => NONE)
    | _ => NONE
End

(* Matches Python memory_read_ops in memory_location.py.
 * SOME record: valid memory-reading instruction with well-formed operands.
 * NONE (outer): opcode doesn't read memory, or operand count is wrong. *)
(* Operand order: EVM semantic order (matching step_inst_base).
 * MLOAD [addr], MCOPY [dst; src; sz], RETURN [off; sz], etc. *)
Definition mem_read_ops_def:
  mem_read_ops inst =
    case inst.inst_opcode of
      MLOAD =>
        (case inst.inst_operands of
           [src] =>
             SOME <| iao_ofst := src; iao_size := SOME (Lit 32w);
                     iao_max_size := SOME (Lit 32w) |>
         | _ => NONE)
    | ILOAD =>
        (case inst.inst_operands of
           [src] =>
             SOME <| iao_ofst := src; iao_size := SOME (Lit 32w);
                     iao_max_size := SOME (Lit 32w) |>
         | _ => NONE)
    | MCOPY =>
        (* EVM: MCOPY dst src sz — reads from src *)
        (case inst.inst_operands of
           [_; src; sz] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | CALL =>
        (* EVM: CALL gas addr val argsOff argsLen retOff retLen — reads from argsOff *)
        (case inst.inst_operands of
           [_; _; _; src; sz; _; _] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | DELEGATECALL =>
        (* EVM: DELEGATECALL gas addr argsOff argsLen retOff retLen *)
        (case inst.inst_operands of
           [_; _; src; sz; _; _] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | STATICCALL =>
        (* EVM: STATICCALL gas addr argsOff argsLen retOff retLen *)
        (case inst.inst_operands of
           [_; _; src; sz; _; _] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | RETURN =>
        (* EVM: RETURN offset size *)
        (case inst.inst_operands of
           [src; sz] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | CREATE =>
        (* EVM: CREATE value offset size — reads from offset *)
        (case inst.inst_operands of
           [_; src; sz] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | CREATE2 =>
        (* EVM: CREATE2 value offset size salt *)
        (case inst.inst_operands of
           [_; src; sz; _] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | SHA3 =>
        (* EVM: SHA3 offset size *)
        (case inst.inst_operands of
           [ofst; sz] =>
             SOME <| iao_ofst := ofst; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | LOG =>
        (* EVM: LOG tc offset size topics...
           In HOL4: Lit tc :: offset :: size :: topics *)
        (case inst.inst_operands of
           _::ofst::sz::_ =>
             SOME <| iao_ofst := ofst; iao_size := SOME sz;
                     iao_max_size := SOME sz |>
         | _ => NONE)
    | REVERT =>
        (* EVM: REVERT offset size *)
        (case inst.inst_operands of
           [src; sz] =>
             SOME <| iao_ofst := src; iao_size := SOME sz; iao_max_size := SOME sz |>
         | _ => NONE)
    | _ => NONE
End

