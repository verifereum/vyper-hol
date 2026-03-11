(*
 * Fix Memory Locations Pass — Definitions
 *
 * Ports vyper/venom/passes/fix_mem_locations.py to HOL4.
 *
 * Replaces hardcoded memory accesses to FREE_VAR_SPACE (offset 0)
 * and FREE_VAR_SPACE2 (offset 32) with pinned allocas + GEP offsets.
 * Creates two pinned allocas at function entry, then rewrites any
 * mstore/mload/etc targeting those fixed addresses to use alloca pointers.
 *
 * No analysis needed — literal pattern match on address operands.
 * Framework: per-instruction expansion (1:N) with entry-block prologue.
 *
 * TOP-LEVEL:
 *   free_var_space, free_var_space2    — memory position constants
 *   in_free_var                        — range check
 *   get_mem_write_offset               — extract write offset operand
 *   get_mem_read_offset                — extract read offset operand
 *   fix_mem_inst                       — per-instruction transform
 *   fix_mem_function                   — function-level transform
 *   fix_mem_context                    — context-level transform
 *
 * Helper:
 *   replace_nth           — replace operand at index
 *   fml_alloca_var        — fresh variable names
 *
 * Source: vyper/venom/passes/fix_mem_locations.py
 *)

Theory fixMemLocationsDefs
Ancestors
  passSimulationDefs venomExecSemantics venomInst

(* ===== Constants ===== *)

(* Python: MemoryPositions.FREE_VAR_SPACE = 0 *)
Definition free_var_space_def:
  free_var_space = 0n
End

(* Python: MemoryPositions.FREE_VAR_SPACE2 = 32 *)
Definition free_var_space2_def:
  free_var_space2 = 32n
End

(* Check if offset falls within [free_var, free_var + 32). *)
Definition in_free_var_def:
  in_free_var (fv : num) (offset : num) <=>
    fv <= offset /\ offset < fv + 32
End

(* ===== Operand Utilities ===== *)

(* Replace the n-th element of a list. *)
Definition replace_nth_def:
  replace_nth 0 v (x::rest) = v :: rest /\
  replace_nth (SUC n) v (x::rest) = x :: replace_nth n v rest /\
  replace_nth _ _ [] = []
End

(* ===== Memory Operand Access (HOL4 semantic order) ===== *)

(*
 * Index of the memory write destination operand for each opcode.
 * Uses HOL4 semantic operand order (matches step_inst_base).
 *
 * Note: mem_write_ops in memLocDefs uses Python stack order.
 * These helpers use HOL4 semantic order for consistency with step_inst_base.
 *)
Definition mem_write_offset_idx_def:
  mem_write_offset_idx MSTORE = SOME 0n /\    (* [offset; value] *)
  mem_write_offset_idx ISTORE = SOME 0n /\    (* [offset; value] *)
  mem_write_offset_idx MCOPY = SOME 0n /\     (* [dst; src; size] *)
  mem_write_offset_idx CALLDATACOPY = SOME 0n /\
  mem_write_offset_idx DLOADBYTES = SOME 0n /\
  mem_write_offset_idx CODECOPY = SOME 0n /\
  mem_write_offset_idx RETURNDATACOPY = SOME 0n /\
  mem_write_offset_idx EXTCODECOPY = SOME 1n /\ (* [addr; dst; src; size] *)
  mem_write_offset_idx CALL = SOME 5n /\        (* [gas; addr; val; ao; as; ro; rs] *)
  mem_write_offset_idx DELEGATECALL = SOME 4n /\ (* [gas; addr; ao; as; ro; rs] *)
  mem_write_offset_idx STATICCALL = SOME 4n /\   (* [gas; addr; ao; as; ro; rs] *)
  mem_write_offset_idx _ = NONE
End

(*
 * Index of the memory read source operand for each opcode.
 *)
Definition mem_read_offset_idx_def:
  mem_read_offset_idx MLOAD = SOME 0n /\      (* [addr] *)
  mem_read_offset_idx ILOAD = SOME 0n /\      (* [addr] *)
  mem_read_offset_idx MCOPY = SOME 1n /\      (* [dst; src; size] *)
  mem_read_offset_idx CALL = SOME 3n /\       (* [gas; addr; val; ao; as; ro; rs] *)
  mem_read_offset_idx DELEGATECALL = SOME 2n /\ (* [gas; addr; ao; as; ro; rs] *)
  mem_read_offset_idx STATICCALL = SOME 2n /\   (* [gas; addr; ao; as; ro; rs] *)
  mem_read_offset_idx RETURN = SOME 0n /\     (* [off; sz] *)
  mem_read_offset_idx CREATE = SOME 1n /\     (* [val; off; sz] *)
  mem_read_offset_idx CREATE2 = SOME 1n /\    (* [val; off; sz; salt] *)
  mem_read_offset_idx SHA3 = SOME 0n /\       (* [off; sz] *)
  mem_read_offset_idx REVERT = SOME 0n /\     (* [off; sz] *)
  mem_read_offset_idx LOG = SOME 1n /\        (* [tc; off; sz; topics...] *)
  mem_read_offset_idx _ = NONE
End

(* Extract the memory offset operand from an instruction. *)
Definition get_mem_write_offset_def:
  get_mem_write_offset inst =
    case mem_write_offset_idx inst.inst_opcode of
      NONE => NONE
    | SOME idx =>
        if idx < LENGTH inst.inst_operands
        then SOME (EL idx inst.inst_operands)
        else NONE
End

Definition get_mem_read_offset_def:
  get_mem_read_offset inst =
    case mem_read_offset_idx inst.inst_opcode of
      NONE => NONE
    | SOME idx =>
        if idx < LENGTH inst.inst_operands
        then SOME (EL idx inst.inst_operands)
        else NONE
End

(* Replace the memory offset operand in an instruction. *)
Definition set_mem_write_offset_def:
  set_mem_write_offset inst new_op =
    case mem_write_offset_idx inst.inst_opcode of
      NONE => inst
    | SOME idx =>
        inst with inst_operands :=
          replace_nth idx new_op inst.inst_operands
End

Definition set_mem_read_offset_def:
  set_mem_read_offset inst new_op =
    case mem_read_offset_idx inst.inst_opcode of
      NONE => inst
    | SOME idx =>
        inst with inst_operands :=
          replace_nth idx new_op inst.inst_operands
End

(* ===== Write size check ===== *)

(* Check if an instruction has a known write size.
   Python: get_write_max_size(inst) — returns NONE for non-writing insts. *)
Definition has_write_size_def:
  has_write_size inst <=> mem_write_offset_idx inst.inst_opcode <> NONE
End

(* Check if an instruction has a known read size. *)
Definition has_read_size_def:
  has_read_size inst <=> mem_read_offset_idx inst.inst_opcode <> NONE
End

(* ===== Fresh Variable Names ===== *)

Definition fml_alloca1_var_def:
  fml_alloca1_var = "fml_free_ptr1"
End

Definition fml_alloca2_var_def:
  fml_alloca2_var = "fml_free_ptr2"
End

Definition fml_gep_var_def:
  fml_gep_var (id:num) = STRCAT "fml_gep_" (toString id)
End

(* ===== Per-Instruction Transform ===== *)

(*
 * Try to fix a memory offset operand by replacing a literal address
 * in the FREE_VAR_SPACE range with a GEP from the corresponding alloca.
 *
 * Returns SOME (gep_inst, new_op) if replacement needed, NONE otherwise.
 *)
Definition fix_offset_op_def:
  fix_offset_op inst_id alloca1 alloca2 op =
    case op of
      Lit w =>
        let offset = w2n w in
        if in_free_var free_var_space offset then
          let gep_v = fml_gep_var inst_id in
          let diff = offset - free_var_space in
          SOME (<| inst_id := inst_id; inst_opcode := GEP;
                   inst_operands := [Var alloca1; Lit (n2w diff)];
                   inst_outputs := [gep_v] |>,
                Var gep_v)
        else if in_free_var free_var_space2 offset then
          let gep_v = fml_gep_var inst_id in
          let diff = offset - free_var_space2 in
          SOME (<| inst_id := inst_id; inst_opcode := GEP;
                   inst_operands := [Var alloca2; Lit (n2w diff)];
                   inst_outputs := [gep_v] |>,
                Var gep_v)
        else NONE
    | _ => NONE
End

(*
 * Process a single instruction.
 * Returns a list of instructions: possibly a GEP prefix + the
 * (potentially modified) original instruction.
 *
 * Checks both write and read offsets. Write is checked first
 * (matching Python iteration order).
 *)
Definition fix_mem_inst_def:
  fix_mem_inst alloca1 alloca2 inst =
    let id = inst.inst_id in
    let (prefix1, inst1) =
      case get_mem_write_offset inst of
        NONE => ([], inst)
      | SOME op =>
          case fix_offset_op id alloca1 alloca2 op of
            NONE => ([], inst)
          | SOME (gep, new_op) =>
              ([gep], set_mem_write_offset inst new_op) in
    let (prefix2, inst2) =
      case get_mem_read_offset inst1 of
        NONE => ([], inst1)
      | SOME op =>
          case fix_offset_op (id + 1) alloca1 alloca2 op of
            NONE => ([], inst1)
          | SOME (gep, new_op) =>
              ([gep], set_mem_read_offset inst1 new_op) in
    prefix1 ++ prefix2 ++ [inst2]
End

(* ===== Block and Function Transform ===== *)

(* Transform a block. *)
Definition fix_mem_block_def:
  fix_mem_block alloca1 alloca2 bb =
    bb with bb_instructions :=
      FLAT (MAP (fix_mem_inst alloca1 alloca2) bb.bb_instructions)
End

(*
 * Transform a function:
 * 1. Create two pinned allocas (32 bytes each) at entry
 * 2. Rewrite all memory accesses in FREE_VAR_SPACE range
 *
 * The allocas are inserted at the start of the entry block.
 *)
Definition fix_mem_function_def:
  fix_mem_function fn =
    case fn.fn_blocks of
      [] => fn
    | entry :: rest =>
        let alloca1 = fml_alloca1_var in
        let alloca2 = fml_alloca2_var in
        let alloca_insts = [
          <| inst_id := 0; inst_opcode := ALLOCA;
             inst_operands := [Lit 32w]; inst_outputs := [alloca1] |>;
          <| inst_id := 1; inst_opcode := ALLOCA;
             inst_operands := [Lit 32w]; inst_outputs := [alloca2] |>
        ] in
        let entry' = entry with bb_instructions :=
          alloca_insts ++ (FLAT (MAP (fix_mem_inst alloca1 alloca2)
                                    entry.bb_instructions)) in
        let rest' = MAP (fix_mem_block alloca1 alloca2) rest in
        fn with fn_blocks := entry' :: rest'
End

(* Transform all functions in a context. *)
Definition fix_mem_context_def:
  fix_mem_context ctx =
    ctx with ctx_functions := MAP fix_mem_function ctx.ctx_functions
End

(* ===== Fresh Variable Tracking ===== *)

Definition fml_fresh_vars_fn_def:
  fml_fresh_vars_fn fn =
    {fml_alloca1_var; fml_alloca2_var} UNION
    BIGUNION (set (MAP (\bb.
      BIGUNION (set (MAP (\inst.
        {fml_gep_var inst.inst_id; fml_gep_var (inst.inst_id + 1)})
        bb.bb_instructions)))
      fn.fn_blocks))
End
