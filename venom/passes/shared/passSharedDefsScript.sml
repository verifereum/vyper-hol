(*
 * Pass Shared Definitions
 *
 * Common helpers used by multiple optimization passes.
 * Opcode-level predicates (is_volatile, is_terminator) live in venomInst.
 *
 * TOP-LEVEL:
 *   is_removable          — instruction can be NOP'd if output unused
 *   mk_nop_inst           — replace instruction with NOP
 *   mk_assign_inst        — replace instruction with ASSIGN from operand
 *   ml_is_fixed           — memory location has known offset + size
 *   is_copy_opcode        — bulk memory copy opcodes (MCOPY, etc.)
 *   is_store_opcode       — single-word store opcodes (MSTORE, etc.)
 *   load_opcode_addr_space  — map load opcode to address space
 *   store_opcode_addr_space — map store opcode to address space
 *   (addr_space_word_scale is in venomEffects)
 *   subst_operand         — substitute a variable in an operand
 *   subst_operands        — substitute a variable across all operands
 *   subst_operands_map    — substitute multiple variables via fmap
 *)

Theory passSharedDefs
Ancestors
  venomInst venomEffects memLocDefs

(* ===== Removability ===== *)

(* An instruction is removable (can be NOP'd) if:
   - it is not volatile
   - it is not a terminator
   - it has outputs (otherwise it's already effectful or a no-op) *)
Definition is_removable_def:
  is_removable inst <=>
    ~is_volatile inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_outputs <> []
End

(* ===== Instruction builders ===== *)

(* Replace an instruction with NOP, clearing operands and outputs *)
Definition mk_nop_inst_def:
  mk_nop_inst inst =
    inst with <| inst_opcode := NOP;
                 inst_operands := [];
                 inst_outputs := [] |>
End

(* Replace an instruction with ASSIGN from a single operand.
   Preserves inst_id and inst_outputs. *)
Definition mk_assign_inst_def:
  mk_assign_inst inst src_op =
    inst with <| inst_opcode := ASSIGN;
                 inst_operands := [src_op] |>
End

(* ===== PHI helpers ===== *)

(* Extract variable names that appear as value operands in PHI
   instructions. PHI operands are [Label l1, Var v1, Label l2, Var v2, ...].
   Returns the list of variable names [v1, v2, ...]. *)
Definition phi_value_vars_def:
  phi_value_vars [] = [] /\
  phi_value_vars [_] = [] /\
  phi_value_vars (Label _ :: Var v :: rest) = v :: phi_value_vars rest /\
  phi_value_vars (_ :: _ :: rest) = phi_value_vars rest
End

(* Collect all variable names that appear as value operands in any
   PHI instruction across the function. *)
Definition phi_used_vars_def:
  phi_used_vars fn =
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst.
        if inst.inst_opcode = PHI then phi_value_vars inst.inst_operands
        else [])
        bb.bb_instructions))
      fn.fn_blocks))
End

(* ===== Store opcode predicate ===== *)

(* Memory/storage/transient store instructions *)
Definition is_store_opcode_def:
  is_store_opcode MSTORE = T /\
  is_store_opcode SSTORE = T /\
  is_store_opcode TSTORE = T /\
  is_store_opcode _ = F
End

(* NOTE: is_alloca_op already in venomInst — use that instead *)

(* ===== Copy opcode predicate ===== *)

(* Bulk memory copy opcodes *)
Definition is_copy_opcode_def:
  is_copy_opcode MCOPY = T /\
  is_copy_opcode CALLDATACOPY = T /\
  is_copy_opcode CODECOPY = T /\
  is_copy_opcode DLOADBYTES = T /\
  is_copy_opcode RETURNDATACOPY = T /\
  is_copy_opcode _ = F
End

(* ===== Opcode ↔ address space mappings ===== *)

(* Map load opcode to its address space *)
Definition load_opcode_addr_space_def:
  load_opcode_addr_space MLOAD = AddrSp_Memory /\
  load_opcode_addr_space SLOAD = AddrSp_Storage /\
  load_opcode_addr_space TLOAD = AddrSp_Transient /\
  load_opcode_addr_space _ = AddrSp_Memory  (* default; shouldn't happen *)
End

(* Map store opcode to its address space *)
Definition store_opcode_addr_space_def:
  store_opcode_addr_space MSTORE = AddrSp_Memory /\
  store_opcode_addr_space SSTORE = AddrSp_Storage /\
  store_opcode_addr_space TSTORE = AddrSp_Transient /\
  store_opcode_addr_space _ = AddrSp_Memory
End

(* ===== Operand substitution ===== *)

(* Substitute a single variable: if operand is Var old, replace with new_op *)
Definition subst_operand_def:
  subst_operand old new_op (Var v) =
    (if v = old then new_op else Var v) /\
  subst_operand old new_op op = op
End

(* Substitute across all operands of an instruction *)
Definition subst_operands_def:
  subst_operands old new_op inst =
    inst with inst_operands :=
      MAP (subst_operand old new_op) inst.inst_operands
End

(* Substitute a single operand using a substitution map *)
Definition subst_op_map_def:
  subst_op_map (subs : (string, operand) fmap) (Var v) =
    (case FLOOKUP subs v of SOME new_op => new_op | NONE => Var v) /\
  subst_op_map subs (Lit w) = Lit w /\
  subst_op_map subs (Label l) = Label l
End

(* Substitute multiple variables (from a finite map) *)
Definition subst_operands_map_def:
  subst_operands_map (subs : (string, operand) fmap) inst =
    inst with inst_operands :=
      MAP (subst_op_map subs) inst.inst_operands
End

(* ===== Copy propagation helpers ===== *)

(* An ASSIGN instruction is "forwardable" if:
   1. Source variable doesn't feed a PHI (literals always pass)
   2. Output variable doesn't feed a PHI
   Used by copy propagation (assign_elim) transfer, transform,
   and eliminated_vars computation.
   phi_vars = phi_used_vars fn *)
Definition is_forwardable_assign_def:
  is_forwardable_assign (phi_vars : string set) inst <=>
    inst.inst_opcode = ASSIGN /\
    (case (inst.inst_operands, inst.inst_outputs) of
       ([src_op], [out]) =>
         (case src_op of Var v => v NOTIN phi_vars | _ => T) /\
         out NOTIN phi_vars
     | _ => F)
End

(* ===== Memory location helpers ===== *)

(* A memory location is "fixed" when it has known offset + size.
   Python: MemoryLocation.is_fixed. Only fixed locations are tracked
   as lattice keys in analyses. *)
Definition ml_is_fixed_def:
  ml_is_fixed loc <=> IS_SOME loc.ml_offset /\ IS_SOME loc.ml_size
End

(* ===== NOP clearing ===== *)

(* Remove NOP instructions from a block.
   Matches Python's IRBasicBlock.clear_nops(). *)
Definition clear_nops_block_def:
  clear_nops_block bb =
    bb with bb_instructions :=
      FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions
End

(* Remove NOPs from all blocks in a function *)
Definition clear_nops_function_def:
  clear_nops_function fn =
    fn with fn_blocks := MAP clear_nops_block fn.fn_blocks
End
