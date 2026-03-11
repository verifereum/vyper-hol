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
 *   subst_operand         — substitute a variable in an operand
 *   subst_operands        — substitute a variable across all operands
 *   subst_operands_map    — substitute multiple variables via fmap
 *)

Theory passSharedDefs
Ancestors
  venomInst

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
