(*
 * SCCP Transformation
 *
 * Matches _propagate_constants and _replace_constants from sccp.py
 *
 * The transformation:
 * 1. Replaces variable operands with their constant lattice values
 * 2. Simplifies jnz to jmp when condition is a known constant
 *)

Theory sccpTransform
Ancestors
  sccpAbsInt venomSem

(* ==========================================================================
   Operand Transformation (matches operand replacement in _replace_constants)

   If a variable has a Const lattice value, replace it with a literal.
   ========================================================================== *)

Definition transform_operand_def:
  transform_operand (lenv: lattice_env) (Lit v) = Lit v /\
  transform_operand lenv (Var x) =
    (case lattice_lookup x lenv of
       Const c => Lit c
     | _ => Var x) /\
  transform_operand lenv (Label l) = Label l
End

(* Transform all operands in a list *)
Definition transform_operands_def:
  transform_operands lenv ops = MAP (transform_operand lenv) ops
End

(* ==========================================================================
   Instruction Transformation (matches _replace_constants)
   ========================================================================== *)

Definition transform_inst_def:
  transform_inst (lenv: lattice_env) (inst: instruction) =
    case inst.inst_opcode of
      (* JNZ with constant condition => JMP *)
      JNZ =>
        (case inst.inst_operands of
           [cond_op; true_lbl; false_lbl] =>
             (case abs_operand lenv cond_op of
                Const c =>
                  if c = 0w then
                    (* Jump to false branch *)
                    inst with <| inst_opcode := JMP;
                                 inst_operands := [false_lbl] |>
                  else
                    (* Jump to true branch *)
                    inst with <| inst_opcode := JMP;
                                 inst_operands := [true_lbl] |>
              | _ =>
                  (* Not constant, just transform operands *)
                  inst with inst_operands := transform_operands lenv inst.inst_operands)
         | _ => inst)
      (* PHI nodes are not transformed (handled separately) *)
    | PHI => inst
      (* All other instructions: transform operands *)
    | _ => inst with inst_operands := transform_operands lenv inst.inst_operands
End

(* ==========================================================================
   Block and Function Transformation
   ========================================================================== *)

Definition transform_block_def:
  transform_block (lenv: lattice_env) (bb: basic_block) =
    bb with bb_instructions := MAP (transform_inst lenv) bb.bb_instructions
End

Definition transform_function_def:
  transform_function (lenv: lattice_env) (fn: ir_function) =
    fn with fn_blocks := MAP (transform_block lenv) fn.fn_blocks
End

(* ==========================================================================
   Transformation Properties
   ========================================================================== *)

(* Transform preserves block labels *)
Theorem transform_block_label:
  !lenv bb. (transform_block lenv bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def]
QED

(* Transform preserves instruction count *)
Theorem transform_block_length:
  !lenv bb.
    LENGTH (transform_block lenv bb).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  rw[transform_block_def]
QED

(* Operand transformation is sound *)
Theorem transform_operand_sound:
  !lenv s op v.
    env_sound lenv s /\
    eval_operand op s = SOME v
  ==>
    eval_operand (transform_operand lenv op) s = SOME v
Proof
  cheat
QED

