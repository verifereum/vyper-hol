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
  sccpAbsInt sccpLattice venomSem venomState

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

(* Operand transformation is sound: same evaluation result *)
Theorem transform_operand_sound:
  !lenv s op v.
    env_sound lenv s /\
    eval_operand op s = SOME v
  ==>
    eval_operand (transform_operand lenv op) s = SOME v
Proof
  rpt strip_tac >> Cases_on `op` >> simp[transform_operand_def] >>
  (* Only Var case remains *)
  Cases_on `lattice_lookup s' lenv` >> simp[eval_operand_def] >>
  (* Const c case: use env_sound to get c = v *)
  gvs[eval_operand_def, env_sound_def, lattice_lookup_def, lattice_sound_def] >>
  Cases_on `FLOOKUP lenv s'` >> gvs[] >>
  first_x_assum (qspecl_then [`s'`, `Const c`] mp_tac) >> simp[lattice_sound_def]
QED

(* Operand transformation preserves evaluation (when variable is defined) *)
Theorem transform_operand_eq:
  !lenv s op.
    env_sound lenv s /\
    (!x. op = Var x ==> IS_SOME (lookup_var x s))
  ==>
    eval_operand (transform_operand lenv op) s = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >> simp[transform_operand_def, eval_operand_def] >>
  (* Only Var case remains *)
  Cases_on `lattice_lookup s' lenv` >> simp[eval_operand_def] >>
  (* Const c case: use IS_SOME and env_sound *)
  `IS_SOME (lookup_var s' s)` by (first_x_assum (qspec_then `s'` mp_tac) >> simp[]) >>
  Cases_on `lookup_var s' s` >> gvs[] >>
  gvs[env_sound_def, lattice_lookup_def, lattice_sound_def] >>
  Cases_on `FLOOKUP lenv s'` >> gvs[] >>
  first_x_assum (qspecl_then [`s'`, `Const c`] mp_tac) >> simp[lattice_sound_def]
QED

(* Transform operands preserves evaluation *)
Theorem transform_operands_sound:
  !lenv s ops vs.
    env_sound lenv s /\
    eval_operands ops s = SOME vs
  ==>
    eval_operands (transform_operands lenv ops) s = SOME vs
Proof
  Induct_on `ops` >> simp[transform_operands_def, eval_operands_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule_all transform_operand_sound >> simp[transform_operands_def] >>
  REWRITE_TAC[GSYM transform_operands_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

(* ==========================================================================
   Execution Helpers for Transformed Instructions
   ========================================================================== *)

(* exec_binop with transformed operands produces same result *)
Theorem exec_binop_transform:
  !f lenv inst s s'.
    env_sound lenv s /\
    exec_binop f inst s = OK s'
  ==>
    exec_binop f (inst with inst_operands := transform_operands lenv inst.inst_operands) s = OK s'
Proof
  rpt strip_tac >> gvs[exec_binop_def, AllCaseEqs()] >>
  simp[transform_operands_def] >>
  `eval_operand (transform_operand lenv op1) s = SOME v1` by
    (irule transform_operand_sound >> simp[]) >>
  `eval_operand (transform_operand lenv op2) s = SOME v2` by
    (irule transform_operand_sound >> simp[]) >>
  simp[]
QED

(* exec_unop with transformed operands produces same result *)
Theorem exec_unop_transform:
  !f lenv inst s s'.
    env_sound lenv s /\
    exec_unop f inst s = OK s'
  ==>
    exec_unop f (inst with inst_operands := transform_operands lenv inst.inst_operands) s = OK s'
Proof
  rpt strip_tac >> gvs[exec_unop_def, AllCaseEqs()] >>
  simp[transform_operands_def] >>
  `eval_operand (transform_operand lenv op1) s = SOME v` by
    (irule transform_operand_sound >> simp[]) >>
  simp[]
QED

(* exec_modop with transformed operands produces same result *)
Theorem exec_modop_transform:
  !f lenv inst s s'.
    env_sound lenv s /\
    exec_modop f inst s = OK s'
  ==>
    exec_modop f (inst with inst_operands := transform_operands lenv inst.inst_operands) s = OK s'
Proof
  rpt strip_tac >> gvs[exec_modop_def, AllCaseEqs()] >>
  simp[transform_operands_def] >>
  `eval_operand (transform_operand lenv op1) s = SOME v1` by
    (irule transform_operand_sound >> simp[]) >>
  `eval_operand (transform_operand lenv op2) s = SOME v2` by
    (irule transform_operand_sound >> simp[]) >>
  `eval_operand (transform_operand lenv op3) s = SOME v3` by
    (irule transform_operand_sound >> simp[]) >>
  simp[]
QED

(* ==========================================================================
   Result Type Properties
   These lemmas show exec_binop/unop/modop only return OK or Error
   ========================================================================== *)

Theorem exec_binop_not_halt:
  !f inst s v. exec_binop f inst s <> Halt v
Proof
  simp[exec_binop_def, AllCaseEqs()]
QED

Theorem exec_binop_not_revert:
  !f inst s v. exec_binop f inst s <> Revert v
Proof
  simp[exec_binop_def, AllCaseEqs()]
QED

Theorem exec_unop_not_halt:
  !f inst s v. exec_unop f inst s <> Halt v
Proof
  simp[exec_unop_def, AllCaseEqs()]
QED

Theorem exec_unop_not_revert:
  !f inst s v. exec_unop f inst s <> Revert v
Proof
  simp[exec_unop_def, AllCaseEqs()]
QED

Theorem exec_modop_not_halt:
  !f inst s v. exec_modop f inst s <> Halt v
Proof
  simp[exec_modop_def, AllCaseEqs()]
QED

Theorem exec_modop_not_revert:
  !f inst s v. exec_modop f inst s <> Revert v
Proof
  simp[exec_modop_def, AllCaseEqs()]
QED

