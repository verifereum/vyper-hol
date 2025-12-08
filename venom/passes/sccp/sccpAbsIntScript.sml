(*
 * SCCP Abstract Interpretation
 *
 * Matches _visit_expr and _eval from vyper/venom/passes/sccp/sccp.py
 *
 * Abstract interpretation of instructions:
 * - If any operand is BOTTOM => result is BOTTOM
 * - If any operand is TOP => result is TOP
 * - Otherwise evaluate with concrete values
 *)

Theory sccpAbsInt
Ancestors
  sccpLattice venomSem

(* ==========================================================================
   Abstract Evaluation of Binary Operations (matches _eval in sccp.py)

   For arithmetic ops:
   - If any operand is BOTTOM => BOTTOM
   - If any operand is TOP => TOP
   - Otherwise compute the result
   ========================================================================== *)

Definition abs_binop_def:
  abs_binop (f: bytes32 -> bytes32 -> bytes32) lv1 lv2 =
    case (lv1, lv2) of
      (BOTTOM, _) => BOTTOM
    | (_, BOTTOM) => BOTTOM
    | (TOP, _) => TOP
    | (_, TOP) => TOP
    | (Const v1, Const v2) => Const (f v1 v2)
End

Definition abs_unop_def:
  abs_unop (f: bytes32 -> bytes32) lv =
    case lv of
      BOTTOM => BOTTOM
    | TOP => TOP
    | Const v => Const (f v)
End

(* ==========================================================================
   Abstract Interpretation of Instructions (matches _visit_expr)

   Returns the new lattice value for the output variable, if any.
   ========================================================================== *)

(* Abstract step for a single instruction - updates lattice environment *)
Definition abs_step_inst_def:
  abs_step_inst (lenv: lattice_env) (inst: instruction) =
    case inst.inst_output of
      NONE => lenv  (* No output, lattice unchanged *)
    | SOME out_var =>
        let new_val =
          case inst.inst_opcode of
            (* ASSIGN: propagate the operand's lattice value *)
            ASSIGN =>
              (case inst.inst_operands of
                 [op] => abs_operand lenv op
               | _ => BOTTOM)
            (* Binary arithmetic ops *)
          | ADD =>
              (case inst.inst_operands of
                 [op1; op2] => abs_binop word_add
                                 (abs_operand lenv op1)
                                 (abs_operand lenv op2)
               | _ => BOTTOM)
          | SUB =>
              (case inst.inst_operands of
                 [op1; op2] => abs_binop word_sub
                                 (abs_operand lenv op1)
                                 (abs_operand lenv op2)
               | _ => BOTTOM)
          | MUL =>
              (case inst.inst_operands of
                 [op1; op2] => abs_binop word_mul
                                 (abs_operand lenv op1)
                                 (abs_operand lenv op2)
               | _ => BOTTOM)
            (* For other ops, conservatively return BOTTOM *)
          | _ => BOTTOM
        in
          lattice_update out_var new_val lenv
End

(* ==========================================================================
   Abstract Interpretation of PHI (matches _visit_phi)

   PHI takes the meet of all incoming values from executed predecessors.
   We extract variable operands and take meet of their lattice values.
   ========================================================================== *)

(* Extract variable names from PHI operands (label/var pairs) *)
Definition phi_vars_def:
  phi_vars [] = [] /\
  phi_vars [_] = [] /\
  phi_vars (lbl :: Var v :: rest) = v :: phi_vars rest /\
  phi_vars (_ :: _ :: rest) = phi_vars rest
End

(* Meet over a list of lattice values *)
Definition lattice_meet_list_def:
  lattice_meet_list [] = TOP /\
  lattice_meet_list [x] = x /\
  lattice_meet_list (x::y::rest) = lattice_meet x (lattice_meet_list (y::rest))
End

(* Abstract PHI: meet of all operand variable values *)
Definition abs_phi_def:
  abs_phi (lenv: lattice_env) (ops: operand list) =
    lattice_meet_list (MAP (\v. lattice_lookup v lenv) (phi_vars ops))
End

(* ==========================================================================
   Soundness of Abstract Interpretation

   Key theorem: if the abstract interpretation gives Const c,
   then concrete execution gives c.
   ========================================================================== *)

Theorem abs_binop_sound:
  !f lv1 lv2 v1 v2.
    lattice_sound lv1 v1 /\
    lattice_sound lv2 v2
  ==>
    lattice_sound (abs_binop f lv1 lv2) (f v1 v2)
Proof
  cheat
QED

Theorem abs_unop_sound:
  !f lv v.
    lattice_sound lv v
  ==>
    lattice_sound (abs_unop f lv) (f v)
Proof
  cheat
QED

(* Main soundness theorem for abstract step *)
Theorem abs_step_inst_sound:
  !lenv s inst s'.
    env_sound lenv s /\
    step_inst inst s = OK s'
  ==>
    env_sound (abs_step_inst lenv inst) s'
Proof
  cheat
QED

