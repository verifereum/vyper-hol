(*
 * SCCP Lattice Definitions
 *
 * Matches the lattice structure from vyper/venom/passes/sccp/sccp.py
 *
 * The lattice:
 * - TOP: undefined/unknown (initial state)
 * - Const v: a definite constant value
 * - BOTTOM: multiple possible values (not constant)
 *
 * Meet operation (from _meet in sccp.py):
 * - TOP meet y = y
 * - y meet TOP = x
 * - x meet x = x
 * - otherwise BOTTOM
 *)

Theory sccpLattice
Ancestors
  finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   Lattice Value Type (matches LatticeEnum + IRLiteral in Python)
   ========================================================================== *)

Datatype:
  lattice_val =
    TOP
  | Const bytes32
  | BOTTOM
End

(* ==========================================================================
   Lattice Meet Operation (matches _meet function in sccp.py)
   ========================================================================== *)

Definition lattice_meet_def:
  lattice_meet TOP y = y /\
  lattice_meet x TOP = x /\
  lattice_meet BOTTOM _ = BOTTOM /\
  lattice_meet _ BOTTOM = BOTTOM /\
  lattice_meet (Const v1) (Const v2) =
    if v1 = v2 then Const v1 else BOTTOM
End

(* Properties - structure only, proofs cheated for now *)
Theorem lattice_meet_comm:
  !x y. lattice_meet x y = lattice_meet y x
Proof
  cheat
QED

Theorem lattice_meet_assoc:
  !x y z. lattice_meet (lattice_meet x y) z = lattice_meet x (lattice_meet y z)
Proof
  cheat
QED

Theorem lattice_meet_idemp:
  !x. lattice_meet x x = x
Proof
  cheat
QED

Theorem lattice_meet_top_left[simp]:
  !x. lattice_meet TOP x = x
Proof
  cheat
QED

Theorem lattice_meet_top_right[simp]:
  !x. lattice_meet x TOP = x
Proof
  cheat
QED

Theorem lattice_meet_bottom_left[simp]:
  !x. lattice_meet BOTTOM x = BOTTOM
Proof
  cheat
QED

Theorem lattice_meet_bottom_right[simp]:
  !x. lattice_meet x BOTTOM = BOTTOM
Proof
  cheat
QED

(* ==========================================================================
   Lattice Environment (matches self.lattice: dict[IRVariable, LatticeItem])
   ========================================================================== *)

Type lattice_env = ``:(string, lattice_val) fmap``

Definition lattice_lookup_def:
  lattice_lookup v (env: lattice_env) =
    case FLOOKUP env v of
      NONE => TOP  (* Uninitialized variables are TOP *)
    | SOME lv => lv
End

Definition lattice_update_def:
  lattice_update v lv (env: lattice_env) = env |+ (v, lv)
End

(* ==========================================================================
   Abstract Evaluation of Operands (matches _eval_from_lattice)

   - Literal => Const value
   - Variable => lookup in lattice
   - Label => BOTTOM (not a value)
   ========================================================================== *)

Definition abs_operand_def:
  abs_operand (lenv: lattice_env) (Lit v) = Const v /\
  abs_operand lenv (Var x) = lattice_lookup x lenv /\
  abs_operand lenv (Label _) = BOTTOM
End

(* ==========================================================================
   Soundness Relation

   Relates abstract lattice values to concrete runtime values.
   ========================================================================== *)

Definition lattice_sound_def:
  lattice_sound TOP _ = T /\
  lattice_sound (Const c) v = (c = v) /\
  lattice_sound BOTTOM _ = T
End

(* Environment soundness: every variable in the lattice is sound *)
Definition env_sound_def:
  env_sound (lenv: lattice_env) (s: venom_state) <=>
    !v lv. FLOOKUP lenv v = SOME lv ==>
           case lookup_var v s of
             NONE => T
           | SOME c => lattice_sound lv c
End

(* Key soundness theorem for operands *)
Theorem abs_operand_sound:
  !lenv s op v.
    env_sound lenv s /\
    eval_operand op s = SOME v
  ==>
    lattice_sound (abs_operand lenv op) v
Proof
  cheat
QED

