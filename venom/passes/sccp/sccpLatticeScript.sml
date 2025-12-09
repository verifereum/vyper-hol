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

(* ==========================================================================
   Lattice Properties
   ========================================================================== *)

Theorem lattice_meet_comm:
  !x y. lattice_meet x y = lattice_meet y x
Proof
  Cases >> Cases >> simp[lattice_meet_def] >> rw[EQ_SYM_EQ]
QED

Theorem lattice_meet_assoc:
  !x y z. lattice_meet (lattice_meet x y) z = lattice_meet x (lattice_meet y z)
Proof
  Cases >> Cases >> Cases >> simp[lattice_meet_def] >>
  rpt (COND_CASES_TAC >> simp[lattice_meet_def]) >> metis_tac[]
QED

Theorem lattice_meet_idemp:
  !x. lattice_meet x x = x
Proof
  Cases >> simp[lattice_meet_def]
QED

Theorem lattice_meet_top_left[simp]:
  !x. lattice_meet TOP x = x
Proof
  Cases >> simp[lattice_meet_def]
QED

Theorem lattice_meet_top_right[simp]:
  !x. lattice_meet x TOP = x
Proof
  Cases >> simp[lattice_meet_def]
QED

Theorem lattice_meet_bottom_left[simp]:
  !x. lattice_meet BOTTOM x = BOTTOM
Proof
  Cases >> simp[lattice_meet_def]
QED

Theorem lattice_meet_bottom_right[simp]:
  !x. lattice_meet x BOTTOM = BOTTOM
Proof
  Cases >> simp[lattice_meet_def]
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

(* Soundness of meet: if both inputs are sound for v, output is sound *)
Theorem lattice_sound_meet:
  !lv1 lv2 v.
    lattice_sound lv1 v /\ lattice_sound lv2 v ==>
    lattice_sound (lattice_meet lv1 lv2) v
Proof
  Cases >> Cases >> simp[lattice_meet_def, lattice_sound_def]
QED

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
  rpt strip_tac >> Cases_on `op` >> simp[abs_operand_def] >- (
    (* Lit case *)
    gvs[eval_operand_def, lattice_sound_def]
  ) >- (
    (* Var case *)
    gvs[eval_operand_def] >> fs[env_sound_def] >>
    simp[lattice_lookup_def] >>
    Cases_on `FLOOKUP lenv s'` >> simp[lattice_sound_def] >>
    first_x_assum (qspecl_then [`s'`, `x`] mp_tac) >> simp[]
  ) >- (
    (* Label case - contradiction *)
    gvs[eval_operand_def]
  )
QED

(* Updating both lattice and state preserves soundness *)
Theorem env_sound_update:
  !lenv s var lv v.
    env_sound lenv s /\ lattice_sound lv v ==>
    env_sound (lattice_update var lv lenv) (update_var var v s)
Proof
  rpt strip_tac >>
  simp[env_sound_def, lattice_update_def, update_var_def] >>
  rpt strip_tac >>
  Cases_on `v' = var` >- (
    gvs[FLOOKUP_UPDATE, lookup_var_def]
  ) >- (
    gvs[FLOOKUP_UPDATE, lookup_var_def] >>
    fs[env_sound_def] >>
    first_x_assum (qspecl_then [`v'`, `lv'`] mp_tac) >> simp[lookup_var_def]
  )
QED

