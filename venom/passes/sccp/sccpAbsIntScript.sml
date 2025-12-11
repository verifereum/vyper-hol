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
  sccpLattice venomSem venomState finite_map

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
    case inst.inst_outputs of
      [] => lenv  (* No output, lattice unchanged *)
    | [out_var] =>
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
    | _ => lenv  (* Multiple outputs not handled *)
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
  Cases_on `lv1` >> Cases_on `lv2` >> simp[abs_binop_def, lattice_sound_def]
QED

Theorem abs_unop_sound:
  !f lv v.
    lattice_sound lv v
  ==>
    lattice_sound (abs_unop f lv) (f v)
Proof
  Cases_on `lv` >> simp[abs_unop_def, lattice_sound_def]
QED

(* Helper: BOTTOM is always sound *)
Theorem lattice_sound_bottom[simp]:
  !v. lattice_sound BOTTOM v
Proof
  simp[lattice_sound_def]
QED

(* ==========================================================================
   Helper lemmas for abs_step_inst_sound
   ========================================================================== *)

(* env_sound only depends on vs_vars *)
Theorem env_sound_vs_vars_eq:
  !lenv s s'.
    s'.vs_vars = s.vs_vars /\ env_sound lenv s ==> env_sound lenv s'
Proof
  rw[env_sound_def, lookup_var_def]
QED

(* Adding BOTTOM to the lattice preserves soundness *)
Theorem env_sound_lattice_update_bottom:
  !lenv s x. env_sound lenv s ==> env_sound (lattice_update x BOTTOM lenv) s
Proof
  rw[env_sound_def, lattice_update_def, FLOOKUP_UPDATE] >>
  Cases_on `v = x` >> gvs[lattice_sound_def] >>
  Cases_on `lookup_var v s` >> simp[]
QED

(* Combined: BOTTOM lattice update with state change preserving vs_vars *)
Theorem env_sound_lattice_update_bottom_vs_vars:
  !lenv s s' x.
    env_sound lenv s /\ s'.vs_vars = s.vs_vars ==>
    env_sound (lattice_update x BOTTOM lenv) s'
Proof
  rw[env_sound_def, lattice_update_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `v = x` >> gvs[lattice_sound_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> simp[]
QED

(* When step_inst returns OK with no output, vs_vars is unchanged *)
Theorem step_inst_no_output_vars:
  !inst s s'.
    step_inst inst s = OK s' /\ inst.inst_outputs = [] ==>
    s'.vs_vars = s.vs_vars
Proof
  rw[step_inst_def] >> Cases_on `inst.inst_opcode` >>
  gvs[AllCaseEqs(), exec_binop_def, exec_unop_def, exec_modop_def] >>
  gvs[mstore_def, sstore_def, tstore_def, jump_to_def]
QED

(* When step_inst returns OK with single output via exec_binop, s' = update_var out v s *)
Theorem exec_binop_single_output:
  !f inst s s'.
    exec_binop f inst s = OK s' ==>
    ?out v. inst.inst_outputs = [out] /\ s' = update_var out v s
Proof
  rw[exec_binop_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_unop_single_output:
  !f inst s s'.
    exec_unop f inst s = OK s' ==>
    ?out v. inst.inst_outputs = [out] /\ s' = update_var out v s
Proof
  rw[exec_unop_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_modop_single_output:
  !f inst s s'.
    exec_modop f inst s = OK s' ==>
    ?out v. inst.inst_outputs = [out] /\ s' = update_var out v s
Proof
  rw[exec_modop_def, AllCaseEqs()] >> metis_tac[]
QED

(* When step_inst returns OK with multiple outputs, vs_vars unchanged *)
(* This is because opcodes that modify vs_vars all require single output *)
Theorem step_inst_multi_output_vars:
  !inst s s' o1 o2 rest.
    step_inst inst s = OK s' /\ inst.inst_outputs = o1::o2::rest ==>
    s'.vs_vars = s.vs_vars
Proof
  rw[step_inst_def] >> Cases_on `inst.inst_opcode` >>
  gvs[AllCaseEqs(), exec_binop_def, exec_unop_def, exec_modop_def] >>
  gvs[mstore_def, sstore_def, tstore_def, jump_to_def]
QED

(* Helper for ASSIGN soundness *)
Theorem step_inst_assign_value:
  !inst s s' out.
    step_inst inst s = OK s' /\
    inst.inst_opcode = ASSIGN /\
    inst.inst_outputs = [out] ==>
    ?op v. inst.inst_operands = [op] /\
           eval_operand op s = SOME v /\
           s' = update_var out v s
Proof
  rw[step_inst_def, AllCaseEqs()] >> gvs[] >>
  qexists_tac `op1` >> qexists_tac `v` >> simp[]
QED

(* Helper for ADD soundness *)
Theorem step_inst_add_value:
  !inst s s' out.
    step_inst inst s = OK s' /\
    inst.inst_opcode = ADD /\
    inst.inst_outputs = [out] ==>
    ?op1 op2 v1 v2. inst.inst_operands = [op1; op2] /\
                    eval_operand op1 s = SOME v1 /\
                    eval_operand op2 s = SOME v2 /\
                    s' = update_var out (word_add v1 v2) s
Proof
  rw[step_inst_def, exec_binop_def, AllCaseEqs()] >> gvs[]
QED

(* Helper for SUB soundness *)
Theorem step_inst_sub_value:
  !inst s s' out.
    step_inst inst s = OK s' /\
    inst.inst_opcode = SUB /\
    inst.inst_outputs = [out] ==>
    ?op1 op2 v1 v2. inst.inst_operands = [op1; op2] /\
                    eval_operand op1 s = SOME v1 /\
                    eval_operand op2 s = SOME v2 /\
                    s' = update_var out (word_sub v1 v2) s
Proof
  rw[step_inst_def, exec_binop_def, AllCaseEqs()] >> gvs[]
QED

(* Helper for MUL soundness *)
Theorem step_inst_mul_value:
  !inst s s' out.
    step_inst inst s = OK s' /\
    inst.inst_opcode = MUL /\
    inst.inst_outputs = [out] ==>
    ?op1 op2 v1 v2. inst.inst_operands = [op1; op2] /\
                    eval_operand op1 s = SOME v1 /\
                    eval_operand op2 s = SOME v2 /\
                    s' = update_var out (word_mul v1 v2) s
Proof
  rw[step_inst_def, exec_binop_def, AllCaseEqs()] >> gvs[]
QED

(* Helper: env_sound preserved when vs_vars updated and lattice updated with sound value *)
Theorem env_sound_update_vs_vars:
  !lenv s s' out lv v.
    env_sound lenv s /\
    lattice_sound lv v /\
    s'.vs_vars = s.vs_vars |+ (out, v) ==>
    env_sound (lattice_update out lv lenv) s'
Proof
  rw[env_sound_def, lattice_update_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = out` >> gvs[]
QED

(* Helper for single-output binop cases *)
Theorem abs_step_binop_sound:
  !lenv s inst s' h f.
    env_sound lenv s /\
    exec_binop f inst s = OK s' /\
    inst.inst_outputs = [h] ==>
    env_sound (lattice_update h
                 (case inst.inst_operands of
                    [] => BOTTOM
                  | [op1] => BOTTOM
                  | [op1; op2] => abs_binop f (abs_operand lenv op1) (abs_operand lenv op2)
                  | _ => BOTTOM) lenv) s'
Proof
  rw[exec_binop_def, AllCaseEqs()] >> gvs[] >>
  irule env_sound_update >> simp[] >>
  irule abs_binop_sound >> simp[] >>
  conj_tac >> irule abs_operand_sound >> qexists_tac `s` >> simp[]
QED

(* Tactic for handling single-output cases after opcode split and exec unfold *)
val single_output_tac =
  (* ADD/SUB/MUL with abs_binop - proves update_var goal with abs_binop *)
  (irule env_sound_update >> simp[] >>
   irule abs_binop_sound >> simp[] >>
   conj_tac >> irule abs_operand_sound >> qexists_tac `s` >> simp[])
  ORELSE
  (* ASSIGN with abs_operand - proves update_var goal with abs_operand *)
  (irule env_sound_update >> simp[] >>
   irule abs_operand_sound >> qexists_tac `s` >> simp[])
  ORELSE
  (* Other update_var cases with BOTTOM - PHI, SLOAD, TLOAD, etc. *)
  (irule env_sound_update >> simp[lattice_sound_def])
  ORELSE
  (* NOP - state unchanged, just lattice update *)
  (irule env_sound_lattice_update_bottom >> simp[])
  ORELSE
  (* JMP/JNZ/MSTORE/SSTORE/TSTORE - state modified but vs_vars preserved *)
  (irule env_sound_lattice_update_bottom_vs_vars >> qexists_tac `s` >>
   simp[jump_to_def, tstore_def, sstore_def, mstore_def]);

(* Main soundness theorem for abstract step *)
Theorem abs_step_inst_sound:
  !lenv s inst s'.
    env_sound lenv s /\
    step_inst inst s = OK s'
  ==>
    env_sound (abs_step_inst lenv inst) s'
Proof
  rpt strip_tac >> simp[abs_step_inst_def] >>
  (* Case split on outputs *)
  Cases_on `inst.inst_outputs` >> gvs[] >-
  (* Empty outputs - vs_vars unchanged *)
  (irule env_sound_vs_vars_eq >> qexists_tac `s` >> simp[] >>
   metis_tac[step_inst_no_output_vars]) >>
  (* h::t case *)
  Cases_on `t` >> gvs[] >>
  (* Single output [h] OR multi output - handle together *)
  Cases_on `inst.inst_opcode` >> gvs[step_inst_def, AllCaseEqs()] >>
  fs[exec_binop_def, exec_unop_def, exec_modop_def, AllCaseEqs()] >> gvs[] >>
  (* Try each tactic in order *)
  TRY (irule env_sound_update >> simp[] >>
       irule abs_binop_sound >> simp[] >>
       conj_tac >> irule abs_operand_sound >> qexists_tac `s` >> simp[]) >>
  TRY (irule env_sound_update >> simp[] >>
       irule abs_operand_sound >> qexists_tac `s` >> simp[]) >>
  TRY (irule env_sound_update >> simp[lattice_sound_def]) >>
  TRY (irule env_sound_lattice_update_bottom >> simp[]) >>
  TRY (irule env_sound_lattice_update_bottom_vs_vars >> qexists_tac `s` >>
       simp[jump_to_def, tstore_def, sstore_def, mstore_def]) >>
  TRY (irule env_sound_vs_vars_eq >> qexists_tac `s` >> simp[] >>
       TRY (metis_tac[step_inst_multi_output_vars]) >>
       simp[jump_to_def, tstore_def, sstore_def, mstore_def])
QED

