(*
 * SSA Construction Block-Level: Instruction Compatibility
 *
 * TOP-LEVEL:
 *   - inst_ssa_compatible_def
 *
 * Helpers:
 *   - eval_renamed_operand
 *   - exec_*_ssa_equiv, exec_*_not_halt
 *)

Theory mkSsaBlockCompat
Ancestors
  mkSsaDefs mkSsaTransform mkSsaStateEquiv mkSsaWellFormed
  venomState venomInst venomSem list finite_map

(* ==========================================================================
   Binary/Unary/Mod Operations Preserve SSA Equivalence
   ========================================================================== *)

(* Helper: eval_operand with renamed operand gives same result *)
Theorem eval_renamed_operand:
  !vm s_orig s_ssa ns op.
    ssa_state_equiv vm s_orig s_ssa /\
    (!v. FLOOKUP vm v = SOME (ssa_var_name v (stack_top ns v)) \/
         (FLOOKUP vm v = NONE /\ stack_top ns v = 0)) ==>
    eval_operand op s_orig = eval_operand (rename_operand ns op) s_ssa
Proof
  rpt strip_tac >>
  Cases_on `op` >> fs[rename_operand_def, eval_operand_def] >>
  fs[ssa_state_equiv_def, var_map_equiv_def] >>
  first_x_assum (qspec_then `s` mp_tac) >>
  strip_tac >> fs[ssa_var_name_def]
QED

(* Helper: exec_binop never returns Halt *)
Theorem exec_binop_not_halt:
  !f inst s r. exec_binop f inst s <> Halt r
Proof
  rw[exec_binop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_unop never returns Halt *)
Theorem exec_unop_not_halt:
  !f inst s r. exec_unop f inst s <> Halt r
Proof
  rw[exec_unop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_modop never returns Halt *)
Theorem exec_modop_not_halt:
  !f inst s r. exec_modop f inst s <> Halt r
Proof
  rw[exec_modop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: Binary operation preserves SSA equivalence.
   The SSA output variable must be fresh (not used elsewhere in the mapping).
   In SSA construction, this is guaranteed by using version numbers. *)
Theorem exec_binop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    inst_ssa.inst_opcode = inst.inst_opcode /\
    (case inst.inst_outputs of
       [out] => ?ssa_out.
         inst_ssa.inst_outputs = [ssa_out] /\
         (* Freshness: ssa_out not used by any other mapping *)
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => inst_ssa.inst_outputs = inst.inst_outputs) /\
    exec_binop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_binop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_binop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  gvs[AllCaseEqs()] >>
  (* Use eval_operand_ssa_equiv *)
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  (* Provide witnesses *)
  qexists_tac `vm |+ (out, ssa_out)` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* Helper: Unary operation preserves SSA equivalence *)
Theorem exec_unop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    inst_ssa.inst_opcode = inst.inst_opcode /\
    (case inst.inst_outputs of
       [out] => ?ssa_out.
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => inst_ssa.inst_outputs = inst.inst_outputs) /\
    exec_unop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_unop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  gvs[AllCaseEqs()] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  qexists_tac `vm |+ (out, ssa_out)` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* Helper: Modular operation preserves SSA equivalence *)
Theorem exec_modop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    inst_ssa.inst_opcode = inst.inst_opcode /\
    (case inst.inst_outputs of
       [out] => ?ssa_out.
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => inst_ssa.inst_outputs = inst.inst_outputs) /\
    exec_modop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_modop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  Cases_on `t` >> fs[] >>
  gvs[AllCaseEqs()] >>
  `eval_operand h s_orig = eval_operand (ssa_operand vm h) s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h' s_orig = eval_operand (ssa_operand vm h') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  `eval_operand h'' s_orig = eval_operand (ssa_operand vm h'') s_ssa` by
    (irule eval_operand_ssa_equiv >> simp[]) >>
  gvs[] >>
  qexists_tac `vm |+ (out, ssa_out)` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* ==========================================================================
   Instruction Step Equivalence
   ========================================================================== *)

(* KEY LEMMA: Transform of instruction is well-formed for equivalence.
   The freshness conditions ensure the SSA output variable doesn't collide
   with other mappings in vm. In practice, SSA construction uses versioned
   names like "x:1" that are guaranteed fresh. *)
Definition inst_ssa_compatible_def:
  inst_ssa_compatible vm inst inst_ssa <=>
    inst_ssa.inst_opcode = inst.inst_opcode /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (* Freshness: ssa_out not used by any other mapping *)
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (* ssa_out doesn't collide with other unmapped variables *)
         (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
     | _ => T)  (* Multi-output not fully handled *)
End

(* Helper: inst_ssa_compatible preserves opcode equality *)
Theorem inst_ssa_compatible_opcode:
  !vm inst inst_ssa.
    inst_ssa_compatible vm inst inst_ssa ==>
    inst_ssa.inst_opcode = inst.inst_opcode
Proof
  rw[inst_ssa_compatible_def]
QED

(* Helper: inst_ssa_compatible preserves operand mapping *)
Theorem inst_ssa_compatible_operands:
  !vm inst inst_ssa.
    inst_ssa_compatible vm inst inst_ssa ==>
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands
Proof
  rw[inst_ssa_compatible_def]
QED

(* Helper: inst_ssa_compatible implies freshness for output *)
Theorem inst_ssa_compatible_output_fresh:
  !vm inst inst_ssa out.
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_outputs = [out] ==>
    ?ssa_out.
      inst_ssa.inst_outputs = [ssa_out] /\
      (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
      (!v. v <> out /\ FLOOKUP vm v = NONE ==> v <> ssa_out)
Proof
  rw[inst_ssa_compatible_def] >>
  Cases_on `FLOOKUP vm out` >> gvs[] >>
  metis_tac[]
QED
