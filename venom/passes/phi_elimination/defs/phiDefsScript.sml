(*
 * PHI Elimination — Definitions
 *
 * PHI-specific definitions for the elimination pass:
 *   - dfg_lookup: singleton-output filtered DFG lookup
 *   - ssa_form: SSA well-formedness predicate
 *   - dfg_ids: instruction IDs visible through dfg_lookup
 *   - phi_var_operands, phi_well_formed: PHI operand helpers
 *   - assign_var_operand, is_phi_inst: instruction classification
 *)

Theory phiDefs
Ancestors
  dfgDefs dfgAnalysisProps pred_set list finite_map
  venomState venomInst venomWf venomExecSemantics

(* ==========================================================================
   Shared DFG compatibility layer
   ========================================================================== *)

Type dfg = ``:dfg_analysis``

(* PHI compatibility lookup: only singleton-output defs are visible. *)
Definition dfg_lookup_def:
  dfg_lookup dfg v =
    case dfg_get_def dfg v of
      NONE => NONE
    | SOME inst =>
        if inst.inst_outputs = [v] then SOME inst else NONE
End

Theorem dfg_lookup_implies_get_def:
  !dfg v inst.
    dfg_lookup dfg v = SOME inst
    ==>
    dfg_get_def dfg v = SOME inst /\ inst.inst_outputs = [v]
Proof
  rw[dfg_lookup_def] >> gvs[AllCaseEqs()]
QED

Theorem dfg_lookup_single_output:
  !dfg v inst.
    dfg_lookup dfg v = SOME inst ==> inst.inst_outputs = [v]
Proof
  metis_tac[dfg_lookup_implies_get_def]
QED

Theorem dfg_build_function_lookup_correct:
  !fn v inst.
    dfg_lookup (dfg_build_function fn) v = SOME inst
    ==>
    inst.inst_outputs = [v] /\ MEM inst (fn_insts fn)
Proof
  rpt strip_tac >>
  drule dfg_lookup_implies_get_def >> strip_tac >>
  drule dfg_build_function_correct >> simp[]
QED

(* ssa_form and is_phi_inst are now in venomWfTheory *)

(* IDs visible through compatibility lookup (for termination measure). *)
Definition dfg_ids_def:
  dfg_ids dfg = { inst.inst_id | ?v. dfg_lookup dfg v = SOME inst }
End

Theorem dfg_ids_subset_dfg_def_ids:
  !dfg. dfg_ids dfg SUBSET dfg_def_ids dfg
Proof
  rw[dfg_ids_def, SUBSET_DEF, GSPECIFICATION] >>
  drule dfg_lookup_implies_get_def >> strip_tac >>
  drule dfg_get_def_implies_dfg_def_ids >> simp[]
QED

Theorem dfg_ids_finite:
  !dfg. FINITE (dfg_ids dfg)
Proof
  metis_tac[dfg_ids_subset_dfg_def_ids, dfg_def_ids_finite, SUBSET_FINITE]
QED

Theorem dfg_lookup_implies_dfg_ids:
  !dfg v inst.
    dfg_lookup dfg v = SOME inst ==> inst.inst_id IN dfg_ids dfg
Proof
  rw[dfg_ids_def, GSPECIFICATION] >> metis_tac[]
QED

(* ==========================================================================
   PHI instruction helpers
   ========================================================================== *)

(* Helper: Extract variable names from PHI operands (Label,Var pairs) *)
Definition phi_var_operands_def:
  phi_var_operands [] = [] /\
  phi_var_operands [_] = [] /\
  phi_var_operands (Label lbl :: Var v :: rest) = v :: phi_var_operands rest /\
  phi_var_operands (_ :: _ :: rest) = phi_var_operands rest
End

(* Helper: Extract variable from ASSIGN if operand is a single variable *)
Definition assign_var_operand_def:
  assign_var_operand inst =
    case inst.inst_operands of
      [Var v] => SOME v
    | _ => NONE
End

(* Helper: resolve_phi returns one of the phi_var_operands.
   Used to establish that PHI resolution gives a variable we can look up. *)
Theorem resolve_phi_in_operands:
  !prev_bb ops v.
    resolve_phi prev_bb ops = SOME (Var v) ==>
    MEM v (phi_var_operands ops)
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_var_operands_def] >>
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  TRY (disj2_tac) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  rpt strip_tac >> res_tac
QED
