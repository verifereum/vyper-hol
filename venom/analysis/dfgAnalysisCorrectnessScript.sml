(*
 * DFG Analysis Correctness
 *
 * Proof-oriented lemmas over shared dfgAnalysis definitions.
 * This file provides reusable correctness infrastructure for passes that
 * consume the shared DFG.
 *)

Theory dfgAnalysisCorrectness
Ancestors
  dfgAnalysis list finite_map pred_set

(* --------------------------------------------------------------------------
   Bridge-level predicates
   -------------------------------------------------------------------------- *)

Definition well_formed_dfg_def:
  well_formed_dfg dfg <=>
    !v inst. dfg_get_def dfg v = SOME inst ==> MEM v inst.inst_outputs
End

Definition dfg_def_ids_def:
  dfg_def_ids dfg = IMAGE (\inst. inst.inst_id) (FRANGE dfg.dfg_defs)
End

(* --------------------------------------------------------------------------
   Well-formedness preservation
   -------------------------------------------------------------------------- *)

Theorem well_formed_dfg_update:
  !dfg inst v.
    well_formed_dfg dfg /\ MEM v inst.inst_outputs
    ==> well_formed_dfg (dfg with dfg_defs := dfg.dfg_defs |+ (v, inst))
Proof
  rw[well_formed_dfg_def, dfg_get_def_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = v` >> fs[]
QED

Theorem dfg_add_defs_well_formed:
  !dfg vs inst.
    well_formed_dfg dfg /\ EVERY (\v. MEM v inst.inst_outputs) vs
    ==> well_formed_dfg (dfg_add_defs dfg vs inst)
Proof
  Induct_on `vs` >> rw[dfg_add_defs_def] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    match_mp_tac well_formed_dfg_update >>
    simp[]
  ) >>
  simp[]
QED

Theorem dfg_add_use_get_def:
  !dfg v inst u.
    dfg_get_def (dfg_add_use dfg u inst) v = dfg_get_def dfg v
Proof
  rw[dfg_add_use_def, dfg_get_def_def]
QED

Theorem dfg_add_uses_get_def:
  !dfg vs inst v.
    dfg_get_def (dfg_add_uses dfg vs inst) v = dfg_get_def dfg v
Proof
  Induct_on `vs` >> rw[dfg_add_uses_def] >>
  rw[dfg_add_use_get_def]
QED

Theorem dfg_add_uses_preserve_wf:
  !dfg vs inst.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_add_uses dfg vs inst)
Proof
  rw[well_formed_dfg_def] >>
  qpat_x_assum `dfg_get_def (dfg_add_uses dfg vs inst) v = SOME inst'` mp_tac >>
  simp[dfg_add_uses_get_def] >>
  metis_tac[well_formed_dfg_def]
QED

Theorem well_formed_dfg_update_ids:
  !dfg ids. well_formed_dfg dfg ==> well_formed_dfg (dfg with dfg_ids := ids)
Proof
  rw[well_formed_dfg_def, dfg_get_def_def]
QED

Theorem dfg_add_inst_well_formed:
  !dfg inst.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_add_inst dfg inst)
Proof
  rw[dfg_add_inst_def] >>
  match_mp_tac well_formed_dfg_update_ids >>
  match_mp_tac dfg_add_defs_well_formed >>
  conj_tac >- (
    match_mp_tac dfg_add_uses_preserve_wf >>
    simp[]
  ) >>
  simp[EVERY_MEM]
QED

Theorem dfg_build_insts_rev_well_formed:
  !dfg insts.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_build_insts_rev dfg insts)
Proof
  Induct_on `insts` >> rw[dfg_build_insts_rev_def] >>
  first_x_assum match_mp_tac >>
  metis_tac[dfg_add_inst_well_formed]
QED

Theorem dfg_build_insts_well_formed:
  !insts. well_formed_dfg (dfg_build_insts insts)
Proof
  rw[dfg_build_insts_def, dfg_empty_def] >>
  match_mp_tac dfg_build_insts_rev_well_formed >>
  rw[well_formed_dfg_def, dfg_get_def_def, dfg_empty_def]
QED

Theorem dfg_build_function_well_formed:
  !fn. well_formed_dfg (dfg_build_function fn)
Proof
  rw[dfg_build_function_def, dfg_build_insts_well_formed]
QED

(* --------------------------------------------------------------------------
   Def-source correctness
   -------------------------------------------------------------------------- *)

Theorem dfg_add_defs_lookup:
  !dfg vs inst v inst'.
    dfg_get_def (dfg_add_defs dfg vs inst) v = SOME inst' ==>
    dfg_get_def dfg v = SOME inst' \/ (inst' = inst /\ MEM v vs)
Proof
  Induct_on `vs` >> rw[dfg_add_defs_def] >>
  first_x_assum (qspecl_then [`dfg with dfg_defs := dfg.dfg_defs |+ (h,inst)`,
                              `inst`, `v`, `inst'`] mp_tac) >>
  simp[dfg_get_def_def, FLOOKUP_UPDATE] >>
  Cases_on `h = v` >> fs[] >>
  metis_tac[]
QED

Theorem dfg_add_inst_get_def:
  !dfg inst0 v.
    dfg_get_def (dfg_add_inst dfg inst0) v =
    dfg_get_def
      (dfg_add_defs
         (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0)
         inst0.inst_outputs inst0) v
Proof
  rw[dfg_add_inst_def, dfg_get_def_def]
QED

Theorem dfg_add_inst_lookup:
  !dfg inst0 v inst.
    dfg_get_def (dfg_add_inst dfg inst0) v = SOME inst ==>
    dfg_get_def dfg v = SOME inst \/ (inst = inst0 /\ MEM v inst0.inst_outputs)
Proof
  metis_tac[dfg_add_inst_get_def, dfg_add_defs_lookup, dfg_add_uses_get_def]
QED

Theorem dfg_build_insts_rev_correct:
  !insts dfg v inst.
    dfg_get_def (dfg_build_insts_rev dfg insts) v = SOME inst ==>
    dfg_get_def dfg v = SOME inst \/
    (MEM inst insts /\ MEM v inst.inst_outputs)
Proof
  Induct_on `insts` >> rw[dfg_build_insts_rev_def] >>
  first_x_assum drule >>
  disch_then strip_assume_tac >- (
    drule dfg_add_inst_lookup >> simp[] >>
    strip_tac >> metis_tac[]
  ) >>
  metis_tac[]
QED

Theorem dfg_build_insts_correct:
  !insts v inst.
    dfg_get_def (dfg_build_insts insts) v = SOME inst ==>
    MEM inst insts /\ MEM v inst.inst_outputs
Proof
  rw[dfg_build_insts_def] >>
  drule (Q.SPECL [`REVERSE insts`, `dfg_empty`, `v`, `inst`] dfg_build_insts_rev_correct) >>
  simp[dfg_get_def_def, dfg_empty_def] >>
  metis_tac[MEM_REVERSE]
QED

Theorem dfg_build_function_correct:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst
    ==>
    MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)
Proof
  rw[dfg_build_function_def] >>
  drule dfg_build_insts_correct >>
  simp[]
QED

(* --------------------------------------------------------------------------
   Finiteness/termination helpers
   -------------------------------------------------------------------------- *)

Theorem dfg_def_ids_finite:
  !dfg. FINITE (dfg_def_ids dfg)
Proof
  rw[dfg_def_ids_def, IMAGE_FINITE, FINITE_FRANGE]
QED

Theorem dfg_get_def_implies_dfg_def_ids:
  !dfg v inst. dfg_get_def dfg v = SOME inst ==> inst.inst_id IN dfg_def_ids dfg
Proof
  metis_tac[dfg_def_ids_def, IN_IMAGE, IN_FRANGE_FLOOKUP, dfg_get_def_def]
QED

val _ = export_theory();
