(*
 * DFG Analysis Correctness Proofs
 *
 * Internal proof machinery for DFG analysis.
 * Re-exported via dfgAnalysisPropsScript.sml.
 *)

Theory dfgCorrectnessProof
Ancestors
  dfgDefs list finite_map pred_set

(* --------------------------------------------------------------------------
   Well-formedness preservation
   -------------------------------------------------------------------------- *)

Theorem well_formed_dfg_update_proof:
  !dfg inst v.
    well_formed_dfg dfg /\ MEM v inst.inst_outputs
    ==> well_formed_dfg (dfg with dfg_defs := dfg.dfg_defs |+ (v, inst))
Proof
  rw[well_formed_dfg_def, dfg_get_def_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = v` >> fs[]
QED

Theorem dfg_add_defs_well_formed_proof:
  !dfg vs inst.
    well_formed_dfg dfg /\ EVERY (\v. MEM v inst.inst_outputs) vs
    ==> well_formed_dfg (dfg_add_defs dfg vs inst)
Proof
  Induct_on `vs` >> rw[dfg_add_defs_def] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    match_mp_tac well_formed_dfg_update_proof >>
    simp[]
  ) >>
  simp[]
QED

Theorem dfg_add_use_get_def_proof:
  !dfg v inst u.
    dfg_get_def (dfg_add_use dfg u inst) v = dfg_get_def dfg v
Proof
  rw[dfg_add_use_def, dfg_get_def_def]
QED

Theorem dfg_add_uses_get_def_proof:
  !dfg vs inst v.
    dfg_get_def (dfg_add_uses dfg vs inst) v = dfg_get_def dfg v
Proof
  Induct_on `vs` >> rw[dfg_add_uses_def] >>
  rw[dfg_add_use_get_def_proof]
QED

Theorem dfg_add_uses_preserve_wf_proof:
  !dfg vs inst.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_add_uses dfg vs inst)
Proof
  rw[well_formed_dfg_def] >>
  qpat_x_assum `dfg_get_def (dfg_add_uses dfg vs inst) v = SOME inst'` mp_tac >>
  simp[dfg_add_uses_get_def_proof] >>
  metis_tac[well_formed_dfg_def]
QED

Theorem well_formed_dfg_update_ids_proof:
  !dfg ids. well_formed_dfg dfg ==> well_formed_dfg (dfg with dfg_ids := ids)
Proof
  rw[well_formed_dfg_def, dfg_get_def_def]
QED

Theorem dfg_add_inst_well_formed_proof:
  !dfg inst.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_add_inst dfg inst)
Proof
  rw[dfg_add_inst_def] >>
  match_mp_tac well_formed_dfg_update_ids_proof >>
  match_mp_tac dfg_add_defs_well_formed_proof >>
  conj_tac >- (
    match_mp_tac dfg_add_uses_preserve_wf_proof >>
    simp[]
  ) >>
  simp[EVERY_MEM]
QED

Theorem dfg_build_insts_rev_well_formed_proof:
  !dfg insts.
    well_formed_dfg dfg ==> well_formed_dfg (dfg_build_insts_rev dfg insts)
Proof
  Induct_on `insts` >> rw[dfg_build_insts_rev_def] >>
  first_x_assum match_mp_tac >>
  metis_tac[dfg_add_inst_well_formed_proof]
QED

Theorem dfg_build_insts_well_formed_proof:
  !insts. well_formed_dfg (dfg_build_insts insts)
Proof
  rw[dfg_build_insts_def, dfg_empty_def] >>
  match_mp_tac dfg_build_insts_rev_well_formed_proof >>
  rw[well_formed_dfg_def, dfg_get_def_def, dfg_empty_def]
QED

Theorem dfg_build_function_well_formed_proof:
  !fn. well_formed_dfg (dfg_build_function fn)
Proof
  rw[dfg_build_function_def, dfg_build_insts_well_formed_proof]
QED

(* --------------------------------------------------------------------------
   Def-source correctness
   -------------------------------------------------------------------------- *)

Theorem dfg_add_defs_lookup_proof:
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

Theorem dfg_add_inst_get_def_proof:
  !dfg inst0 v.
    dfg_get_def (dfg_add_inst dfg inst0) v =
    dfg_get_def
      (dfg_add_defs
         (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0)
         inst0.inst_outputs inst0) v
Proof
  rw[dfg_add_inst_def, dfg_get_def_def]
QED

Theorem dfg_add_inst_lookup_proof:
  !dfg inst0 v inst.
    dfg_get_def (dfg_add_inst dfg inst0) v = SOME inst ==>
    dfg_get_def dfg v = SOME inst \/ (inst = inst0 /\ MEM v inst0.inst_outputs)
Proof
  metis_tac[dfg_add_inst_get_def_proof, dfg_add_defs_lookup_proof, dfg_add_uses_get_def_proof]
QED

Theorem dfg_build_insts_rev_correct_proof:
  !insts dfg v inst.
    dfg_get_def (dfg_build_insts_rev dfg insts) v = SOME inst ==>
    dfg_get_def dfg v = SOME inst \/
    (MEM inst insts /\ MEM v inst.inst_outputs)
Proof
  Induct_on `insts` >> rw[dfg_build_insts_rev_def] >>
  first_x_assum drule >>
  disch_then strip_assume_tac >- (
    drule dfg_add_inst_lookup_proof >> simp[] >>
    strip_tac >> metis_tac[]
  ) >>
  metis_tac[]
QED

Theorem dfg_build_insts_correct_proof:
  !insts v inst.
    dfg_get_def (dfg_build_insts insts) v = SOME inst ==>
    MEM inst insts /\ MEM v inst.inst_outputs
Proof
  rw[dfg_build_insts_def] >>
  drule (Q.SPECL [`REVERSE insts`, `dfg_empty`, `v`, `inst`] dfg_build_insts_rev_correct_proof) >>
  simp[dfg_get_def_def, dfg_empty_def] >>
  metis_tac[MEM_REVERSE]
QED

Theorem dfg_build_function_correct_proof:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst
    ==>
    MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)
Proof
  rw[dfg_build_function_def] >>
  drule dfg_build_insts_correct_proof >>
  simp[]
QED

(* --------------------------------------------------------------------------
   Finiteness/termination helpers
   -------------------------------------------------------------------------- *)

Theorem dfg_def_ids_finite_proof:
  !dfg. FINITE (dfg_def_ids dfg)
Proof
  rw[dfg_def_ids_def, IMAGE_FINITE, FINITE_FRANGE]
QED

Theorem dfg_get_def_implies_dfg_def_ids_proof:
  !dfg v inst. dfg_get_def dfg v = SOME inst ==> inst.inst_id IN dfg_def_ids dfg
Proof
  metis_tac[dfg_def_ids_def, IN_IMAGE, IN_FRANGE_FLOOKUP, dfg_get_def_def]
QED

(* --------------------------------------------------------------------------
   Uses correctness
   -------------------------------------------------------------------------- *)

(* If dfg_get_uses reports inst as a user of v, then inst is from the
   function and v appears among its operand variables. *)
Theorem dfg_build_function_uses_sound_proof:
  !fn v inst.
    MEM inst (dfg_get_uses (dfg_build_function fn) v) ==>
    MEM inst (fn_insts fn) /\ MEM v (operand_vars inst.inst_operands)
Proof
  cheat
QED

(* Every instruction in the function that mentions v as an operand
   variable appears in the uses list for v. *)
Theorem dfg_build_function_uses_complete_proof:
  !fn v inst.
    MEM inst (fn_insts fn) /\
    MEM v (operand_vars inst.inst_operands) ==>
    MEM inst (dfg_get_uses (dfg_build_function fn) v)
Proof
  cheat
QED

(* --------------------------------------------------------------------------
   Defs completeness
   -------------------------------------------------------------------------- *)

(* If any instruction in the function lists v as an output, then
   dfg_get_def returns some defining instruction for v. *)
Theorem dfg_build_function_defs_complete_proof:
  !fn v inst.
    MEM inst (fn_insts fn) /\
    MEM v inst.inst_outputs ==>
    ?inst'. dfg_get_def (dfg_build_function fn) v = SOME inst'
Proof
  cheat
QED

(* --------------------------------------------------------------------------
   ID map correctness
   -------------------------------------------------------------------------- *)

(* If dfg_get_inst_by_id returns an instruction, it is from the function. *)
Theorem dfg_build_function_ids_sound_proof:
  !fn id inst.
    dfg_get_inst_by_id (dfg_build_function fn) id = SOME inst ==>
    MEM inst (fn_insts fn)
Proof
  cheat
QED

(* Every instruction in the function is retrievable by its ID. *)
Theorem dfg_build_function_ids_complete_proof:
  !fn inst.
    MEM inst (fn_insts fn) ==>
    ?inst'. dfg_get_inst_by_id (dfg_build_function fn) inst.inst_id = SOME inst'
Proof
  cheat
QED

