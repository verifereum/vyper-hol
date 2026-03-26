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

(* ==========================================================================
   Local helpers for uses/defs/ids correctness
   ========================================================================== *)

(* --- dfg_add_defs preserves uses and ids fields --- *)

Theorem dfg_add_defs_uses[local]:
  !vs dfg inst. (dfg_add_defs dfg vs inst).dfg_uses = dfg.dfg_uses
Proof
  Induct >> rw[dfg_add_defs_def]
QED

Theorem dfg_add_defs_ids[local]:
  !vs dfg inst. (dfg_add_defs dfg vs inst).dfg_ids = dfg.dfg_ids
Proof
  Induct >> rw[dfg_add_defs_def]
QED

(* --- dfg_add_use: soundness, preservation, introduction --- *)

Theorem dfg_add_use_sound[local]:
  !dfg v inst u w.
    MEM u (dfg_get_uses (dfg_add_use dfg v inst) w) ==>
    MEM u (dfg_get_uses dfg w) \/ (u = inst /\ w = v)
Proof
  rw[dfg_add_use_def, dfg_get_uses_def, LET_THM] >>
  Cases_on `MEM inst (dfg_get_uses dfg v)` >> fs[dfg_get_uses_def] >>
  Cases_on `w = v` >> fs[FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP dfg.dfg_uses v` >> fs[] >> metis_tac[]
QED

Theorem dfg_add_use_preserve[local]:
  !dfg v inst w u.
    MEM u (dfg_get_uses dfg w) ==>
    MEM u (dfg_get_uses (dfg_add_use dfg v inst) w)
Proof
  rw[dfg_add_use_def, dfg_get_uses_def, LET_THM] >>
  Cases_on `MEM inst (dfg_get_uses dfg v)` >> fs[dfg_get_uses_def] >>
  Cases_on `w = v` >> fs[FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP dfg.dfg_uses v` >> fs[]
QED

Theorem dfg_add_use_intro[local]:
  !dfg v inst. MEM inst (dfg_get_uses (dfg_add_use dfg v inst) v)
Proof
  rw[dfg_add_use_def, dfg_get_uses_def, LET_THM] >>
  Cases_on `MEM inst (dfg_get_uses dfg v)` >> fs[dfg_get_uses_def] >>
  Cases_on `FLOOKUP dfg.dfg_uses v` >> fs[FLOOKUP_UPDATE]
QED

(* --- dfg_add_uses: soundness, preservation, introduction --- *)

Theorem dfg_add_uses_sound[local]:
  !vs dfg inst u w.
    MEM u (dfg_get_uses (dfg_add_uses dfg vs inst) w) ==>
    MEM u (dfg_get_uses dfg w) \/ (u = inst /\ MEM w vs)
Proof
  Induct >> rw[dfg_add_uses_def] >>
  first_x_assum drule >> strip_tac >> fs[] >>
  drule dfg_add_use_sound >> metis_tac[]
QED

Theorem dfg_add_uses_preserve[local]:
  !vs dfg inst w u.
    MEM u (dfg_get_uses dfg w) ==>
    MEM u (dfg_get_uses (dfg_add_uses dfg vs inst) w)
Proof
  Induct >> rw[dfg_add_uses_def] >>
  first_x_assum match_mp_tac >>
  metis_tac[dfg_add_use_preserve]
QED

Theorem dfg_add_uses_intro[local]:
  !vs dfg inst w.
    MEM w vs ==> MEM inst (dfg_get_uses (dfg_add_uses dfg vs inst) w)
Proof
  Induct >> rw[dfg_add_uses_def]
  >- (irule dfg_add_uses_preserve >> metis_tac[dfg_add_use_intro])
  >- (first_x_assum match_mp_tac >> fs[])
QED

(* --- dfg_add_inst: uses soundness/completeness, ids --- *)

Theorem dfg_add_inst_uses_sound[local]:
  !dfg inst0 u w.
    MEM u (dfg_get_uses (dfg_add_inst dfg inst0) w) ==>
    MEM u (dfg_get_uses dfg w) \/
    (u = inst0 /\ MEM w (operand_vars inst0.inst_operands))
Proof
  rw[dfg_add_inst_def, LET_THM] >>
  `(dfg_add_defs (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0)
     inst0.inst_outputs inst0).dfg_uses =
   (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0).dfg_uses` by
    metis_tac[dfg_add_defs_uses] >>
  fs[dfg_get_uses_def] >>
  `MEM u (dfg_get_uses (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0) w)` by
    fs[dfg_get_uses_def] >>
  drule dfg_add_uses_sound >> fs[dfg_get_uses_def]
QED

Theorem dfg_add_inst_uses_preserve[local]:
  !dfg inst0 u w.
    MEM u (dfg_get_uses dfg w) ==>
    MEM u (dfg_get_uses (dfg_add_inst dfg inst0) w)
Proof
  rw[dfg_add_inst_def, LET_THM, dfg_get_uses_def] >>
  `(dfg_add_defs (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0)
     inst0.inst_outputs inst0).dfg_uses =
   (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0).dfg_uses` by
    metis_tac[dfg_add_defs_uses] >>
  fs[] >>
  `MEM u (dfg_get_uses (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0) w)` by
    (irule dfg_add_uses_preserve >> fs[dfg_get_uses_def]) >>
  fs[dfg_get_uses_def]
QED

Theorem dfg_add_inst_uses_intro[local]:
  !dfg inst0 w.
    MEM w (operand_vars inst0.inst_operands) ==>
    MEM inst0 (dfg_get_uses (dfg_add_inst dfg inst0) w)
Proof
  rw[dfg_add_inst_def, LET_THM, dfg_get_uses_def] >>
  `(dfg_add_defs (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0)
     inst0.inst_outputs inst0).dfg_uses =
   (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0).dfg_uses` by
    metis_tac[dfg_add_defs_uses] >>
  fs[] >>
  `MEM inst0 (dfg_get_uses (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0) w)` by
    (irule dfg_add_uses_intro >> fs[]) >>
  fs[dfg_get_uses_def]
QED

Theorem dfg_add_uses_ids[local]:
  !vs dfg inst. (dfg_add_uses dfg vs inst).dfg_ids = dfg.dfg_ids
Proof
  Induct >> rw[dfg_add_uses_def, dfg_add_use_def, LET_THM, dfg_get_uses_def] >>
  Cases_on `MEM inst (case FLOOKUP dfg.dfg_uses h of NONE => [] | SOME uses => uses)` >> fs[]
QED

Theorem dfg_add_inst_ids_sound[local]:
  !dfg inst0 id inst.
    dfg_get_inst_by_id (dfg_add_inst dfg inst0) id = SOME inst ==>
    dfg_get_inst_by_id dfg id = SOME inst \/
    (inst = inst0 /\ id = inst0.inst_id)
Proof
  rw[dfg_add_inst_def, LET_THM, dfg_get_inst_by_id_def] >>
  fs[dfg_add_defs_ids, dfg_add_uses_ids, FLOOKUP_UPDATE] >>
  Cases_on `id = inst0.inst_id` >> fs[]
QED

Theorem dfg_add_inst_ids_intro[local]:
  !dfg inst0.
    dfg_get_inst_by_id (dfg_add_inst dfg inst0) inst0.inst_id = SOME inst0
Proof
  rw[dfg_add_inst_def, LET_THM, dfg_get_inst_by_id_def] >>
  fs[dfg_add_defs_ids, dfg_add_uses_ids, FLOOKUP_UPDATE]
QED

Theorem dfg_add_inst_ids_preserve[local]:
  !dfg inst0 id inst.
    dfg_get_inst_by_id dfg id = SOME inst ==>
    dfg_get_inst_by_id (dfg_add_inst dfg inst0) id = SOME inst \/
    id = inst0.inst_id
Proof
  rw[dfg_add_inst_def, LET_THM, dfg_get_inst_by_id_def] >>
  fs[dfg_add_defs_ids, dfg_add_uses_ids, FLOOKUP_UPDATE] >>
  Cases_on `id = inst0.inst_id` >> fs[]
QED

(* --- dfg_add_defs completeness --- *)

Theorem dfg_add_defs_preserve[local]:
  !vs dfg inst v inst'.
    dfg_get_def dfg v = SOME inst' ==>
    ?inst''. dfg_get_def (dfg_add_defs dfg vs inst) v = SOME inst''
Proof
  Induct >> rw[dfg_add_defs_def] >>
  first_x_assum match_mp_tac >>
  rw[dfg_get_def_def, FLOOKUP_UPDATE] >>
  Cases_on `v = h` >> fs[dfg_get_def_def]
QED

Theorem dfg_add_defs_complete[local]:
  !vs dfg inst v.
    MEM v vs ==> ?inst'. dfg_get_def (dfg_add_defs dfg vs inst) v = SOME inst'
Proof
  Induct >> rw[dfg_add_defs_def]
  >- (irule dfg_add_defs_preserve >>
      rw[dfg_get_def_def, FLOOKUP_UPDATE])
  >- (first_x_assum drule >> metis_tac[])
QED

(* --------------------------------------------------------------------------
   build_insts_rev preservation and completeness lemmas
   Extracted as named local theorems to avoid inline re-proof.
   -------------------------------------------------------------------------- *)

Theorem build_insts_rev_uses_preserve[local]:
  !insts dfg u w.
    MEM u (dfg_get_uses dfg w) ==>
    MEM u (dfg_get_uses (dfg_build_insts_rev dfg insts) w)
Proof
  Induct >> rw[dfg_build_insts_rev_def] >>
  first_x_assum match_mp_tac >>
  metis_tac[dfg_add_inst_uses_preserve]
QED

Theorem build_insts_rev_uses_sound[local]:
  !insts dfg u w.
    MEM u (dfg_get_uses (dfg_build_insts_rev dfg insts) w) ==>
    MEM u (dfg_get_uses dfg w) \/
    (MEM u insts /\ MEM w (operand_vars u.inst_operands))
Proof
  Induct >> rw[dfg_build_insts_rev_def] >>
  first_x_assum drule >> strip_tac >> fs[] >>
  drule dfg_add_inst_uses_sound >> metis_tac[]
QED

Theorem build_insts_rev_uses_complete[local]:
  !insts dfg inst0 w.
    MEM inst0 insts /\ MEM w (operand_vars inst0.inst_operands) ==>
    MEM inst0 (dfg_get_uses (dfg_build_insts_rev dfg insts) w)
Proof
  Induct >> rw[dfg_build_insts_rev_def]
  >- (irule build_insts_rev_uses_preserve >>
      metis_tac[dfg_add_inst_uses_intro])
  >- (first_x_assum match_mp_tac >> fs[])
QED

Theorem dfg_add_inst_defs_preserve[local]:
  !dfg inst0 v inst'.
    dfg_get_def dfg v = SOME inst' ==>
    ?inst''. dfg_get_def (dfg_add_inst dfg inst0) v = SOME inst''
Proof
  rw[dfg_add_inst_def, LET_THM] >>
  `dfg_get_def (dfg_add_uses dfg (operand_vars inst0.inst_operands) inst0) v =
   SOME inst'` by metis_tac[dfg_add_uses_get_def_proof] >>
  drule dfg_add_defs_preserve >>
  rw[dfg_get_def_def]
QED

Theorem build_insts_rev_defs_preserve[local]:
  !insts dfg v inst'.
    dfg_get_def dfg v = SOME inst' ==>
    ?inst''. dfg_get_def (dfg_build_insts_rev dfg insts) v = SOME inst''
Proof
  Induct >> rw[dfg_build_insts_rev_def] >>
  first_x_assum match_mp_tac >>
  metis_tac[dfg_add_inst_defs_preserve]
QED

Theorem dfg_add_inst_defs_complete[local]:
  !dfg inst0 v.
    MEM v inst0.inst_outputs ==>
    ?inst'. dfg_get_def (dfg_add_inst dfg inst0) v = SOME inst'
Proof
  rw[dfg_add_inst_def, LET_THM, dfg_get_def_def] >>
  metis_tac[dfg_add_defs_complete, dfg_get_def_def]
QED

Theorem build_insts_rev_defs_complete[local]:
  !insts dfg inst0 v.
    MEM inst0 insts /\ MEM v inst0.inst_outputs ==>
    ?inst'. dfg_get_def (dfg_build_insts_rev dfg insts) v = SOME inst'
Proof
  Induct >> rw[dfg_build_insts_rev_def]
  >- (irule build_insts_rev_defs_preserve >>
      metis_tac[dfg_add_inst_defs_complete])
  >- metis_tac[]
QED

Theorem build_insts_rev_ids_sound[local]:
  !insts dfg id inst.
    dfg_get_inst_by_id (dfg_build_insts_rev dfg insts) id = SOME inst ==>
    dfg_get_inst_by_id dfg id = SOME inst \/ MEM inst insts
Proof
  Induct >> rw[dfg_build_insts_rev_def] >>
  first_x_assum drule >> strip_tac >> fs[] >>
  drule dfg_add_inst_ids_sound >> metis_tac[]
QED

Theorem build_insts_rev_ids_preserve[local]:
  !insts dfg id inst.
    dfg_get_inst_by_id dfg id = SOME inst ==>
    ?inst'. dfg_get_inst_by_id (dfg_build_insts_rev dfg insts) id = SOME inst'
Proof
  Induct >> rw[dfg_build_insts_rev_def] >>
  first_x_assum match_mp_tac >>
  drule dfg_add_inst_ids_preserve >> strip_tac >> fs[] >>
  metis_tac[dfg_add_inst_ids_intro]
QED

Theorem build_insts_rev_ids_complete[local]:
  !insts dfg inst0.
    MEM inst0 insts ==>
    ?inst'. dfg_get_inst_by_id (dfg_build_insts_rev dfg insts) inst0.inst_id = SOME inst'
Proof
  Induct >> rw[dfg_build_insts_rev_def]
  >- (irule build_insts_rev_ids_preserve >> metis_tac[dfg_add_inst_ids_intro])
  >- (first_x_assum drule >> metis_tac[])
QED

(* --------------------------------------------------------------------------
   Main correctness theorems (uses, defs, ids)
   All follow: unfold build_function → drule build_insts_rev lemma → MEM_REVERSE
   -------------------------------------------------------------------------- *)

Theorem dfg_build_function_uses_sound_proof:
  !fn v inst.
    MEM inst (dfg_get_uses (dfg_build_function fn) v) ==>
    MEM inst (fn_insts fn) /\ MEM v (operand_vars inst.inst_operands)
Proof
  rw[dfg_build_function_def, dfg_build_insts_def] >>
  drule build_insts_rev_uses_sound >>
  simp[dfg_get_uses_def, dfg_empty_def] >>
  metis_tac[MEM_REVERSE]
QED

Theorem dfg_build_function_uses_complete_proof:
  !fn v inst.
    MEM inst (fn_insts fn) /\
    MEM v (operand_vars inst.inst_operands) ==>
    MEM inst (dfg_get_uses (dfg_build_function fn) v)
Proof
  rw[dfg_build_function_def, dfg_build_insts_def] >>
  irule build_insts_rev_uses_complete >> simp[MEM_REVERSE]
QED

Theorem dfg_build_function_defs_complete_proof:
  !fn v inst.
    MEM inst (fn_insts fn) /\
    MEM v inst.inst_outputs ==>
    ?inst'. dfg_get_def (dfg_build_function fn) v = SOME inst'
Proof
  rw[dfg_build_function_def, dfg_build_insts_def] >>
  irule build_insts_rev_defs_complete >>
  qexists_tac `inst` >> simp[MEM_REVERSE]
QED

Theorem dfg_build_function_ids_sound_proof:
  !fn id inst.
    dfg_get_inst_by_id (dfg_build_function fn) id = SOME inst ==>
    MEM inst (fn_insts fn)
Proof
  rw[dfg_build_function_def, dfg_build_insts_def] >>
  drule build_insts_rev_ids_sound >>
  simp[dfg_get_inst_by_id_def, dfg_empty_def] >>
  metis_tac[MEM_REVERSE]
QED

Theorem dfg_build_function_ids_complete_proof:
  !fn inst.
    MEM inst (fn_insts fn) ==>
    ?inst'. dfg_get_inst_by_id (dfg_build_function fn) inst.inst_id = SOME inst'
Proof
  rw[dfg_build_function_def, dfg_build_insts_def] >>
  irule build_insts_rev_ids_complete >> simp[MEM_REVERSE]
QED


(* --------------------------------------------------------------------------
   normalize_operand preserves eval_operand
   -------------------------------------------------------------------------- *)

open venomStateTheory

(* Semantic DFG well-formedness: for every variable defined by an ASSIGN
   instruction in the DFG, the variable's value equals the ASSIGN source's
   value. This holds at any program point where all preceding ASSIGNs
   have been executed (i.e., within the same basic block after the
   defining instruction, or in any dominated block in SSA form). *)
Definition dfg_assigns_sound_def:
  dfg_assigns_sound dfg s <=>
    !v inst. FLOOKUP dfg.dfg_defs v = SOME inst /\
             inst.inst_opcode = ASSIGN ==>
      case inst.inst_operands of
        [op] => lookup_var v s = eval_operand op s
      | _ => T
End

(* normalize_operand preserves eval_operand under DFG soundness.
   Key infrastructure: enables connecting lattice-tracked values
   (which use normalized operands) to actual runtime values. *)
Theorem normalize_operand_eval_proof:
  !dfg visited op s.
    dfg_assigns_sound dfg s ==>
    eval_operand (normalize_operand dfg visited op) s = eval_operand op s
Proof
  ho_match_mp_tac normalize_operand_ind >>
  rpt conj_tac
  >- (
    (* Case: Var v *)
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    simp[Once normalize_operand_def] >>
    IF_CASES_TAC >> simp[] >>
    Cases_on `FLOOKUP dfg.dfg_defs dfg'` >> simp[] >>
    rename1 `FLOOKUP _ _ = SOME inst` >>
    IF_CASES_TAC >> simp[] >>
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    rename1 `inst.inst_operands = [src_op]` >>
    (* Apply IH *)
    first_x_assum (qspecl_then [`inst`, `src_op`, `[]`] mp_tac) >>
    simp[] >> disch_then (qspec_then `s` mp_tac) >> simp[] >>
    strip_tac >>
    (* dfg_assigns_sound gives: lookup_var dfg' s = eval_operand src_op s *)
    fs[dfg_assigns_sound_def] >>
    first_x_assum (qspecl_then [`dfg'`, `inst`] mp_tac) >>
    simp[eval_operand_def]
  )
  >- simp[normalize_operand_def, eval_operand_def]
  >- simp[normalize_operand_def, eval_operand_def]
QED
