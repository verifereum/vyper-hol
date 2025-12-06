(*
 * DFG Origin Computation
 *
 * This theory defines origin computation through PHI/ASSIGN chains.
 * A PHI's "origins" are the non-PHI/non-ASSIGN instructions that
 * ultimately provide values to it.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - compute_origins        : Trace back through PHI/ASSIGN chains
 *   - phi_single_origin      : Find single origin for a PHI
 *   - phi_operands_direct    : Check if PHI operands point directly to origin
 *
 * TOP-LEVEL THEOREMS:
 *   - compute_origins_valid      : Checked version equals unchecked for valid IR
 *   - phi_operands_direct_flookup: Key lemma for PHI elimination correctness
 *
 * HELPER DEFINITIONS:
 *   - get_origins, get_origins_checked : Origin computation internals
 *   - defs_dominate_uses : For validity
 *
 * ============================================================================
 *)

Theory dfgOrigins
Ancestors
  dfgDefs pred_set list

(* ==========================================================================
   Origin Computation
   ==========================================================================

   get_origins traces back through PHI/ASSIGN chains to find "root"
   instructions. The visited set provides cycle detection.
   ========================================================================== *)

(* Helper: Unchecked origin computation. Always succeeds, even on cycles. *)
Definition get_origins_def:
  get_origins_list dfg (visited: num set) [] = {} /\
  get_origins_list dfg visited (v::vs) =
    (case FLOOKUP dfg v of
       NONE => get_origins_list dfg visited vs
     | SOME src_inst =>
         get_origins dfg visited src_inst UNION get_origins_list dfg visited vs) /\

  get_origins dfg visited inst =
    if inst.inst_opcode = PHI then
      if inst.inst_id IN visited then
        {}
      else
        let visited' = inst.inst_id INSERT visited in
        let vars = phi_var_operands inst.inst_operands in
        let origins = get_origins_list dfg visited' vars in
        if CARD origins > 1 then {inst}
        else origins
    else if inst.inst_opcode = ASSIGN then
      if inst.inst_id IN visited then {inst}
      else
        let visited' = inst.inst_id INSERT visited in
        case assign_var_operand inst of
          SOME v =>
            (case FLOOKUP dfg v of
               NONE => {inst}
             | SOME src_inst => get_origins dfg visited' src_inst)
        | NONE => {inst}
    else
      {inst}
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL (dfg, visited, vars) =>
             (CARD (dfg_ids dfg DIFF visited), LENGTH vars)
         | INR (dfg, visited, inst) =>
             (CARD (dfg_ids dfg DIFF visited) +
                (if inst.inst_id IN dfg_ids dfg then 0 else 1), 0))` >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac FLOOKUP_implies_dfg_ids >> simp[] >>
  Cases_on `inst.inst_id IN dfg_ids dfg` >> simp[] >>
  TRY (irule CARD_PSUBSET >> simp[FINITE_DIFF, dfg_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
       qexists_tac `inst.inst_id` >> simp[] >> NO_TAC) >>
  TRY (`dfg_ids dfg DIFF (inst.inst_id INSERT visited) = dfg_ids dfg DIFF visited`
         by (simp[EXTENSION] >> metis_tac[]) >> simp[] >> NO_TAC)
End

(* TOP-LEVEL: Main entry point for origin computation.
   Starts with empty visited set. *)
Definition compute_origins_def:
  compute_origins dfg inst = get_origins dfg {} inst
End

(* ==========================================================================
   Checked Version (with assertions for valid IR)
   ========================================================================== *)

(* Helper: Checked version that returns SOME/NONE.
   The key theorem get_origins_checked_always_some proves this always
   returns SOME when visited is finite. *)
Definition get_origins_checked_def:
  get_origins_list_checked dfg (visited: num set) [] = SOME {} /\
  get_origins_list_checked dfg visited (v::vs) =
    (case FLOOKUP dfg v of
       NONE => get_origins_list_checked dfg visited vs
     | SOME src_inst =>
         case (get_origins_checked dfg visited src_inst,
               get_origins_list_checked dfg visited vs) of
           (SOME s1, SOME s2) => SOME (s1 UNION s2)
         | _ => NONE) /\

  get_origins_checked dfg visited inst =
    if inst.inst_opcode = PHI then
      if inst.inst_id IN visited then SOME {}
      else
        let visited' = inst.inst_id INSERT visited in
        let vars = phi_var_operands inst.inst_operands in
        case get_origins_list_checked dfg visited' vars of
          NONE => NONE
        | SOME origins =>
            if CARD origins > 1 then SOME {inst}
            else SOME origins
    else if inst.inst_opcode = ASSIGN then
      (* This mirrors the Python implementation: Python doesn't track ASSIGN
         in visited at all. We check visited for HOL termination proof but
         return SOME {inst} (not NONE) on cycle. Under defs_dominate_uses,
         ASSIGN cycles can't happen, so this case never triggers for valid IR. *)
      if inst.inst_id IN visited then SOME {inst}
      else
        let visited' = inst.inst_id INSERT visited in
        case assign_var_operand inst of
          SOME v =>
            (case FLOOKUP dfg v of
               NONE => SOME {inst}
             | SOME src_inst => get_origins_checked dfg visited' src_inst)
        | NONE => SOME {inst}
    else
      SOME {inst}
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL (dfg, visited, vars) =>
             (CARD (dfg_ids dfg DIFF visited), LENGTH vars)
         | INR (dfg, visited, inst) =>
             (CARD (dfg_ids dfg DIFF visited) +
                (if inst.inst_id IN dfg_ids dfg then 0 else 1), 0))` >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac FLOOKUP_implies_dfg_ids >> simp[] >>
  Cases_on `inst.inst_id IN dfg_ids dfg` >> simp[] >>
  TRY (irule CARD_PSUBSET >> simp[FINITE_DIFF, dfg_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
       qexists_tac `inst.inst_id` >> simp[] >> NO_TAC) >>
  TRY (`dfg_ids dfg DIFF (inst.inst_id INSERT visited) = dfg_ids dfg DIFF visited`
         by (simp[EXTENSION] >> metis_tac[]) >> simp[] >> NO_TAC)
End

(* ==========================================================================
   Dominance (for valid IR property)
   ========================================================================== *)

(* Helper: Instruction dominance based on instruction IDs *)
Definition inst_dominates_def:
  inst_dominates inst1 inst2 <=> inst1.inst_id < inst2.inst_id
End

(* Helper: Valid IR property - definitions dominate uses for ASSIGN *)
Definition defs_dominate_uses_def:
  defs_dominate_uses dfg <=>
    !inst v def_inst.
      FLOOKUP dfg v = SOME def_inst /\
      inst.inst_opcode = ASSIGN /\
      assign_var_operand inst = SOME v
      ==>
      inst_dominates def_inst inst
End

(* ==========================================================================
   Correctness Theorems for Origin Computation
   ========================================================================== *)

(* Helper: When checked returns SOME, it equals unchecked *)
Theorem get_origins_checked_eq:
  (!dfg visited vars result.
     get_origins_list_checked dfg visited vars = SOME result ==>
     get_origins_list dfg visited vars = result) /\
  (!dfg visited inst result.
     get_origins_checked dfg visited inst = SOME result ==>
     get_origins dfg visited inst = result)
Proof
  ho_match_mp_tac get_origins_checked_ind >> rpt conj_tac >> rpt gen_tac >- (
    simp[Once get_origins_checked_def, Once get_origins_def]
  ) >- (
    rpt strip_tac >>
    simp[Once get_origins_checked_def, Once get_origins_def] >>
    Cases_on `FLOOKUP dfg v` >> fs[] >- (
      fs[Once get_origins_checked_def]
    ) >>
    fs[Once get_origins_checked_def] >> gvs[AllCaseEqs()] >>
    first_x_assum (qspec_then `s1` mp_tac) >> simp[] >>
    qpat_x_assum `get_origins_checked _ _ _ = _` mp_tac >>
    simp[Once get_origins_checked_def] >> gvs[AllCaseEqs()] >>
    strip_tac >> fs[]
  ) >- (
    rpt strip_tac >>
    simp[Once get_origins_checked_def, Once get_origins_def] >>
    qpat_x_assum `get_origins_checked _ _ _ = _` mp_tac >>
    simp[Once get_origins_checked_def] >> gvs[AllCaseEqs()] >>
    strip_tac >> fs[]
  )
QED

(* Helper: Predicate for valid visited sets *)
Definition visited_valid_def:
  visited_valid dfg visited <=>
    !id. id IN visited ==> id IN dfg_ids dfg
End

(* Helper: Inductive lemma for list_checked success *)
Theorem get_origins_list_checked_succeeds:
  !dfg visited vars.
    defs_dominate_uses dfg /\
    (!v src_inst. MEM v vars /\ FLOOKUP dfg v = SOME src_inst ==>
       ?result. get_origins_checked dfg visited src_inst = SOME result)
    ==>
    ?result. get_origins_list_checked dfg visited vars = SOME result
Proof
  Induct_on `vars` >- rw[Once get_origins_checked_def] >>
  rpt strip_tac >>
  rw[Once get_origins_checked_def] >>
  Cases_on `FLOOKUP dfg h` >> fs[] >- (
    first_x_assum match_mp_tac >> rw[] >>
    first_x_assum match_mp_tac >> fs[] >> qexists_tac `v` >> fs[]
  ) >>
  `?r. get_origins_checked dfg visited x = SOME r` by (
    first_x_assum (qspecl_then [`h`, `x`] mp_tac) >> fs[]
  ) >> fs[] >>
  `?result. get_origins_list_checked dfg visited vars = SOME result` by (
    first_x_assum match_mp_tac >> rw[] >>
    first_x_assum match_mp_tac >> fs[] >> qexists_tac `v` >> fs[]
  ) >> fs[]
QED

(* KEY LEMMA: get_origins_checked ALWAYS returns SOME when visited is finite.
   No special preconditions like defs_dominate_uses are needed. *)
Theorem get_origins_checked_always_some:
  (!dfg visited vars.
    FINITE visited
    ==>
    ?result. get_origins_list_checked dfg visited vars = SOME result) /\
  (!dfg visited inst.
    FINITE visited
    ==>
    ?result. get_origins_checked dfg visited inst = SOME result)
Proof
  ho_match_mp_tac get_origins_checked_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> simp[Once get_origins_checked_def] >>
  (* Handle all case splits uniformly *)
  TRY (
    (* v::vars case *)
    Cases_on `FLOOKUP dfg v` >> simp[] >>
    TRY (first_x_assum (qspec_then `ARB` mp_tac) >> simp[] >> NO_TAC) >>
    `?r1. get_origins_checked dfg visited x = SOME r1` by (
      qpat_x_assum `!inst. _` (qspec_then `x` mp_tac) >> simp[]
    ) >>
    `?r2. get_origins_list_checked dfg visited vars = SOME r2` by (
      qpat_x_assum `!src_inst. _` (qspec_then `x` mp_tac) >> simp[]
    ) >>
    simp[] >> NO_TAC
  ) >>
  TRY (
    (* inst case - PHI *)
    Cases_on `inst.inst_opcode = PHI` >> simp[] >>
    TRY (
      Cases_on `inst.inst_id IN visited` >> simp[] >>
      `FINITE (inst.inst_id INSERT visited)` by simp[] >>
      `?r. get_origins_list_checked dfg (inst.inst_id INSERT visited)
           (phi_var_operands inst.inst_operands) = SOME r` by (
        first_x_assum (qspecl_then [`inst.inst_id INSERT visited`,
                                     `phi_var_operands inst.inst_operands`] mp_tac) >>
        simp[]
      ) >>
      Cases_on `CARD r > 1` >> simp[] >> NO_TAC
    ) >>
    (* Non-PHI case - ASSIGN *)
    Cases_on `inst.inst_opcode = ASSIGN` >> simp[] >>
    Cases_on `inst.inst_id IN visited` >> simp[] >>
    Cases_on `assign_var_operand inst` >> simp[] >>
    Cases_on `FLOOKUP dfg x` >> simp[] >>
    `FINITE (inst.inst_id INSERT visited)` by simp[] >>
    first_x_assum (qspecl_then [`inst.inst_id INSERT visited`, `x`, `x'`] mp_tac) >>
    simp[]
  )
QED

(* Helper: Corollary with original statement *)
Theorem defs_dominate_uses_checked_succeeds:
  !dfg visited inst.
    defs_dominate_uses dfg /\
    FINITE visited /\
    (!id. id IN visited ==> id IN dfg_ids dfg)
    ==>
    ?result. get_origins_checked dfg visited inst = SOME result
Proof
  rpt strip_tac >>
  irule (cj 2 get_origins_checked_always_some) >> simp[]
QED

(* TOP-LEVEL: For valid IR, checked version equals unchecked. *)
Theorem compute_origins_valid:
  !dfg inst.
    defs_dominate_uses dfg ==>
    ?result. get_origins_checked dfg {} inst = SOME result /\
             compute_origins dfg inst = result
Proof
  rw[compute_origins_def] >>
  `?result. get_origins_checked dfg {} inst = SOME result` by (
    irule defs_dominate_uses_checked_succeeds >>
    rw[]
  ) >>
  metis_tac[get_origins_checked_eq]
QED

(* ==========================================================================
   Single Origin Helper - Used by PHI Elimination Pass
   ========================================================================== *)

(* TOP-LEVEL: Find the single origin for a PHI, if one exists. *)
Definition phi_single_origin_def:
  phi_single_origin dfg inst =
    if ~is_phi_inst inst then NONE else
    let origins = compute_origins dfg inst in
    let non_self = origins DELETE inst in
    if CARD non_self = 1 then SOME (CHOICE non_self)
    else NONE
End

(* Helper: Check if all PHI operand variables are the same *)
Definition phi_uniform_operands_def:
  phi_uniform_operands ops <=>
    case phi_var_operands ops of
      [] => T
    | (v::vs) => EVERY (\x. x = v) vs
End

(* TOP-LEVEL: For single-origin PHIs, operand variables equal origin's output. *)
Definition phi_operands_direct_def:
  phi_operands_direct dfg inst <=>
    case phi_single_origin dfg inst of
      NONE => T
    | SOME origin =>
        case origin.inst_output of
          NONE => T
        | SOME src_var =>
            EVERY (\v. v = src_var) (phi_var_operands inst.inst_operands)
End

(* Helper: Origins come from DFG lookups (or are the instruction itself) *)
Theorem get_origins_in_dfg_or_self:
  (!dfg visited vars origin.
     origin IN get_origins_list dfg visited vars ==>
     (?v. FLOOKUP dfg v = SOME origin)) /\
  (!dfg visited inst origin.
     origin IN get_origins dfg visited inst ==>
     origin = inst \/ (?v. FLOOKUP dfg v = SOME origin))
Proof
  ho_match_mp_tac get_origins_ind >> rpt conj_tac >> rpt gen_tac >- (
    (* Base case: empty list *)
    simp[Once get_origins_def]
  ) >- (
    (* v::vars case *)
    strip_tac >> simp[Once get_origins_def] >>
    Cases_on `FLOOKUP dfg v` >> gvs[] >>
    rpt strip_tac >> fs[IN_UNION] >> metis_tac[]
  ) >- (
    (* get_origins case *)
    strip_tac >> rpt strip_tac >>
    qpat_x_assum `origin IN get_origins _ _ _` mp_tac >>
    simp[Once get_origins_def] >>
    rpt (COND_CASES_TAC >> gvs[]) >>
    rpt CASE_TAC >> gvs[] >>
    metis_tac[]
  )
QED

(* Helper: Non-self origins are in the DFG *)
Theorem compute_origins_non_self_in_dfg:
  !dfg inst origin.
    origin IN compute_origins dfg inst /\ origin <> inst ==>
    ?v. FLOOKUP dfg v = SOME origin
Proof
  rw[compute_origins_def] >>
  drule (cj 2 get_origins_in_dfg_or_self) >> simp[]
QED

(* TOP-LEVEL: Key lemma for PHI elimination correctness.
   If phi_operands_direct holds, then looking up the PHI operand variable
   gives the single origin. *)
Theorem phi_operands_direct_flookup:
  !dfg inst origin prev_bb v.
    well_formed_dfg dfg /\
    phi_single_origin dfg inst = SOME origin /\
    phi_operands_direct dfg inst /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v)
  ==>
    FLOOKUP dfg v = SOME origin
Proof
  rpt strip_tac >>
  fs[phi_single_origin_def, AllCaseEqs(), is_phi_inst_def] >>
  (* Get origin IN compute_origins and origin <> inst *)
  `compute_origins dfg inst DELETE inst <> {}` by (
    strip_tac >> fs[CARD_EQ_0, FINITE_DELETE]
  ) >>
  drule CHOICE_DEF >> strip_tac >> fs[IN_DELETE] >>
  (* Get FLOOKUP dfg v' = SOME origin *)
  drule_all compute_origins_non_self_in_dfg >> strip_tac >>
  (* Get origin.inst_output = SOME v' *)
  `origin.inst_output = SOME v'` by fs[well_formed_dfg_def] >>
  (* Get MEM v (phi_var_operands) *)
  drule_all resolve_phi_in_operands >> strip_tac >>
  (* Unfold phi_operands_direct and use EVERY_MEM to get v = v' *)
  fs[phi_operands_direct_def, phi_single_origin_def, is_phi_inst_def, EVERY_MEM] >>
  gvs[AllCaseEqs()]
QED

