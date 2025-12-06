(*
 * Data-Flow Graph (DFG) Analysis
 *
 * This theory defines the DFG structure and operations for Venom IR.
 * The DFG maps each variable to the instruction that produces it,
 * enabling analysis of def-use chains through PHI and ASSIGN instructions.
 *
 * This is reusable infrastructure for multiple optimization passes.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS (used by clients):
 *   - dfg                    : Type alias for the DFG map
 *   - build_dfg_fn           : Build DFG from a function
 *   - well_formed_dfg        : DFG well-formedness predicate
 *   - compute_origins        : Trace back through PHI/ASSIGN chains
 *   - phi_single_origin      : Find single origin for a PHI (main PHI elim API)
 *   - phi_operands_direct    : Check if PHI operands point directly to origin
 *
 * TOP-LEVEL THEOREMS (used by clients):
 *   - build_dfg_fn_well_formed   : DFG construction preserves well-formedness
 *   - build_dfg_fn_correct       : DFG correctly maps variables to instructions
 *   - compute_origins_valid      : Checked version equals unchecked for valid IR
 *   - phi_operands_direct_flookup: Key lemma for PHI elimination correctness
 *
 * HELPER DEFINITIONS (internal):
 *   - build_dfg_def, build_dfg_blocks_def : Inductive DFG construction
 *   - get_origins_def, get_origins_checked_def : Origin computation internals
 *   - phi_var_operands, assign_var_operand, etc. : PHI/ASSIGN helpers
 *   - dfg_ids, visited_valid, defs_dominate_uses : For termination/validity
 *
 * HELPER THEOREMS (internal):
 *   - Inductive well-formedness and correctness lemmas
 *   - get_origins_checked_always_some : Key totality lemma
 *   - Various lemmas for relating checked/unchecked versions
 *
 * ============================================================================
 *)

Theory venomDfg
Ancestors
  list finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   Data-Flow Graph Type and Basic Operations
   ==========================================================================

   TOP-LEVEL: These are the core type and predicates for DFG usage.
   ========================================================================== *)

(* TOP-LEVEL: The DFG type - maps variable names to defining instructions *)
Type dfg = ``:(string, instruction) fmap``

(* Helper: DFG lookup - thin wrapper around FLOOKUP *)
Definition dfg_lookup_def:
  dfg_lookup dfg v = FLOOKUP dfg v
End

(* TOP-LEVEL: DFG well-formedness - if a variable maps to an instruction,
   that instruction must produce the variable. This is a key invariant. *)
Definition well_formed_dfg_def:
  well_formed_dfg dfg <=>
    !v inst. FLOOKUP dfg v = SOME inst ==> inst.inst_output = SOME v
End

(* ==========================================================================
   Building the DFG from a Function
   ==========================================================================

   Helper definitions for inductive construction. The top-level entry point
   is build_dfg_fn which clients should use.
   ========================================================================== *)

(* Helper: Build DFG from a single basic block's instructions *)
Definition build_dfg_def:
  build_dfg_block dfg [] = dfg /\
  build_dfg_block dfg (inst::insts) =
    let dfg' = case inst.inst_output of
                 SOME v => dfg |+ (v, inst)
               | NONE => dfg
    in build_dfg_block dfg' insts
End

(* Helper: Build DFG from a list of basic blocks *)
Definition build_dfg_blocks_def:
  build_dfg_blocks dfg [] = dfg /\
  build_dfg_blocks dfg (bb::bbs) =
    build_dfg_blocks (build_dfg_block dfg bb.bb_instructions) bbs
End

(* TOP-LEVEL: Build the DFG for an entire function.
   This is the main entry point for DFG construction. *)
Definition build_dfg_fn_def:
  build_dfg_fn fn = build_dfg_blocks FEMPTY fn.fn_blocks
End

(* ==========================================================================
   Well-formedness Theorems
   ==========================================================================

   These theorems establish that DFG construction preserves well-formedness.
   build_dfg_fn_well_formed is the top-level result; others are helpers.
   ========================================================================== *)

(* Helper: Updating a well-formed DFG preserves well-formedness *)
Theorem well_formed_dfg_update:
  !dfg inst v.
    well_formed_dfg dfg /\ inst.inst_output = SOME v
    ==> well_formed_dfg (dfg |+ (v, inst))
Proof
  rw[well_formed_dfg_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = v` >> fs[]
QED

(* Helper: Block-level construction preserves well-formedness *)
Theorem build_dfg_block_well_formed:
  !dfg insts.
    well_formed_dfg dfg ==> well_formed_dfg (build_dfg_block dfg insts)
Proof
  Induct_on `insts` >>
  simp[build_dfg_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_output` >>
  simp[build_dfg_def] >>
  metis_tac[well_formed_dfg_update]
QED

(* Helper: Multi-block construction preserves well-formedness *)
Theorem build_dfg_blocks_well_formed:
  !dfg bbs.
    well_formed_dfg dfg ==> well_formed_dfg (build_dfg_blocks dfg bbs)
Proof
  Induct_on `bbs` >> rw[build_dfg_blocks_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `build_dfg_block dfg h.bb_instructions` mp_tac) >>
  impl_tac >- (match_mp_tac build_dfg_block_well_formed >> simp[]) >>
  simp[]
QED

(* TOP-LEVEL: The DFG built from any function is well-formed.
   This is used by PHI elimination to ensure FLOOKUP gives correct outputs. *)
Theorem build_dfg_fn_well_formed:
  !fn. well_formed_dfg (build_dfg_fn fn)
Proof
  simp[build_dfg_fn_def] >>
  match_mp_tac build_dfg_blocks_well_formed >>
  simp[well_formed_dfg_def, FLOOKUP_DEF]
QED

(* ==========================================================================
   DFG Correctness Theorems
   ==========================================================================

   These theorems establish that the DFG correctly maps variables to the
   instructions that define them. build_dfg_fn_correct is the top-level
   result; others are inductive helpers.
   ========================================================================== *)

(* Helper: Collect all instructions from a function (for correctness statements) *)
Definition fn_instructions_def:
  fn_instructions fn = FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)
End

(* Helper: SSA form predicate - each variable has at most one definition.
   Not directly used in main proofs, but documents an important invariant. *)
Definition ssa_form_def:
  ssa_form fn <=>
    !v inst1 inst2.
      MEM inst1 (fn_instructions fn) /\
      MEM inst2 (fn_instructions fn) /\
      inst1.inst_output = SOME v /\
      inst2.inst_output = SOME v
      ==>
      inst1 = inst2
End

(* Helper: Block-level DFG correctness *)
Theorem build_dfg_block_correct:
  !insts dfg v inst.
    FLOOKUP (build_dfg_block dfg insts) v = SOME inst ==>
    (FLOOKUP dfg v = SOME inst \/ (MEM inst insts /\ inst.inst_output = SOME v))
Proof
  Induct_on `insts` >> simp[build_dfg_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_output` >> fs[] >- (
    first_x_assum (qspecl_then [`dfg`, `v`, `inst`] mp_tac) >> simp[] >>
    strip_tac >> metis_tac[]
  ) >>
  first_x_assum (qspecl_then [`dfg |+ (x, h)`, `v`, `inst`] mp_tac) >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on `x = v` >> fs[] >>
  strip_tac >> metis_tac[]
QED

(* Helper: Multi-block DFG correctness *)
Theorem build_dfg_blocks_correct:
  !bbs dfg v inst.
    FLOOKUP (build_dfg_blocks dfg bbs) v = SOME inst ==>
    (FLOOKUP dfg v = SOME inst \/
     (?bb. MEM bb bbs /\ MEM inst bb.bb_instructions /\ inst.inst_output = SOME v))
Proof
  Induct_on `bbs` >> simp[build_dfg_blocks_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`build_dfg_block dfg h.bb_instructions`, `v`, `inst`] mp_tac) >>
  simp[] >> strip_tac >- (
    drule build_dfg_block_correct >> strip_tac >- fs[] >>
    disj2_tac >> qexists_tac `h` >> simp[]
  ) >>
  metis_tac[]
QED

(* TOP-LEVEL: If FLOOKUP returns an instruction, that instruction is in the
   function and produces the variable. This is used to establish that
   origins found via DFG traversal are actual instructions in the code. *)
Theorem build_dfg_fn_correct:
  !fn v inst.
    FLOOKUP (build_dfg_fn fn) v = SOME inst
    ==>
    inst.inst_output = SOME v /\
    MEM inst (fn_instructions fn)
Proof
  rw[build_dfg_fn_def, fn_instructions_def] >>
  drule build_dfg_blocks_correct >> fs[MEM_FLAT, MEM_MAP] >>
  strip_tac >> qexists_tac `bb.bb_instructions` >> simp[] >>
  qexists_tac `bb` >> simp[]
QED

(* ==========================================================================
   DFG IDs and Finiteness (for termination proofs)
   ==========================================================================

   These are internal helpers used to prove termination of get_origins.
   The key insight is that dfg_ids is finite, so the "unvisited" set
   decreases on each recursive call.
   ========================================================================== *)

(* Helper: Set of all instruction IDs in the DFG (for termination measure) *)
Definition dfg_ids_def:
  dfg_ids dfg = { inst.inst_id | ?v. FLOOKUP dfg v = SOME inst }
End

(* Helper: dfg_ids is always finite (enables CARD-based termination) *)
Theorem dfg_ids_finite:
  !dfg. FINITE (dfg_ids dfg)
Proof
  rw[dfg_ids_def] >>
  `{inst.inst_id | ?v. FLOOKUP dfg v = SOME inst} =
   IMAGE (\inst. inst.inst_id) (FRANGE dfg)` by (
    simp[EXTENSION, GSPECIFICATION, IN_FRANGE_FLOOKUP] >>
    metis_tac[]
  ) >>
  simp[IMAGE_FINITE, FINITE_FRANGE]
QED

(* Helper: FLOOKUP finding an instruction implies its ID is in dfg_ids *)
Theorem FLOOKUP_implies_dfg_ids:
  !dfg v inst. FLOOKUP dfg v = SOME inst ==> inst.inst_id IN dfg_ids dfg
Proof
  rw[dfg_ids_def, GSPECIFICATION] >> metis_tac[]
QED

(* ==========================================================================
   PHI Instruction Helpers
   ==========================================================================

   These are internal helpers for analyzing PHI and ASSIGN instructions.
   They extract operand information needed by get_origins and related
   functions.
   ========================================================================== *)

(* Helper: Extract variable names from PHI operands (Label,Var pairs) *)
Definition phi_var_operands_def:
  phi_var_operands [] = [] /\
  phi_var_operands [_] = [] /\
  phi_var_operands (Label lbl :: Var v :: rest) = v :: phi_var_operands rest /\
  phi_var_operands (_ :: _ :: rest) = phi_var_operands rest
End

(* Helper: Check if PHI operands are well-formed (Label,Var pairs) *)
Definition phi_well_formed_def:
  phi_well_formed [] = T /\
  phi_well_formed [_] = T /\
  phi_well_formed (Label lbl :: Var v :: rest) = phi_well_formed rest /\
  phi_well_formed (Label lbl :: _ :: rest) = F /\
  phi_well_formed (_ :: _ :: rest) = phi_well_formed rest
End

(* Helper: Extract variable from ASSIGN if operand is a single variable *)
Definition assign_var_operand_def:
  assign_var_operand inst =
    case inst.inst_operands of
      [Var v] => SOME v
    | _ => NONE
End

(* Helper: Check if instruction is a PHI *)
Definition is_phi_inst_def:
  is_phi_inst inst <=> inst.inst_opcode = PHI
End

(* Helper: Check if instruction is an assign with variable operand *)
Definition is_var_assign_def:
  is_var_assign inst <=>
    inst.inst_opcode = ASSIGN /\ IS_SOME (assign_var_operand inst)
End

(* Helper: Get source variables from an instruction for tracing *)
Definition inst_source_vars_def:
  inst_source_vars inst =
    if inst.inst_opcode = PHI then
      phi_var_operands inst.inst_operands
    else if inst.inst_opcode = ASSIGN then
      case assign_var_operand inst of
        SOME v => [v]
      | NONE => []
    else []
End

(* Helper: Get the set of unique variable names from PHI operands *)
Definition phi_operand_vars_def:
  phi_operand_vars ops = set (phi_var_operands ops)
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

(* ==========================================================================
   Origin Computation
   ==========================================================================

   These functions trace back through PHI/ASSIGN chains to find "root"
   instructions. A PHI's "origins" are the non-PHI/non-ASSIGN instructions
   that ultimately provide values to it.

   get_origins is the unchecked version that always succeeds.
   get_origins_checked is a checked version that returns NONE on errors.
   compute_origins is the TOP-LEVEL entry point that starts with empty visited.

   The visited set provides cycle detection and enables termination proof.
   ========================================================================== *)

(* Helper: Unchecked origin computation. Always succeeds, even on cycles.
   Returns the set of "root" instructions that provide values. *)
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
   Starts with empty visited set. Used by phi_single_origin. *)
Definition compute_origins_def:
  compute_origins dfg inst = get_origins dfg {} inst
End

(* ==========================================================================
   Checked Version (with assertions for valid IR)
   ==========================================================================

   This is an alternative version of get_origins that returns SOME/NONE
   instead of always succeeding. It mirrors the Python implementation.

   The key theorem get_origins_checked_always_some proves this always
   returns SOME when visited is finite - no special preconditions needed.
   ========================================================================== *)

(* Helper: Checked version of origin computation.
   Returns SOME result on success, NONE on error (though errors don't
   actually occur when visited is finite - see get_origins_checked_always_some). *)
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
   ==========================================================================

   These definitions capture valid IR properties. defs_dominate_uses says
   that for ASSIGN instructions, the definition must appear before the use.
   This prevents ASSIGN cycles in valid IR.
   ========================================================================== *)

(* Helper: Instruction dominance based on instruction IDs *)
Definition inst_dominates_def:
  inst_dominates inst1 inst2 <=> inst1.inst_id < inst2.inst_id
End

(* Helper: Valid IR property - definitions dominate uses for ASSIGN.
   This prevents cycles through ASSIGN instructions. *)
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
   ==========================================================================

   These theorems establish that the checked version equals the unchecked
   version when it succeeds, and that it always succeeds for valid IR.

   Key results:
   - get_origins_checked_eq: checked = unchecked when SOME
   - get_origins_checked_always_some: checked always returns SOME
   - compute_origins_valid: TOP-LEVEL - shows checked = unchecked
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

(* Helper: Predicate for valid visited sets (not used in main proofs) *)
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
   This is the central result that makes the checked version total.
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

(* Helper: Corollary with original statement (preconditions not actually needed) *)
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

(* TOP-LEVEL: For valid IR, checked version equals unchecked.
   This is the main result connecting the two implementations. *)
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
   ==========================================================================

   These are the TOP-LEVEL definitions used by the PHI elimination pass.
   phi_single_origin identifies PHIs that can be eliminated.
   phi_operands_direct is a well-formedness condition for elimination.
   ========================================================================== *)

(* TOP-LEVEL: Find the single origin for a PHI, if one exists.
   Returns SOME origin if the PHI has exactly one non-self origin.
   This is the main API for identifying eliminable PHIs. *)
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

(* TOP-LEVEL: For single-origin PHIs, operand variables equal origin's output.
   This is a well-formedness condition required for PHI elimination. *)
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
   gives the single origin. This is crucial for proving that the
   transformed code (using origin's value) equals the original. *)
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

