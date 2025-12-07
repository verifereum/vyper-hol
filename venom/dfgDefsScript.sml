(*
 * Data-Flow Graph (DFG) Definitions
 *
 * This theory defines the DFG structure and basic operations.
 * The DFG maps each variable to the instruction that produces it.
 *
 * This is reusable infrastructure for multiple optimization passes.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - dfg                    : Type alias for the DFG map
 *   - build_dfg_fn           : Build DFG from a function
 *   - well_formed_dfg        : DFG well-formedness predicate
 *
 * TOP-LEVEL THEOREMS:
 *   - build_dfg_fn_well_formed   : DFG construction preserves well-formedness
 *   - build_dfg_fn_correct       : DFG correctly maps variables to instructions
 *
 * HELPER DEFINITIONS:
 *   - build_dfg_block, build_dfg_blocks : Inductive DFG construction
 *   - phi_var_operands, assign_var_operand, etc. : PHI/ASSIGN helpers
 *   - dfg_ids : Set of instruction IDs in DFG (for termination proofs)
 *
 * ============================================================================
 *)

Theory dfgDefs
Ancestors
  list finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   Data-Flow Graph Type and Basic Operations
   ========================================================================== *)

(* TOP-LEVEL: The DFG type - maps variable names to defining instructions *)
Type dfg = ``:(string, instruction) fmap``

(* TOP-LEVEL: DFG well-formedness - if a variable maps to an instruction,
   that instruction must produce the variable. This is a key invariant. *)
Definition well_formed_dfg_def:
  well_formed_dfg dfg <=>
    !v inst. FLOOKUP dfg v = SOME inst ==> inst.inst_output = SOME v
End

(* ==========================================================================
   Building the DFG from a Function
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
   ========================================================================== *)

(* Helper: Collect all instructions from a function *)
Definition fn_instructions_def:
  fn_instructions fn = FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)
End

(* Helper: SSA form predicate - each variable has at most one definition *)
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
   function and produces the variable. *)
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

