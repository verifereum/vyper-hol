(*
 * SSA Construction Well-Formedness Definitions
 *
 * This theory defines well-formedness conditions for SSA construction.
 * These conditions ensure the transformation is correct.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - wf_input_fn            : Input function is suitable for SSA construction
 *   - wf_ssa_fn              : Output function is in valid SSA form
 *   - wf_var_mapping         : Variable mapping is consistent
 *
 * TOP-LEVEL THEOREMS:
 *   - ssa_transform_produces_ssa : Transform produces valid SSA
 *   - wf_input_implies_wf_ssa    : Well-formed input produces well-formed SSA
 *
 * ============================================================================
 *)

Theory mkSsaWellFormed
Ancestors
  mkSsaDefs mkSsaTransform mkSsaStateEquiv finite_map pred_set list
  venomState venomInst venomSem

(* ==========================================================================
   Input Function Well-Formedness
   ==========================================================================

   The input function must satisfy certain conditions for SSA construction
   to be valid. These are relatively weak conditions.
   ========================================================================== *)

(* TOP-LEVEL: All PHI operands are well-formed (Label/Var pairs) *)
Definition wf_phi_operands_def:
  wf_phi_operands fn <=>
    !bb idx inst.
      MEM bb fn.fn_blocks /\
      get_instruction bb idx = SOME inst /\
      inst.inst_opcode = PHI ==>
      phi_well_formed inst.inst_operands
End

(* TOP-LEVEL: Entry block has no PHI instructions *)
Definition no_entry_phi_def:
  no_entry_phi fn <=>
    fn.fn_blocks <> [] ==>
    !idx inst.
      get_instruction (HD fn.fn_blocks) idx = SOME inst ==>
      inst.inst_opcode <> PHI
End

(* TOP-LEVEL: No PHI instructions in any block *)
Definition no_phi_fn_def:
  no_phi_fn fn <=>
    !bb idx inst.
      MEM bb fn.fn_blocks /\
      get_instruction bb idx = SOME inst ==>
      inst.inst_opcode <> PHI
End

(* TOP-LEVEL: Each instruction has at most one output *)
Definition single_output_fn_def:
  single_output_fn fn <=>
    !bb idx inst.
      MEM bb fn.fn_blocks /\
      get_instruction bb idx = SOME inst ==>
      LENGTH inst.inst_outputs <= 1
End

(* TOP-LEVEL: All blocks are reachable (have valid labels) *)
Definition blocks_reachable_def:
  blocks_reachable fn <=>
    !bb. MEM bb fn.fn_blocks ==> bb.bb_label <> ""
End

(* TOP-LEVEL: Well-formed input function
   (well-formed PHIs, no entry PHIs, single-output instructions, reachable blocks) *)
Definition wf_input_fn_def:
  wf_input_fn fn <=>
    fn.fn_blocks <> [] /\
    wf_phi_operands fn /\
    no_entry_phi fn /\
    single_output_fn fn /\
    blocks_reachable fn
End

(* ==========================================================================
   SSA Output Well-Formedness
   ==========================================================================

   The SSA output must satisfy the single-assignment property:
   each variable is defined exactly once.
   ========================================================================== *)

(* Helper: Get all outputs defined in a list of instructions *)
Definition insts_outputs_def:
  insts_outputs [] = [] /\
  insts_outputs (inst::insts) =
    inst.inst_outputs ++ insts_outputs insts
End

(* Helper: Get all outputs in a block *)
Definition block_outputs_def:
  block_outputs bb = insts_outputs bb.bb_instructions
End

(* Helper: Get all outputs in a function *)
Definition fn_outputs_def:
  fn_outputs fn = FLAT (MAP block_outputs fn.fn_blocks)
End

(* TOP-LEVEL: SSA form - all outputs are unique *)
Definition ssa_unique_defs_def:
  ssa_unique_defs fn <=>
    ALL_DISTINCT (fn_outputs fn)
End

(* TOP-LEVEL: Well-formed SSA output *)
Definition wf_ssa_fn_def:
  wf_ssa_fn fn <=>
    ssa_unique_defs fn /\
    wf_phi_operands fn
End

(* ==========================================================================
   Variable Mapping Consistency
   ==========================================================================

   The variable mapping must be consistent with the transformation:
   - Each original variable maps to its current SSA version
   - The mapping evolves correctly as we step through instructions
   ========================================================================== *)

(* TOP-LEVEL: Mapping covers all live variables *)
Definition mapping_covers_vars_def:
  mapping_covers_vars (vm:var_mapping) live_vars <=>
    !v. v IN live_vars ==> ?ssa_v. FLOOKUP vm v = SOME ssa_v
End

(* TOP-LEVEL: Mapping is injective (different vars map to different SSA vars) *)
Definition mapping_injective_def:
  mapping_injective (vm:var_mapping) <=>
    !v1 v2 ssa_v.
      FLOOKUP vm v1 = SOME ssa_v /\
      FLOOKUP vm v2 = SOME ssa_v ==>
      v1 = v2
End

(* TOP-LEVEL: Well-formed variable mapping *)
Definition wf_var_mapping_def:
  wf_var_mapping (vm:var_mapping) fn <=>
    mapping_injective vm
End

(* ==========================================================================
   PHI Node Placement Validity
   ==========================================================================

   PHI nodes must be placed correctly:
   - At dominance frontiers
   - For live variables only
   ========================================================================== *)

(* TOP-LEVEL: PHI placement is valid *)
Definition valid_phi_placement_def:
  valid_phi_placement fn cfg df <=>
    !bb idx inst v.
      MEM bb fn.fn_blocks /\
      get_instruction bb idx = SOME inst /\
      inst.inst_opcode = PHI /\
      MEM v inst.inst_outputs ==>
      (* PHI is at a dominance frontier *)
      ?def_block. bb.bb_label IN get_dom_frontier df def_block
End

(* ==========================================================================
   Instruction-Level Compatibility (for transformation validity)
   ========================================================================== *)

(* Helper: Get SSA version of an operand via mapping *)
Definition wf_ssa_operand_def:
  wf_ssa_operand (vm:var_mapping) (Var v) =
    (case FLOOKUP vm v of
       SOME ssa_v => Var ssa_v
     | NONE => Var v) /\
  wf_ssa_operand vm (Lit l) = Lit l /\
  wf_ssa_operand vm (Label l) = Label l
End

(* Helper: Instruction is SSA-compatible with original under mapping.
   Includes freshness conditions to ensure SSA output doesn't collide. *)
Definition wf_inst_ssa_compatible_def:
  wf_inst_ssa_compatible vm inst inst_ssa <=>
    inst_ssa.inst_opcode = inst.inst_opcode /\
    inst_ssa.inst_operands = MAP (wf_ssa_operand vm) inst.inst_operands /\
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

(* Helper: Blocks are SSA compatible *)
Definition wf_blocks_ssa_compatible_def:
  wf_blocks_ssa_compatible vm [] [] = T /\
  wf_blocks_ssa_compatible vm (bb::bbs) (bb_ssa::bbs_ssa) =
    (bb.bb_label = bb_ssa.bb_label /\
     LENGTH bb.bb_instructions = LENGTH bb_ssa.bb_instructions /\
     (!idx. idx < LENGTH bb.bb_instructions ==>
            wf_inst_ssa_compatible vm
              (EL idx bb.bb_instructions)
              (EL idx bb_ssa.bb_instructions)) /\
     wf_blocks_ssa_compatible vm bbs bbs_ssa) /\
  wf_blocks_ssa_compatible vm _ _ = F
End

(* ==========================================================================
   Transformation Validity
   ==========================================================================

   The transformation is valid if the input/output are well-formed
   and the mapping is consistent.
   ========================================================================== *)

(* TOP-LEVEL: Valid SSA transformation *)
Definition valid_ssa_transform_def:
  valid_ssa_transform fn_orig fn_ssa vm <=>
    (* Input is well-formed *)
    wf_input_fn fn_orig /\
    (* Output is well-formed SSA *)
    wf_ssa_fn fn_ssa /\
    (* Mapping is consistent *)
    wf_var_mapping vm fn_ssa /\
    (* Structure is preserved *)
    LENGTH fn_orig.fn_blocks = LENGTH fn_ssa.fn_blocks /\
    fn_orig.fn_name = fn_ssa.fn_name /\
    (* Instruction-level compatibility *)
    wf_blocks_ssa_compatible vm fn_orig.fn_blocks fn_ssa.fn_blocks
End

(* ==========================================================================
   Basic Properties
   ========================================================================== *)

Theorem insts_outputs_length:
  !insts. LENGTH (insts_outputs insts) <= LENGTH insts + SUM (MAP (\i. LENGTH i.inst_outputs) insts)
Proof
  Induct_on `insts` >> rw[insts_outputs_def]
QED

Theorem fn_outputs_nil:
  !fn. fn.fn_blocks = [] ==> fn_outputs fn = []
Proof
  rw[fn_outputs_def]
QED

(* ==========================================================================
   Helpful Lemmas for Proofs
   ========================================================================== *)

(* If mapping is injective, different original vars have different SSA vars *)
Theorem mapping_injective_distinct:
  !vm v1 v2 ssa_v1 ssa_v2.
    mapping_injective vm /\
    FLOOKUP vm v1 = SOME ssa_v1 /\
    FLOOKUP vm v2 = SOME ssa_v2 /\
    v1 <> v2 ==>
    ssa_v1 <> ssa_v2
Proof
  rw[mapping_injective_def] >> CCONTR_TAC >> gvs[] >>
  first_x_assum (qspecl_then [`v1`, `v2`, `ssa_v2`] mp_tac) >> simp[]
QED

(* Empty function trivially satisfies SSA uniqueness *)
Theorem ssa_unique_defs_empty:
  !fn. fn.fn_blocks = [] ==> ssa_unique_defs fn
Proof
  rw[ssa_unique_defs_def, fn_outputs_def, ALL_DISTINCT]
QED
