(*
 * PHI Elimination Transformation Definitions
 *
 * This theory defines the PHI elimination transformation.
 * The pass replaces PHI nodes that have a single origin with direct assignments.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - transform_inst       : Transform a single instruction
 *   - transform_block      : Transform a basic block
 *   - transform_function   : Transform an entire function
 *   - transform_context    : Transform a context (all functions)
 *
 * HELPER THEOREMS:
 *   - transform_block_label      : Label preservation
 *   - transform_block_length     : Length preservation
 *   - lookup_block_transform     : Lookup commutes with transform
 *   - transform_inst_non_phi     : Non-PHI instructions unchanged
 *   - transform_inst_preserves_terminator : Terminator status preserved
 *
 * ============================================================================
 *)

Theory phiTransform
Ancestors
  list finite_map pred_set
  venomState venomInst venomSem dfgDefs dfgOrigins

(* ==========================================================================
   PHI Elimination Transformation
   ========================================================================== *)

(* TOP-LEVEL: Transform a single instruction.
   If it's a PHI with single origin, replace with ASSIGN from origin's output. *)
Definition transform_inst_def:
  transform_inst dfg inst =
    case phi_single_origin dfg inst of
      SOME origin =>
        (case origin.inst_outputs of
           [src_var] =>
             inst with <|
               inst_opcode := ASSIGN;
               inst_operands := [Var src_var]
             |>
         | _ => inst)
    | NONE => inst
End

(* TOP-LEVEL: Transform a basic block by transforming all instructions *)
Definition transform_block_def:
  transform_block dfg bb =
    bb with bb_instructions := MAP (transform_inst dfg) bb.bb_instructions
End

(* TOP-LEVEL: Transform a function - builds DFG and transforms all blocks *)
Definition transform_function_def:
  transform_function fn =
    let dfg = dfg_build_function fn in
    fn with fn_blocks := MAP (transform_block dfg) fn.fn_blocks
End

(* TOP-LEVEL: Transform a context (all functions) - main entry point *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* ==========================================================================
   Transformation Properties - Helper Lemmas
   ========================================================================== *)

(* Helper: Transform preserves block label *)
Theorem transform_block_label:
  !dfg bb. (transform_block dfg bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def]
QED

Theorem transform_block_length:
  !dfg bb.
    LENGTH (transform_block dfg bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[transform_block_def, LENGTH_MAP]
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

(* Helper: Lookup commutes with transform *)
Theorem lookup_block_transform:
  !lbl blocks dfg.
    lookup_block lbl (MAP (transform_block dfg) blocks) =
    OPTION_MAP (transform_block dfg) (lookup_block lbl blocks)
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> simp[lookup_block_def, transform_block_label]
QED

Theorem lookup_block_MEM:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> MEM bb blocks
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> fs[] >>
  res_tac >> simp[]
QED

Theorem lookup_block_at_hd:
  !lbl blocks bb.
    blocks <> [] /\
    lbl = (HD blocks).bb_label /\
    lookup_block lbl blocks = SOME bb ==>
    bb = HD blocks
Proof
  Cases_on `blocks` >> simp[lookup_block_def]
QED

(* ==========================================================================
   Instruction Transform Properties
   ========================================================================== *)

Theorem transform_inst_identity:
  !dfg inst.
    phi_single_origin dfg inst = NONE ==>
    transform_inst dfg inst = inst
Proof
  rw[transform_inst_def]
QED

Theorem transform_inst_non_phi:
  !dfg inst.
    ~is_phi_inst inst ==>
    transform_inst dfg inst = inst
Proof
  rw[transform_inst_def, phi_single_origin_def]
QED

Theorem transform_inst_preserves_terminator:
  !dfg inst.
    is_terminator (transform_inst dfg inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[transform_inst_def] >>
  Cases_on `phi_single_origin dfg inst` >> simp[] >>
  Cases_on `x.inst_outputs` >> simp[is_terminator_def] >>
  Cases_on `t` >> simp[is_terminator_def] >>
  fs[phi_single_origin_def] >>
  Cases_on `is_phi_inst inst` >> fs[is_phi_inst_def, is_terminator_def]
QED

Theorem get_instruction_transform:
  !dfg bb idx x.
    get_instruction bb idx = SOME x ==>
    get_instruction (transform_block dfg bb) idx = SOME (transform_inst dfg x)
Proof
  rw[get_instruction_def, transform_block_def] >>
  simp[EL_MAP]
QED

(* If all instructions have no single origin, block transform is identity *)
Theorem transform_block_identity:
  !dfg bb.
    (!idx inst. get_instruction bb idx = SOME inst ==> phi_single_origin dfg inst = NONE) ==>
    (transform_block dfg bb).bb_instructions = bb.bb_instructions
Proof
  rw[transform_block_def] >>
  `MAP (transform_inst dfg) bb.bb_instructions = bb.bb_instructions` suffices_by simp[] >>
  irule listTheory.LIST_EQ >>
  simp[LENGTH_MAP, EL_MAP] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[get_instruction_def] >> strip_tac >>
  irule transform_inst_identity >> simp[]
QED

(* Running a block is the same when transform is identity *)
Theorem run_block_transform_identity:
  !bb s dfg.
    (!idx inst. get_instruction bb idx = SOME inst ==> phi_single_origin dfg inst = NONE) ==>
    run_block (transform_block dfg bb) s = run_block bb s
Proof
  rpt strip_tac >>
  (* Use transform_block_identity to show block is unchanged *)
  `transform_block dfg bb = bb` by (
    drule_all transform_block_identity >>
    simp[basic_block_component_equality, transform_block_def]
  ) >>
  simp[]
QED
