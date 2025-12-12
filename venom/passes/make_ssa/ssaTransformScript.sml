(*
 * SSA Construction Transformation Definitions
 *
 * This theory defines the SSA construction transformation.
 * The pass converts non-SSA IR to SSA form by:
 * 1. Adding PHI nodes at dominance frontiers
 * 2. Renaming variables with version numbers
 * 3. Removing degenerate PHIs
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - rename_operand         : Rename operand using current SSA name
 *   - rename_operands        : Rename list of operands
 *   - rename_inst_uses       : Rename uses in an instruction
 *   - rename_inst_def        : Rename definition in an instruction
 *   - transform_inst         : Full instruction transformation
 *   - transform_block        : Transform a basic block
 *   - transform_function     : Transform an entire function
 *
 * HELPER DEFINITIONS:
 *   - update_phi_operand     : Update PHI operand for a specific predecessor
 *   - collect_defs           : Collect variable definitions
 *
 * ============================================================================
 *)

Theory ssaTransform
Ancestors
  ssaDefs list finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   Operand Renaming
   ==========================================================================

   In SSA construction, variable uses are renamed to the current SSA version.
   Literals and labels are unchanged.
   ========================================================================== *)

(* TOP-LEVEL: Rename a single operand using the name stack *)
Definition rename_operand_def:
  rename_operand ns (Var v) = Var (ssa_var_name v (stack_top ns v)) /\
  rename_operand ns (Lit l) = Lit l /\
  rename_operand ns (Label l) = Label l
End

(* TOP-LEVEL: Rename a list of operands *)
Definition rename_operands_def:
  rename_operands ns [] = [] /\
  rename_operands ns (op::ops) = rename_operand ns op :: rename_operands ns ops
End

(* ==========================================================================
   Instruction Transformation
   ==========================================================================

   Each instruction is transformed in two phases:
   1. Rename uses (operands) - use current version from stack
   2. Rename definition (output) - generate new version, push to stack
   ========================================================================== *)

(* TOP-LEVEL: Rename uses in an instruction (operands).
   PHI nodes are special - their operands are renamed per-predecessor. *)
Definition rename_inst_uses_def:
  rename_inst_uses ns inst =
    if inst.inst_opcode = PHI then inst  (* PHI operands handled separately *)
    else inst with inst_operands := rename_operands ns inst.inst_operands
End

(* TOP-LEVEL: Rename definition in an instruction.
   Returns (transformed instruction, updated name stack, updated counter).
   For simplicity, we handle only single-output instructions here. *)
Definition rename_inst_def_def:
  rename_inst_def ns counter inst =
    case inst.inst_outputs of
      [] => (inst, ns, counter)
    | [out] =>
        let base = base_var_name out in
        let version = case FLOOKUP counter base of SOME n => n | NONE => 0 in
        let new_name = ssa_var_name base version in
        let ns' = stack_push ns base version in
        let counter' = counter |+ (base, version + 1) in
        (inst with inst_outputs := [new_name], ns', counter')
    | _ => (inst, ns, counter)  (* Multi-output not yet supported *)
End

(* TOP-LEVEL: Transform an instruction - rename both uses and definition.
   Returns (transformed instruction, updated name stack, updated counter). *)
Definition transform_inst_def:
  transform_inst ns counter inst =
    let inst' = rename_inst_uses ns inst in
    rename_inst_def ns counter inst'
End

(* ==========================================================================
   PHI Node Operand Update
   ==========================================================================

   PHI node operands are updated when processing successor blocks.
   Each predecessor's version of the variable is captured.
   ========================================================================== *)

(* Helper: Find and update the operand for a specific predecessor in PHI *)
Definition update_phi_for_pred_def:
  update_phi_for_pred pred_label ns [] = [] /\
  update_phi_for_pred pred_label ns [op] = [op] /\
  update_phi_for_pred pred_label ns (Label lbl :: Var v :: rest) =
    (if lbl = pred_label then
       Label lbl :: rename_operand ns (Var v) :: rest
     else
       Label lbl :: Var v :: update_phi_for_pred pred_label ns rest) /\
  update_phi_for_pred pred_label ns (op1 :: op2 :: rest) =
    op1 :: op2 :: update_phi_for_pred pred_label ns rest
End

(* TOP-LEVEL: Update PHI instruction for a specific predecessor *)
Definition update_phi_inst_def:
  update_phi_inst pred_label ns inst =
    if inst.inst_opcode = PHI then
      inst with inst_operands := update_phi_for_pred pred_label ns inst.inst_operands
    else
      inst
End

(* Update all PHIs in a block for a specific predecessor *)
Definition update_phis_in_block_def:
  update_phis_in_block pred_label ns bb =
    bb with bb_instructions := MAP (update_phi_inst pred_label ns) bb.bb_instructions
End

(* ==========================================================================
   Block Transformation
   ==========================================================================

   Transform a basic block by:
   1. Processing instructions in order, renaming uses and definitions
   2. Update PHI operands in successor blocks
   ========================================================================== *)

(* Helper: Transform instructions in a block *)
Definition transform_insts_def:
  transform_insts ns counter [] = ([], ns, counter) /\
  transform_insts ns counter (inst::insts) =
    let (inst', ns', counter') = transform_inst ns counter inst in
    let (insts', ns'', counter'') = transform_insts ns' counter' insts in
    (inst'::insts', ns'', counter'')
End

(* TOP-LEVEL: Transform a basic block.
   Returns (transformed block, final name stack, final counter). *)
Definition transform_block_def:
  transform_block ns counter bb =
    let (insts', ns', counter') = transform_insts ns counter bb.bb_instructions in
    (bb with bb_instructions := insts', ns', counter')
End

(* ==========================================================================
   Collecting Variable Definitions
   ==========================================================================

   Before SSA construction, we collect where each variable is defined.
   This is used for placing PHI nodes.
   ========================================================================== *)

(* Helper: Collect definitions from an instruction *)
Definition collect_inst_defs_def:
  collect_inst_defs bb_label idx inst dm =
    case inst.inst_outputs of
      [] => dm
    | [v] => add_def dm v bb_label idx
    | _ => dm  (* Multi-output not yet handled *)
End

(* Helper: Collect definitions from instructions *)
Definition collect_insts_defs_def:
  collect_insts_defs bb_label idx [] dm = dm /\
  collect_insts_defs bb_label idx (inst::insts) dm =
    let dm' = collect_inst_defs bb_label idx inst dm in
    collect_insts_defs bb_label (idx + 1) insts dm'
End

(* Helper: Collect definitions from a block *)
Definition collect_block_defs_def:
  collect_block_defs bb dm = collect_insts_defs bb.bb_label 0 bb.bb_instructions dm
End

(* TOP-LEVEL: Collect all definitions in a function *)
Definition collect_fn_defs_def:
  collect_fn_defs [] dm = dm /\
  collect_fn_defs (bb::bbs) dm =
    collect_fn_defs bbs (collect_block_defs bb dm)
End

(* ==========================================================================
   PHI Node Placement
   ==========================================================================

   PHI nodes are placed at dominance frontiers of definition points.
   ========================================================================== *)

(* TOP-LEVEL: Type for dominance frontier mapping *)
Type dom_frontier = ``:(string, string set) fmap``

(* Helper: Get dominance frontier for a block *)
Definition get_dom_frontier_def:
  get_dom_frontier (df:dom_frontier) lbl =
    case FLOOKUP df lbl of
      SOME s => s
    | NONE => {}
End

(* Helper: Place PHI at a block for a variable *)
Definition place_phi_at_block_def:
  place_phi_at_block next_id var preds bb =
    let phi = mk_phi_inst next_id var preds var in
    (bb with bb_instructions := phi :: bb.bb_instructions, next_id + 1)
End

(* ==========================================================================
   Degenerate PHI Removal
   ==========================================================================

   After renaming, some PHIs become degenerate:
   - All operands are the same variable
   - Only one operand remains after removing self-references
   These can be removed or converted to assigns.
   ========================================================================== *)

(* Helper: Get unique operand values from PHI (excluding self-references) *)
Definition phi_unique_values_def:
  phi_unique_values out [] acc = acc /\
  phi_unique_values out [_] acc = acc /\
  phi_unique_values out (Label lbl :: Var v :: rest) acc =
    (if v = out then phi_unique_values out rest acc
     else phi_unique_values out rest (v INSERT acc)) /\
  phi_unique_values out (_ :: _ :: rest) acc = phi_unique_values out rest acc
End

(* TOP-LEVEL: Check if a PHI is degenerate (has single unique source) *)
Definition is_degenerate_phi_def:
  is_degenerate_phi inst =
    if inst.inst_opcode <> PHI then F
    else
      case inst.inst_outputs of
        [] => F
      | [out] =>
          CARD (phi_unique_values out inst.inst_operands {}) <= 1
      | _ => F
End

(* TOP-LEVEL: Remove or simplify degenerate PHI *)
Definition simplify_phi_def:
  simplify_phi inst =
    if ~is_degenerate_phi inst then SOME inst
    else
      case inst.inst_outputs of
        [] => NONE
      | [out] =>
          let vals = phi_unique_values out inst.inst_operands {} in
          if vals = {} then NONE  (* All self-references - remove *)
          else
            (* Single source - convert to ASSIGN *)
            let src = CHOICE vals in
            SOME (inst with <| inst_opcode := ASSIGN;
                              inst_operands := [Var src] |>)
      | _ => SOME inst
End

(* Helper: filter_map - apply f to each element, keep SOME results *)
Definition filter_map_def:
  filter_map f [] = [] /\
  filter_map f (x::xs) =
    case f x of
      SOME y => y :: filter_map f xs
    | NONE => filter_map f xs
End

(* TOP-LEVEL: Remove degenerate PHIs from a block *)
Definition remove_degenerate_phis_def:
  remove_degenerate_phis bb =
    bb with bb_instructions :=
      filter_map simplify_phi bb.bb_instructions
End

(* ==========================================================================
   Full Function Transformation
   ========================================================================== *)

(* Note: The full transformation requires:
   1. CFG analysis (predecessors/successors)
   2. Dominator tree analysis
   3. Dominance frontier computation
   4. Liveness analysis

   For the HOL4 proof, we model this abstractly by parameterizing
   over these analyses. The key correctness property is that the
   transformation preserves semantics. *)

(* TOP-LEVEL: Abstract transformation result type *)
Datatype:
  ssa_result = <|
    ssr_function : ir_function;
    ssr_var_map : (string, string) fmap  (* original -> SSA name *)
  |>
End

(* ==========================================================================
   Transformation Properties
   ========================================================================== *)

Theorem rename_operands_length:
  !ns ops. LENGTH (rename_operands ns ops) = LENGTH ops
Proof
  Induct_on `ops` >> rw[rename_operands_def]
QED

Theorem transform_insts_length:
  !ns counter insts insts' ns' counter'.
    transform_insts ns counter insts = (insts', ns', counter') ==>
    LENGTH insts' = LENGTH insts
Proof
  Induct_on `insts` >> rw[transform_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem transform_block_length:
  !ns counter bb bb' ns' counter'.
    transform_block ns counter bb = (bb', ns', counter') ==>
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[transform_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule transform_insts_length >> simp[]
QED

Theorem transform_block_label:
  !ns counter bb bb' ns' counter'.
    transform_block ns counter bb = (bb', ns', counter') ==>
    bb'.bb_label = bb.bb_label
Proof
  rw[transform_block_def, LET_THM] >> pairarg_tac >> gvs[]
QED

