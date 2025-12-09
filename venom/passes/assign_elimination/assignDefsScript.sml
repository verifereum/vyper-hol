(*
 * ASSIGN Elimination Definitions
 *
 * This theory defines the ASSIGN elimination transformation.
 * The pass eliminates redundant ASSIGN instructions by replacing
 * uses of the output variable with the source variable.
 *
 * For %y = ASSIGN [Var %x], replace all uses of %y with %x,
 * then transform the ASSIGN to NOP.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - assign_var_source        : Extract source variable from ASSIGN
 *   - is_eliminable_assign     : Check if ASSIGN can be eliminated
 *   - build_assign_map         : Build map from eliminated vars to sources
 *   - replace_var              : Replace variable using map
 *   - transform_inst           : Transform a single instruction
 *   - transform_block          : Transform a basic block
 *   - transform_function       : Transform an entire function
 *
 * ============================================================================
 *)

Theory assignDefs
Ancestors
  list finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   ASSIGN Variable Source Extraction
   ========================================================================== *)

(* Helper: Check if instruction is an ASSIGN *)
Definition is_assign_inst_def:
  is_assign_inst inst <=> inst.inst_opcode = ASSIGN
End

(* Helper: Extract source variable from ASSIGN if operand is a single variable.
   Returns NONE if operand is a literal or not a single-operand ASSIGN. *)
Definition assign_var_source_def:
  assign_var_source inst =
    if inst.inst_opcode <> ASSIGN then NONE else
    case (inst.inst_operands, inst.inst_outputs) of
      ([Var src], [out]) => SOME (out, src)
    | _ => NONE
End

(* Helper: Check if ASSIGN can be eliminated (source is a variable) *)
Definition is_eliminable_assign_def:
  is_eliminable_assign inst = IS_SOME (assign_var_source inst)
End

(* ==========================================================================
   Building the Variable Replacement Map
   ========================================================================== *)

(* Build map from output variables to source variables for eliminable ASSIGNs.
   Map type: string |-> string (output_var -> source_var) *)
Definition build_assign_map_def:
  build_assign_map_block amap [] = amap /\
  build_assign_map_block amap (inst::insts) =
    let amap' = case assign_var_source inst of
                  SOME (out, src) => amap |+ (out, src)
                | NONE => amap
    in build_assign_map_block amap' insts
End

Definition build_assign_map_blocks_def:
  build_assign_map_blocks amap [] = amap /\
  build_assign_map_blocks amap (bb::bbs) =
    build_assign_map_blocks (build_assign_map_block amap bb.bb_instructions) bbs
End

(* TOP-LEVEL: Build the assign map for an entire function *)
Definition build_assign_map_fn_def:
  build_assign_map_fn fn = build_assign_map_blocks FEMPTY fn.fn_blocks
End

(* ==========================================================================
   Variable Replacement
   ========================================================================== *)

(* Replace a variable using the map, resolving chains.
   E.g., if %y -> %x and %x -> %z, then replace_var "%y" gives "%z".
   Uses fuel for termination (chain length bounded by map size). *)
Definition resolve_var_def:
  resolve_var amap fuel v =
    case fuel of
      0 => v
    | SUC fuel' =>
        case FLOOKUP amap v of
          NONE => v
        | SOME src => resolve_var amap fuel' src
End

(* Wrapper with fuel = map size + 1 (sufficient for any chain) *)
Definition replace_var_def:
  replace_var amap v = resolve_var amap (CARD (FDOM amap) + 1) v
End

(* Replace variables in an operand *)
Definition replace_operand_def:
  replace_operand amap (Var v) = Var (replace_var amap v) /\
  replace_operand amap (Lit l) = Lit l /\
  replace_operand amap (Label lbl) = Label lbl
End

(* Replace variables in a list of operands *)
Definition replace_operands_def:
  replace_operands amap ops = MAP (replace_operand amap) ops
End

(* ==========================================================================
   Instruction Transformation
   ========================================================================== *)

(* TOP-LEVEL: Transform a single instruction.
   1. Replace source variables in operands
   2. For eliminable ASSIGNs, transform to NOP *)
Definition transform_inst_def:
  transform_inst amap inst =
    if is_eliminable_assign inst then
      (* Transform to NOP - the variable assignment is no longer needed
         because all uses have been replaced with the source variable *)
      inst with <| inst_opcode := NOP; inst_operands := []; inst_outputs := [] |>
    else
      (* Replace variables in operands *)
      inst with inst_operands := replace_operands amap inst.inst_operands
End

(* TOP-LEVEL: Transform a basic block *)
Definition transform_block_def:
  transform_block amap bb =
    bb with bb_instructions := MAP (transform_inst amap) bb.bb_instructions
End

(* TOP-LEVEL: Transform a function - builds assign map and transforms all blocks *)
Definition transform_function_def:
  transform_function fn =
    let amap = build_assign_map_fn fn in
    fn with fn_blocks := MAP (transform_block amap) fn.fn_blocks
End

(* TOP-LEVEL: Transform a context (all functions) *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* ==========================================================================
   Basic Properties
   ========================================================================== *)

Theorem transform_block_label:
  !amap bb. (transform_block amap bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def]
QED

Theorem transform_block_length:
  !amap bb.
    LENGTH (transform_block amap bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[transform_block_def, LENGTH_MAP]
QED

Theorem is_eliminable_assign_opcode:
  !inst. is_eliminable_assign inst ==> inst.inst_opcode = ASSIGN
Proof
  rw[is_eliminable_assign_def, assign_var_source_def] >>
  gvs[AllCaseEqs()]
QED

Theorem transform_inst_preserves_terminator:
  !amap inst.
    is_terminator (transform_inst amap inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[transform_inst_def] >>
  Cases_on `is_eliminable_assign inst` >> simp[is_terminator_def] >>
  (* When is_eliminable_assign, inst.inst_opcode = ASSIGN which is not terminator *)
  drule is_eliminable_assign_opcode >> simp[is_terminator_def]
QED

Theorem get_instruction_transform:
  !amap bb idx x.
    get_instruction bb idx = SOME x ==>
    get_instruction (transform_block amap bb) idx = SOME (transform_inst amap x)
Proof
  rw[get_instruction_def, transform_block_def] >>
  simp[EL_MAP]
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

Theorem lookup_block_transform:
  !lbl blocks amap.
    lookup_block lbl (MAP (transform_block amap) blocks) =
    OPTION_MAP (transform_block amap) (lookup_block lbl blocks)
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

(* ==========================================================================
   Resolve Variable Properties
   ========================================================================== *)

(* resolve_var with 0 fuel is identity *)
Theorem resolve_var_0:
  !amap v. resolve_var amap 0 v = v
Proof
  rw[Once resolve_var_def]
QED

(* resolve_var terminates when var not in map *)
Theorem resolve_var_not_in_dom:
  !amap fuel v. v NOTIN FDOM amap ==> resolve_var amap fuel v = v
Proof
  Induct_on `fuel` >> rw[Once resolve_var_def, FLOOKUP_DEF]
QED

val _ = export_theory();
