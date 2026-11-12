(*
 * Assert Combiner Pass — Definitions
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 *
 * Ports vyper/venom/passes/assert_combiner.py to HOL4.
 *
 * Combines consecutive `assert iszero(x)` instructions into a single
 * assert using OR:
 *   assert iszero(a); assert iszero(b)  →  assert iszero(a | b)
 *
 * Two phases:
 *   1. Analysis: scan each block for mergeable assert pairs
 *   2. Transform: merge pairs using OR + ISZERO
 *
 * Merge conditions:
 *   - Both asserts use iszero (traced through assigns)
 *   - Same error_msg (modeled as: both are plain ASSERT)
 *   - No volatile/effectful instructions between them
 *
 * Uses DFG analysis (to trace iszero chains through assigns).
 *
 * TOP-LEVEL:
 *   ac_get_iszero_operand    — trace through assigns to find iszero input
 *   ac_is_safe_between       — check if instruction is safe between asserts
 *   ac_scan_block            — analysis: find mergeable assert pairs
 *   ac_merge_inst/insts      — transform: apply the merges, taking the
 *                              OR/ISZERO ids and names from the supply
 *   ac_transform_block       — block-level transform
 *   ac_transform_function    — function-level transform, threading the
 *                              ir_supply the fresh ids/names come from
 *
 * Source: vyper/venom/passes/assert_combiner.py
 *)

Theory assertCombinerDefs
Ancestors
  passTransform dfgDefs venomExecSemantics venomInst venomEffects irSupply
Libs
  pred_setTheory

(* ===== Volatile Detection ===== *)

(* An instruction is volatile if it has observable side effects that
   cannot be reordered. Matches Python IRInstruction.is_volatile.
   Defined here because is_volatile is not yet on main. *)
Definition ac_is_volatile_def:
  ac_is_volatile (opc : opcode) <=>
    MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
             SELFDESTRUCT; LOG; SSTORE; TSTORE;
             MSTORE; MCOPY; ISTORE;
             CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY;
             DLOADBYTES; ASSERT; ASSERT_UNREACHABLE]
End

(* ===== Analysis Helpers ===== *)

(* Check if an instruction is safe to appear between two asserts.
   Must not be a terminator, volatile, or have effects.
   ALLOCA excluded: it modifies vs_allocas (non-variable state),
   breaking execution_equiv in the deferred-abort case.
   PHI/PARAM/FMP_PARAM/OFFSET excluded: they can fail even when operands evaluate
   (PHI needs vs_prev_bb, PARAM/FMP_PARAM need an index in range,
    OFFSET needs the label map). *)
Definition ac_is_safe_between_def:
  ac_is_safe_between inst <=>
    ~is_terminator inst.inst_opcode /\
    ~ac_is_volatile inst.inst_opcode /\
    inst.inst_opcode <> ALLOCA /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> OFFSET /\
    write_effects inst.inst_opcode = {} /\
    read_effects inst.inst_opcode = {}
End

(* Trace an operand through ASSIGN chains to find an ISZERO instruction.
   Returns SOME (iszero's input operand) if found, NONE otherwise.
   Uses visited-set for termination (SSA def-use chains are acyclic). *)
Definition ac_get_iszero_operand_def:
  ac_get_iszero_operand dfg visited op =
    case op of
      Var v =>
        (case dfg_get_def dfg v of
           SOME inst =>
             if inst.inst_id IN visited then NONE
             else if inst.inst_opcode = ISZERO then
               (case inst.inst_operands of
                  [src] => SOME src
                | _ => NONE)
             else if inst.inst_opcode = ASSIGN then
               (case inst.inst_operands of
                  [src] => ac_get_iszero_operand dfg
                             (inst.inst_id INSERT visited) src
                | _ => NONE)
             else NONE
         | NONE => NONE)
    | _ => NONE
Termination
  WF_REL_TAC `inv_image $< (\(dfg,visited,_). CARD (dfg_def_ids dfg DIFF visited))`
  >> rpt strip_tac
  >> imp_res_tac dfg_get_def_implies_dfg_def_ids
  >> irule CARD_PSUBSET
  >> simp[FINITE_DIFF, dfg_def_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION]
  >> qexists_tac `inst.inst_id` >> simp[]
End

(* ===== Merge Candidate ===== *)

Datatype:
  merge_candidate = <|
    mc_first_id  : num;        (* inst_id of first assert (to remove) *)
    mc_first_pred : operand;   (* iszero's input for first assert *)
    mc_second_id : num;        (* inst_id of second assert (to modify) *)
    mc_second_pred : operand   (* iszero's input for second assert *)
  |>
End

(* ===== Analysis: Find Merge Pairs ===== *)

(*
 * Scan a block's instructions to find pairs of asserts that can be merged.
 * Maintains a "pending" assert. When a second assert is found with a safe
 * gap, it forms a merge candidate.
 *
 * pending : SOME (inst_id, iszero_pred) of the current pending assert
 *)
Definition ac_scan_block_def:
  ac_scan_block dfg [] pending = [] /\
  ac_scan_block dfg (inst :: rest) pending =
    if inst.inst_opcode = ASSERT then
      case (inst.inst_operands,
            ac_get_iszero_operand dfg {} (HD inst.inst_operands)) of
        ([_], SOME pred) =>
          (case pending of
             SOME (prev_id, prev_pred) =>
               (* Found a merge pair *)
               let mc = <| mc_first_id := prev_id;
                           mc_first_pred := prev_pred;
                           mc_second_id := inst.inst_id;
                           mc_second_pred := pred |> in
               (* Chain: merged result becomes new pending *)
               mc :: ac_scan_block dfg rest (SOME (inst.inst_id, pred))
           | NONE =>
               ac_scan_block dfg rest (SOME (inst.inst_id, pred)))
      | _ =>
          (* Assert without iszero pattern — reset pending *)
          ac_scan_block dfg rest NONE
    else if ac_is_safe_between inst then
      (* Safe instruction — keep pending *)
      ac_scan_block dfg rest pending
    else
      (* Unsafe instruction — reset pending *)
      ac_scan_block dfg rest NONE
End

(* ===== Transform: Apply Merges ===== *)

(*
 * Apply merge to one instruction, given the block's merge candidates.
 *
 * merged_preds maps an assert id to the predicate it ended up checking.
 * When instruction B is "second" of MC1 (merge with A):
 *   - The merged pred for B = Var or_v (the OR output)
 *   - If B is later "first" of MC2, we use merged_preds[B] instead of mc_first_pred
 * The OR/ISZERO ids and outputs come from the supply, as Python's
 * InstUpdater.add_before takes them from fn.get_next_variable().
 *
 * IMPORTANT: Process "second" logic BEFORE "first" NOP, so that a
 * 3-assert chain A→B→C correctly records merged_preds[B] before B is NOP'd.
 * Otherwise pred_a would be lost when processing C.
 *)
Definition ac_merge_inst_def:
  ac_merge_inst candidates merged_preds sup inst =
    (* Phase 1: "second" merge — compute OR/ISZERO, update merged_preds *)
    let (merged_preds1, pre_insts, merged_op, sup1) =
      case FIND (\mc. mc.mc_second_id = inst.inst_id) candidates of
        SOME mc =>
          let actual_first_pred =
            case ALOOKUP merged_preds mc.mc_first_id of
              SOME p => p
            | NONE => mc.mc_first_pred in
          if actual_first_pred = mc.mc_second_pred then
            (* Identical preds — no merge needed, but record for chaining *)
            ((mc.mc_second_id, actual_first_pred) :: merged_preds,
             [], NONE, sup)
          else
            (case fresh_inst_id sup of (or_id, s1) =>
             case fresh_ir_var s1 of (or_v, s2) =>
             case fresh_inst_id s2 of (iz_id, s3) =>
             case fresh_ir_var s3 of (iz_v, s4) =>
               ((mc.mc_second_id, Var or_v) :: merged_preds,
                [<| inst_id := or_id; inst_opcode := OR;
                    inst_operands := [actual_first_pred; mc.mc_second_pred];
                    inst_outputs := [or_v] |>;
                 <| inst_id := iz_id; inst_opcode := ISZERO;
                    inst_operands := [Var or_v]; inst_outputs := [iz_v] |>],
                SOME iz_v, s4))
      | NONE => (merged_preds, [], NONE, sup) in
    (* Phase 2: if this is also a "first" assert — NOP it *)
    if EXISTS (\mc. mc.mc_first_id = inst.inst_id) candidates then
      (merged_preds1,
       pre_insts ++ [inst with <| inst_opcode := NOP; inst_operands := [];
                                  inst_outputs := [] |>],
       sup1)
    (* Phase 3: if it was only a "second" — emit merged assert *)
    else case merged_op of
      SOME iz_v =>
        (merged_preds1, pre_insts ++ [inst with inst_operands := [Var iz_v]],
         sup1)
    | NONE => (merged_preds1, pre_insts ++ [inst], sup1)
End

Definition ac_merge_insts_def:
  ac_merge_insts candidates merged_preds sup [] = ([], sup) /\
  ac_merge_insts candidates merged_preds sup (inst :: insts) =
    case ac_merge_inst candidates merged_preds sup inst of
      (mp1, out, s1) =>
        case ac_merge_insts candidates mp1 s1 insts of
          (outs, s2) => (out ++ outs, s2)
End

(* ===== Block and Function Transform ===== *)

Definition ac_transform_block_def:
  ac_transform_block dfg sup bb =
    case ac_merge_insts (ac_scan_block dfg bb.bb_instructions NONE) [] sup
                        bb.bb_instructions of
      (insts, sup') => (bb with bb_instructions := insts, sup')
End

Definition ac_transform_blocks_def:
  ac_transform_blocks dfg sup [] = ([], sup) /\
  ac_transform_blocks dfg sup (bb :: bbs) =
    case ac_transform_block dfg sup bb of (bb', s1) =>
    case ac_transform_blocks dfg s1 bbs of (bbs', s2) =>
      (bb' :: bbs', s2)
End

Definition ac_transform_function_def:
  ac_transform_function sup fn =
    case ac_transform_blocks (dfg_build_function fn) sup fn.fn_blocks of
      (bbs, sup') => (fn with fn_blocks := bbs, sup')
End

(* The variables the transform may introduce: those it took from the
   supply. *)
Definition ac_fresh_vars_def:
  ac_fresh_vars sup fn =
    set (SND (ac_transform_function sup fn)).irs_used_vars DIFF
    set sup.irs_used_vars
End
