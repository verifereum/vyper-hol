(*
 * SimplifyCFG Well-Formedness Definitions
 *
 * This theory defines well-formedness conditions for CFG simplification.
 * wf_cfg_fn is the syntactic condition users should check.
 * cfg_wf_fn is the semantic condition used in proofs.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - wf_cfg_fn              : Syntactic well-formedness for CFG
 *   - cfg_wf_fn              : CFG-specific well-formedness conditions
 *
 * TOP-LEVEL THEOREMS:
 *   - wf_cfg_implies_cfg_wf  : Syntactic WF implies CFG WF
 *
 * ============================================================================
 *)

Theory cfgWellFormed
Ancestors
  cfgTransform stateEquiv venomSem venomState venomInst list

(* ==========================================================================
   Block Well-Formedness
   ========================================================================== *)

(* A block is well-formed if:
   1. It has at least one instruction
   2. The last instruction is a terminator
   3. Non-terminator instructions are not at the end *)
Definition wf_block_def:
  wf_block bb <=>
    bb.bb_instructions <> [] /\
    (case get_terminator bb of
       SOME inst => is_terminator inst.inst_opcode
     | NONE => F)
End

(* All jump targets in a block exist in the function *)
Definition targets_exist_def:
  targets_exist bb blocks <=>
    !lbl. MEM (SOME lbl) (MAP get_label
            (case get_terminator bb of
               NONE => []
             | SOME inst => inst.inst_operands)) ==>
          ?b. lookup_block lbl blocks = SOME b
End

(* ==========================================================================
   Function Well-Formedness
   ========================================================================== *)

(* Unique block labels *)
Definition unique_labels_def:
  unique_labels blocks <=>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) blocks)
End

(* TOP-LEVEL: Simple syntactic well-formedness for CFG functions.
   Users should check this to ensure CFG simplification is correct. *)
Definition wf_cfg_fn_def:
  wf_cfg_fn func <=>
    (* Function has at least one block (entry) *)
    func.fn_blocks <> [] /\
    (* All blocks are well-formed *)
    EVERY wf_block func.fn_blocks /\
    (* All jump targets exist *)
    EVERY (\bb. targets_exist bb func.fn_blocks) func.fn_blocks /\
    (* Unique block labels *)
    unique_labels func.fn_blocks
End

(* ==========================================================================
   Merge Conditions
   ========================================================================== *)

(* A block has no PHI instructions *)
Definition no_phi_block_def:
  no_phi_block bb <=> ~EXISTS is_phi_inst bb.bb_instructions
End

(* Merge well-formedness: conditions for merging block A into its predecessor *)
Definition merge_wf_def:
  merge_wf pred_bb succ_bb blocks <=>
    (* Predecessor ends with unconditional jump to successor *)
    get_block_target pred_bb = SOME succ_bb.bb_label /\
    (* Successor has single predecessor *)
    has_single_predecessor succ_bb.bb_label blocks /\
    (* Successor has no PHI instructions *)
    no_phi_block succ_bb /\
    (* Both blocks are well-formed *)
    wf_block pred_bb /\
    wf_block succ_bb
End

(* ==========================================================================
   Thread Conditions
   ========================================================================== *)

(* Thread well-formedness: conditions for threading through a passthrough block *)
Definition thread_wf_def:
  thread_wf passthrough_bb <=>
    (* Block is a passthrough (single JMP instruction) *)
    is_passthrough_block passthrough_bb /\
    (* Block has a valid target *)
    get_block_target passthrough_bb <> NONE
End

(* ==========================================================================
   Semantic Well-Formedness
   ========================================================================== *)

(* Helper: Well-formedness predicate for CFG simplification.
   This is the semantic condition used in the main correctness proofs. *)
Definition cfg_wf_fn_def:
  cfg_wf_fn func <=>
    (* Basic syntactic well-formedness *)
    wf_cfg_fn func /\
    (* Entry block exists and is reachable *)
    (func.fn_blocks <> [] ==>
     lookup_block (HD func.fn_blocks).bb_label func.fn_blocks = SOME (HD func.fn_blocks)) /\
    (* All blocks terminate properly *)
    (!bb. MEM bb func.fn_blocks ==>
          wf_block bb /\ targets_exist bb func.fn_blocks)
End

(* ==========================================================================
   Well-Formedness Preservation
   ========================================================================== *)

(* Helper: merged block is well-formed if both inputs are *)
Theorem merge_blocks_wf:
  !a b.
    wf_block a /\ wf_block b ==>
    wf_block (merge_blocks a b)
Proof
  cheat
QED

(* Helper: replace_label preserves well-formedness *)
Theorem replace_label_block_wf:
  !old new bb. wf_block bb ==> wf_block (replace_label_block old new bb)
Proof
  cheat
QED

(* Helper: thread_jump preserves well-formedness *)
Theorem thread_jump_block_wf:
  !pl tl bb. wf_block bb ==> wf_block (thread_jump_block pl tl bb)
Proof
  cheat
QED

(* ==========================================================================
   Main Theorem: Syntactic implies Semantic WF
   ========================================================================== *)

(* Helper: HD block is in blocks *)
Theorem hd_mem:
  !blocks. blocks <> [] ==> MEM (HD blocks) blocks
Proof
  Cases >> simp[]
QED

(* TOP-LEVEL: wf_cfg_fn implies cfg_wf_fn *)
Theorem wf_cfg_implies_cfg_wf:
  !func. wf_cfg_fn func ==> cfg_wf_fn func
Proof
  rw[wf_cfg_fn_def, cfg_wf_fn_def] >>
  fs[EVERY_MEM] >>
  Cases_on `func.fn_blocks` >> fs[lookup_block_def]
QED

(* ==========================================================================
   Transformation Preserves Well-Formedness
   ========================================================================== *)

(* Remove block preserves unique labels *)
Theorem remove_block_unique_labels:
  !lbl blocks.
    unique_labels blocks ==>
    unique_labels (remove_block lbl blocks)
Proof
  cheat
QED

(* Map preserving labels preserves unique labels *)
Theorem map_preserves_unique_labels:
  !f blocks.
    (!bb. (f bb).bb_label = bb.bb_label) /\
    unique_labels blocks ==>
    unique_labels (MAP f blocks)
Proof
  cheat
QED

