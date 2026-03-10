(*
 * Tail Merge Pass — Definitions
 *
 * Merge structurally equivalent terminal basic blocks.
 * Conservative MVP:
 *   - only reachable, non-entry, halting blocks considered
 *   - blocks with PHI nodes are rejected
 *   - blocks with live-in variables are rejected (all vars defined locally)
 *
 * TOP-LEVEL:
 *   bb_self_contained     — no PHIs, all input vars defined within the block
 *   canon_operand         — canonical form of an operand for signature
 *   block_signature       — structural signature of a halting block (α-renamed)
 *   tail_merge_fn         — transform: deduplicate equivalent blocks
 *   tail_merge_ctx        — transform all functions in context
 *
 * Source: vyper/venom/passes/tail_merge.py
 *)

Theory tailMergeDefs
Ancestors
  cfgTransform venomWf

(* ===== Self-Containedness ===== *)

(* A block is self-contained if it has no PHI instructions and every
   variable used as an operand is defined (as an output) by some
   earlier instruction in the same block. This means no live-in vars. *)
Definition bb_self_contained_def:
  bb_self_contained bb ⇔
    EVERY (λinst. inst.inst_opcode ≠ PHI) bb.bb_instructions ∧
    (∀i inst v.
       i < LENGTH bb.bb_instructions ∧
       inst = EL i bb.bb_instructions ∧
       MEM (Var v) inst.inst_operands ⇒
       ∃j inst_j.
         j < i ∧
         inst_j = EL j bb.bb_instructions ∧
         MEM v inst_j.inst_outputs)
End

(* ===== Block Signature (α-renaming) ===== *)

(* Canonical operand: replace variables with positional indices,
   keep literals and labels as-is.
   var_map: association list mapping original var → canonical index.
   New vars get the next available index (= LENGTH var_map). *)
Definition canon_operand_def:
  canon_operand var_map (Var v) =
    (case ALOOKUP var_map v of
       SOME idx => (var_map, INL idx)
     | NONE =>
         let idx = LENGTH var_map in
         ((v, idx) :: var_map, INL idx)) ∧
  canon_operand var_map (Lit w) = (var_map, INR (INL w)) ∧
  canon_operand var_map (Label l) = (var_map, INR (INR l))
End

(* Canonical operands list: thread var_map through. *)
Definition canon_operands_def:
  canon_operands var_map [] = (var_map, []) ∧
  canon_operands var_map (op::ops) =
    let (var_map', cop) = canon_operand var_map op in
    let (var_map'', cops) = canon_operands var_map' ops in
    (var_map'', cop :: cops)
End

(* Canonical outputs: map each output var to a fresh index. *)
Definition canon_outputs_def:
  canon_outputs var_map [] = (var_map, []) ∧
  canon_outputs var_map (v::vs) =
    let idx = LENGTH var_map in
    let var_map' = (v, idx) :: var_map in
    let (var_map'', idxs) = canon_outputs var_map' vs in
    (var_map'', idx :: idxs)
End

(* Canonical instruction: (opcode, canonical_outputs, canonical_operands).
   Outputs are processed first (matches Python: outputs tuple before operands). *)
Definition canon_inst_def:
  canon_inst var_map inst =
    let (var_map', couts) = canon_outputs var_map inst.inst_outputs in
    let (var_map'', cops) = canon_operands var_map' inst.inst_operands in
    (var_map'', (inst.inst_opcode, couts, cops))
End

(* Canonical instruction list: thread var_map through. *)
Definition canon_insts_def:
  canon_insts var_map [] = [] ∧
  canon_insts var_map (inst::insts) =
    let (var_map', ci) = canon_inst var_map inst in
    ci :: canon_insts var_map' insts
End

(* Block signature: canonical instruction sequence, or NONE if ineligible.
   A block is eligible if it's halting and self-contained. *)
Definition block_signature_def:
  block_signature bb =
    if bb_is_halting bb ∧ bb_self_contained bb then
      SOME (canon_insts [] bb.bb_instructions)
    else NONE
End

(* ===== Tail Merge Transformation ===== *)

(* Compute (label, signature) pairs for eligible blocks.
   Skips entry block and unreachable blocks (matches Python). *)
Definition block_sigs_def:
  block_sigs func entry_label [] = [] ∧
  block_sigs func entry_label (bb::bbs) =
    if bb.bb_label = entry_label then
      block_sigs func entry_label bbs
    else if ¬reachable func bb.bb_label then
      block_sigs func entry_label bbs
    else
      (bb.bb_label, block_signature bb) ::
        block_sigs func entry_label bbs
End

(* Given (label, signature option) pairs, compute the label map:
   for each group of blocks with the same signature, keep the first
   and map others to it.
   groups: assoc list from signature → keeper label.
   Returns assoc list from label → keeper label. *)
Definition compute_merge_map_def:
  compute_merge_map [] groups = [] ∧
  compute_merge_map ((lbl, NONE) :: rest) groups =
    compute_merge_map rest groups ∧
  compute_merge_map ((lbl, SOME sig) :: rest) groups =
    case ALOOKUP groups sig of
      SOME keeper =>
        (lbl, keeper) :: compute_merge_map rest groups
    | NONE =>
        compute_merge_map rest ((sig, lbl) :: groups)
End

(* Tail merge a single function.
   1. Compute signatures for eligible blocks
   2. Compute merge map (label → keeper)
   3. Apply batch label substitution (matches Python _replace_all_labels)
   4. Remove merged blocks *)
Definition tail_merge_fn_def:
  tail_merge_fn func =
    case fn_entry_label func of
      NONE => func
    | SOME entry_label =>
        let sigs = block_sigs func entry_label func.fn_blocks in
        let merge_map = compute_merge_map sigs [] in
        if merge_map = [] then func
        else
          (* Batch label substitution *)
          let func' = subst_label_map_fn merge_map func in
          (* Remove merged blocks *)
          let removed_labels = MAP FST merge_map in
          func' with fn_blocks :=
            FILTER (λbb. ¬MEM bb.bb_label removed_labels)
                   func'.fn_blocks
End

(* Tail merge all functions in a context. *)
Definition tail_merge_ctx_def:
  tail_merge_ctx ctx =
    ctx with ctx_functions := MAP tail_merge_fn ctx.ctx_functions
End
