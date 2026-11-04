Theory makeSsaCurrentDefaultAudit
Ancestors makeSsaCurrentDefaultOrigin makeSsaCurrentMergeSlots
  makeSsaCurrentTokens

(* Static audit.  None of the statements in this theory asserts that a
   concrete runtime binding is initialized.

   Sufficient slot interface (still an obligation in the ordinary case):
   for an actual insertion of v at h, with allocated output out, select
   p, ev, path in the SUPPLIED certificate such that p is a predecessor
   of h, ev is its exit event, path is its actual ancestor path, and
     current_event_exit_env ev v <> CurrentInserted v h /\
     current_event_exit_env ev v <> CurrentDefault out.
   Together with certificate environment realization and the actual
   prefix/slot correspondence, current_tree_trace_nonself_slot then gives
   a concrete operand different from out.  The predecessor need not be
   the nondominated predecessor returned by MergeCertificate.

   Branch table under the frozen task premises:

   1. v is an original leading-PHI output.
      fn_phi_outputs_single_def gives the single-definition bound.
      current_actual_inserted_single_local confines any insertion to
      the defining block.  For lookup h = old and original index i,
      current_certificate_reinsertion_copy gives an inserted output [v],
      a name src <> v, and cleanup ASSIGN [Var src].  Its hypotheses are
      exactly the certificate, wf_function, fn_inst_wf, fn_defs_reach_uses,
      all_reachable, first_block_no_preds, entry block, supply coverage/ok,
      fn_phi_outputs_single_def, the index/output/opcode equations and
      insertion.  Presence of the leading PHI supplies
      blocks_have_leading_phi.  fn_phis_non_degenerate supplies retention
      of the original PHI, not temporal availability of arbitrary copies.
      This is a static non-NOP result, already proved elsewhere.

   2. v occurs as an operand of an original leading PHI.
      current_phi_operand_has_leading_phi makes the selector T;
      current_phi_operand_single_bound supplies the single-definition
      bound.  Insertion supplies selected liveness via
      current_pruned_reach_live.  current_selected_live_single_definition
      gives a defining db dominating h and says that if db is h, its
      occurrence is in the original PHI prefix.  In conjunction with
      current_actual_inserted_single_local, this reduces to branch 1.
      The remaining small integration obligation is lookup uniqueness
      to identify db with the block at h, plus fn_inst_wf's PHI output
      singleton shape.  There is no general ordinary-copy temporal claim.

   3. Remaining variables (no original PHI operand occurrence and no
      original PHI output occurrence).
      Selector F: no leading PHIs exist; selected liveness is entry live.
      Selector T: original PHIs exist for other owners, but h's leading
      PHIs do not define v or use it as a PHI operand.  Thus
      current_phi_cut_clear holds and current_selected_live_edge can
      propagate demand through definition-free source suffixes.
      Neither selector makes multiple definitions into one dominating
      original definition.  current_actual_demanded_cut_tokens is only
      for destinations WITHOUT insertion, so cannot discharge h directly.

   Missing universal graph lemma, proposed precisely for planning:
      under the frozen structural/definedness premises, certificate,
      current_actual_inserted fn v h, and absence of original PHI outputs
      and original PHI operand occurrences of v, there exist p ev path
      in the supplied certificate satisfying the sufficient slot
      interface above, for any out named by CurrentInserted v h.
      By the proved theorem below and MergeCertificate, only out=v
      needs new reasoning.  An appropriate path invariant must track
      demanded v from the selected cut backwards over definition-free
      edges until a real definition or prior inserted changing site is
      encountered; closure forces insertion at any live join where
      those origins cease to agree.  Definite assignment rules out
      reaching entry still demanding an undefined v.  Cycles require
      a finite source path/rank, not unguarded backwards recursion.
      This invariant must provide an existential different predecessor;
      it must NOT assert nondefault on every predecessor, or assume
      source success/target initialization.  This lemma is not proved
      here.  Singleton-copy temporal preservation remains separate.
*)

Theorem current_exit_name_alias_residual:
  current_history_valid V H /\
  current_token_name H (CurrentInserted v h) = SOME out /\
  current_token_name H
    (current_block_token fn ins v p (current_inherited_token fn ins v path)) = SOME n /\
  current_block_token fn ins v p (current_inherited_token fn ins v path) <>
    CurrentInserted v h ==>
  (n = out <=> out = v /\
    current_block_token fn ins v p (current_inherited_token fn ins v path) =
      CurrentDefault v)
Proof
  strip_tac >> drule_all current_inserted_name_collision >>
  metis_tac[current_exit_default_owner]
QED
