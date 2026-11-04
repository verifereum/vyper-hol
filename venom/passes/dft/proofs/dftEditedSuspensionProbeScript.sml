(* Integration audit: equal-control hidden transport is not edited-callee
   transport. These are interface tests, not counterexamples to ctx_sim. *)
Theory dftEditedSuspensionProbe
Ancestors
  dftInvokeOrdinaryBoundary dftHiddenClock dftInaccessibleCaller
  dftPendingSuspension dftOccurrenceOrdinaryClosure dftOccurrenceGasEdit
  dftOccurrenceMachine dftOpenMachine list

Theorem dft_hidden_entry_requires_equal_callees:
  dft_hidden_caller R fL fR tL tR savedL savedR path visit l r /\
  l.dft_occ_core = DftOpen (DftEnter calleeL 0 csL) stackL nL /\
  r.dft_occ_core = DftOpen (DftEnter calleeR 0 csR) stackR nR ==>
  calleeL = calleeR /\ csL = csR
Proof
  simp[dft_hidden_caller_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_pending_entry_requires_equal_callees:
  dft_pending_suspended us fL fR tL tR savedL savedR path visit l r /\
  l.dft_occ_core = DftOpen (DftEnter calleeL 0 csL) stackL nL /\
  r.dft_occ_core = DftOpen (DftEnter calleeR 0 csR) stackR nR ==>
  calleeL = calleeR /\ csL = csR
Proof
  rewrite_tac[dft_pending_suspended_hidden] >>
  metis_tac[dft_hidden_entry_requires_equal_callees]
QED

(* Unlike hidden transport, the existing edit map changes each active callee.
   It changes neither the caller state nor the instruction index. *)
Theorem dft_edit_recursive_entry_shape:
  dft_edit_occ fm bm
    (l with dft_occ_core := DftOpen (DftEnter fn 0 s) stack n) =
  l with dft_occ_core := DftOpen (DftEnter (fm fn) 0 s)
    (MAP (dft_edit_frame fm bm) stack) n
Proof
  simp[dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def]
QED

(* Proposed integration contract, NOT definitions or assumed theorems:

   Let P Corig C C' L l r denote a future mixed residual relation. It must
   contain an inductive list of paired saved callers, each carrying either
   an ordinary edited frame or its own pending update list. A single
   distinguished caller plus equal active control is insufficient.

   Segment candidate (literal HOL shape with P as a schematic predicate):
     !l r. P l r ==>
       ?k j. 0 < k /\ 0 < j /\
         P (FUNPOW (dft_occ_oracle_next w C) k l)
           (FUNPOW (dft_occ_oracle_next w C') j r)
   This must be accompanied by source-ready preservation, target-prefix
   observation coverage, and event correspondence OR justified discard.
   Segment existence alone supplies neither of the latter properties.

   Root candidate:
     !l r result n. P l r /\
       l.dft_occ_core = DftOpen (DftDone result) [] n ==>
       ?result' n'. r.dft_occ_core = DftOpen (DftDone result') [] n' /\
         dft_ordinary_result_rel result result'

   Branch/dependency audit:
   - Entry: dft_pending_two_context_push_fields exposes separate callees,
     setup states, caller metadata and clocks. No setup equality is supplied.
   - Recursive edit: dft_edit_recursive_entry_shape changes the active fn,
     while dft_ordinary_sync requires the whole right state to be its edit
     image. That map preserves caller states and indices. It therefore
     cannot encode the outstanding pending updates/index offset at an
     outer INVOKE/ordinary crossing, let alone two nested such crossings.
   - Return: dft_pending_return_cut handles payload replay for a common
     ret/callee state; an edited execution needs a return-result boundary
     feeding this replay, plus discharge of the top paired saved frame.
   - Abort/clearing: root result matching ignores abort state, but pending
     payload must be discarded along with all frames, not restored.
   - Observations: hidden_caller_observe is same-active-control only;
     across edits need function-map provenance, operand/range agreement
     and memory equality, as in dft_original_mixed_orbit_observe.
   - Events: terminal relation does not supply GAS correspondence; crossing
     may stop with an unmatched read. Match-or-local-discard is separate.
   - Counters: dft_hidden_caller_next_count works only for the unilateral
     same-context payload leg. Distinct active schedules need event counts.

   Existing GAS/ordinary orbit theorems do not provide P for INVOKE edits:
   dft_ordinary_sync_outside assumes x.inst_opcode <> INVOKE and its endpoint
   family carries no recursively accumulating pending-frame relation.
   No global transport hypothesis is assumed in this probe theory.
*)
