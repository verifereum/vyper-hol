# STATE_type_system_rewrite
Updated: 2026-05-14

## Cursor
- component: C3.1.7.3
- status: in_progress
- active_file: semantics/prop/vyperTypeStatePreservationScript.sml
- next_action: 1) Run holbuild to test if renaming theorem to _v2 broke the stale checkpoint. The theorem is now assign_target_TopLevelVar_ArrayRef_branch_ntr_v2 (line 2469). 2) If checkpoint is broken, replace 4 FAIL_TAC probes (lines 2593, 2596, 2612, 2615) with explicit value_has_type derivation. 3) If _v2 rename didn't break checkpoint, try suspend/Resume or extract AppendOp/PopOp as boundary sub-lemmas.
- expected_goal_shape: After CCONTR_TAC >> gvs[] in AppendOp write2 branch: goal has write_storage_slot ... (BaseTV(UintT 256)) (IntV(&(w2n(lookup_storage elem_slot storage)+1))) = (INR(Error(TypeError msg)),st') with assumptions including w2n(lookup_storage elem_slot storage) < n and n < dimword(:256). Need value_has_type (BaseTV (UintT 256)) (IntV(&(w2n(...)+1))).
- verify_with: holbuild(targets=['vyperTypeStatePreservationTheory'])

## If This Fails
- If checkpoint persists even after _v2 rename, extract AppendOp/PopOp into separate standalone boundary lemmas with minimal hypotheses.

## Do Not Retry
- Adding all_tac >> before rpt strip_tac to break stale holbuild checkpoint: Does NOT work - holbuild still matches the checkpoint. all_tac may be optimized away or checkpoint hashes more than prefix text.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6460_t001
- Using metis_tac[write_storage_slot_no_type_error_from_value_has_type] alone for AppendOp/PopOp UintT 256 length writes: metis_tac cannot derive value_has_type (BaseTV (UintT 256)) (IntV &(stored_len +/- 1)) from arithmetic assumptions alone. Need explicit derivation with simp[value_has_type_def] + decide_tac.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6414_t001
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6433_t001

## Reflection
### Tunnel Vision Check
- The stale holbuild checkpoint has been the PRIMARY blocker for 6+ episodes across 3 sessions. Renaming the theorem is the nuclear option - if even that doesn't work, the issue is deeper in holbuild checkpoint storage.
- Rather than fighting the checkpoint inline, extracting AppendOp/PopOp into separate boundary lemmas would: (a) avoid the large AllCaseEqs blast, (b) make each proof self-contained, (c) sidestep the checkpoint entirely since new theorems have never been built.
- The inline Cases_on x1 + Cases_on bd + Cases_on op structure is architecturally correct but tactically fragile - splitting into boundary sub-lemmas for each case pattern follows the proven HashMapRef/Value branch model.

### What Went Wrong
- all_tac >> before rpt strip_tac did NOT break the stale holbuild checkpoint - contrary to previous learnings (L0127/L0149). The checkpoint may hash more than just prefix text.
- FAIL_TAC probes were inserted correctly but never reached because checkpoint replays old pre-probe proof state.
- Renaming theorem to _v2 should definitively break the checkpoint (different theorem name key) but was the very last action and untested.

### Ignored Signals
- The instrumented log (TO_m6461) showed the full goal state including large lambda-case - confirms proof is on the right track. PairCases_on x >> gvs[] should beta-reduce it.
- Multiple previous episodes (E0054-E0056) already noted the checkpoint issue. Should have renamed the theorem much earlier instead of trying minor prefix changes.

### Strategy Adjustments
- RENAME THE THEOREM FIRST on any future encounter with stale holbuild checkpoints. all_tac >> is unreliable; theorem rename is definitive.
- After checkpoint is broken, insert FAIL_TAC probe early to verify goal state before writing dispatch tactics.
- For AppendOp/PopOp value_has_type: use simp[value_has_type_def] + decide_tac after deriving w2n(...)+1 < 2^256 from well_formed_type_value(ArrayTV _ (Dynamic n)) giving n < dimword(:256) plus check giving w2n(lookup_storage...) < n.
- If inline derivation is too fragile, extract into boundary sub-lemmas.

### Oracle Feedback
- PLAN correctly rates C3.1.7.3 as Risk 1 - the mathematical argument is clear. The difficulty is purely tactical (checkpoint + arithmetic), not architectural.
- The extract-boundary-sub-lemma recommendation from PLAN has been consistently correct - should follow it for AppendOp/PopOp instead of trying inline closure within the large proof.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6460_t001 - holbuild with all_tac >> still matching stale checkpoint
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6461_t001 - instrumented log showing full goal state at failure point
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6436_t002 - initial build showing FAIL_TAC error
