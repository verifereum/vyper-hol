# LOG: Type Soundness Repair

L001: [apply_eval_ih] Replaced qspecl_then with drule_all in apply_eval_ih → compiles
L002: [Raise3] Fixed INR case: qpat_x_assum + drule_all + no_return_from_eval → works
L003: [Raise3] Fixed dest_StringV case split: Cases_on + gvs + value_has_type_StringT_dest_StringV_NEQ_NONE → works
L004: [Raise3] Fixed final goal: INR(AssertException x)=res ∧ r=st' → rpt strip_tac >> gvs[] → works, Raise3 QED
L005: [Assert3] FAIL: qpat_x_assum ∀ pattern can't find IH → Q_TAC0/FIRST_ASSUM error
L006: [Assert3] FAIL: reverse(Cases_on q) >- close_inr_err_tac → close_inr_err_tac doesn't solve INR
L007: [Assert3] KEY INSIGHT: simp_tac(srw_ss())[] after Cases_on q SOLVES BOTH SUBGOALS → "goal completely solved by first tactic"
L008: [Assert3] FAIL: AllCaseEqs() on monadic bind chain → 300s timeout
L009: [Assert3] FAIL: first_x_assum drule_all picks wrong IH → Cases_on b fails because b not in scope
L010: [Assert3] DIAGNOSIS: After simp_tac solves both cases, no subgoals remain. Manual IH application is unnecessary. Need simpler proof.
L011: [Assert3] PENDING: Try rewrite_tac + simp_tac + gvs[] approach next session
L012: [KEY][Assert3] insight: simp_tac(srw_ss())[] after Cases_on q SOLVES BOTH INL and INR. Many blocks may be provable without explicit IH application.
L013: [apply_eval_ih] qpat_x_assum ∀-patterns can FAIL in multi-IH contexts even when assumption exists. Need PRED_ASSUM is_forall fallback.
L014: [Assert3] FAILED[wrong_decomposition]: `>- (* INR case *)` targets wrong subgoal — INL is first after `Cases_on q`, not INR. Three failed attempts with different `>-` placements.
L015: [KEY][Assert3] Subgoal ordering: after `Cases_on q`, INL (value) is always subgoal 1, INR (error) is subgoal 2. Use `TRY (.. >> NO_TAC)` from Raise3 instead of `>-`.
L016: [apply_eval_ih] FIXED: Added PRED_ASSUM fallback for when qpat_x_assum ∀-patterns fail in batch mode. Three SML syntax errors fixed: `&&`→`andalso`, `name_of`→`fst o dest_const`, `can` type mismatch.
L017: [KEY][hol_check_proof] hol_check_proof does NOT verify Resume blocks — only checks main theorem up to suspend points. Must use holmake for Resume verification.
L018: [Assert3] FAILED[wrong_variable]: Replace `>-` with TRY/NO_TAC pattern. But `Cases_on b'` fails — `b'` doesn't exist in current goal after gvs[toplevel_value_typed_def]. Variable is `x : toplevel_value`, not `Value v`.
L019: [Assert3] FAILED[timeout]: `Cases_on v` where `v : value` creates too many subgoals + gvs[value_has_type_def] → 300s timeout.
L020: [Assert3] FAILED[first_assum]: `simp[switch_BoolV_def, AllCaseEqs()]` + `first_x_assum (qspec_then 'x' assume_tac)` → FIRST_ASSAM error. qspec_then can't match after simplification.
L021: [Assert3] FAILED[first_assam]: `drule switch_BoolV_cases >> strip_tac` + `qpat_x_assum 'x = Value (BoolV T)'` → FIRST_ASSUM. Assumption pattern doesn't match.
L022: [Assert3] FAILED[cases_on]: `Cases_on 'v'` where v eliminated by gvs → "No var with name v free in goal".
L023: [KEY][Assert3] Root cause: after gvs[toplevel_value_typed_def] >> evaluate_type_BaseT_inv >> gvs[], variable is `x : toplevel_value` not `Value v`. Old code assumed wrong variable naming.
L024: [Assert3] CHEATED to unblock build. Correct fix: use `switch_BoolV_cases` boundary lemma or `Cases_on 'x' >> gvs[toplevel_value_typed_def]`.
L025: [KEY][systemic] After cheating Assert3, 29+ blocks fail with FIRST_ASSAM. Root cause: `first_assum ACCEPT_TAC` fragile after definition changes. Append works interactively until `impl_tac >- first_assum ACCEPT_TAC` on line 1190.
L026: [KEY][strategy] Need systematic approach: cheat ALL failing blocks first, get complete failure inventory, fix infrastructure, then prove blocks one at a time.
L027: [Append] FAILED[Q_TAC0]: Replace qspecl_then+impl_tac with qpat_x_assum+drule_all. Q_TAC0 parsing error on `!s'' loc' sbs' t'` pattern.
L028: [Append] FAILED[Q_TAC0+FIRST_ASSAM]: Replace qpat_x_assum with PRED_ASSUM+same_const+drule_all. Same Q_TAC0 parsing error.
L029: [Append] FAILED[FIRST_ASSAM]: Replace with first_x_assum(fn th=>if same_const ... then drule_all). Error changed to just FIRST_ASSAM — NO eval_base_target ∀-assumption in scope.
L030: [KEY][Append] ROOT CAUSE: first_x_assum drule_all at line 1176 consumes the GUARDED P7 IH instead of P5 IH. After that, there's no eval_base_target ∀-assumption for line 1188. All previous "qspecl_then" failures were misdiagnosed — the real problem was earlier, at line 1176.
L031: [strategy] When fixing a proof failure, check ALL first_x_assum calls in preceding proof steps, not just the line that reports the error.
