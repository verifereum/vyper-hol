# LOG: Type Soundness Repair

L001: [Session 1-5] Diagnosed dxrule_at (Pos last) matching wrong IH in mutual induction
L002: [Session 5] Identified qpat_x_assum + qspecl_then as fix for IH variable capture
L003: [Session 6] Implemented apply_eval_ih + close_inr_err_tac_for with qpat_x_assum
L004: [Session 6] >- (THEN1) causes SML type error in Resume blocks (gentactic vs tactic)
L005: [Session 6] qpat_x_assum with named ∀-variables FAILS on IHs — HOL4 renames bound vars
L006: [Session 6] KEY INSIGHT: INR cases may not need IH at all — "state unchanged on error" + constructor distinctness should suffice. Need to verify eval_X_state lemmas exist.
L007: [Session 6] augment_srw_ss[exception_distinct, error_distinct] already in file — simp_tac can prove no-TypeError constructor distinctness automatically
L008: [Session 6] Refactored close_inr_err_tac: replaced dxrule_at(Pos last) with apply_eval_ih — pattern matching BROKEN due to qpat_x_assum ∀-variable renaming
L009: [Session 6] >- / THEN1 type error in Resume blocks confirmed — produces gentactic not tactic
L010: [Session 6] KEY: "state unchanged on error" approach WON'T work — eval_X functions DO modify state before returning errors. No eval_X_state lemmas exist, only pure op state lemmas.
L011: [Session 6] dxrule_at (Pos last) variable capture: ACCEPT_TAC fails because ∀-variables get renamed, but gvs[] might resolve them via variable elimination
L012: [Session 6] simp_tac (srw_ss()) [] partially handles INR constructor distinctness but can't close INR goals without IH
L013: [Raise3] Replaced manual `?vl. x = Value vl` proof with `toplevel_value_typed_for_BaseT` boundary lemma
L014: [KEY][IH-application] Root cause of all 29 block failures: `apply_eval_ih` uses `qpat_x_assum` with named ∀-variables that fail due to HOL4 renaming in mutual induction
L015: [Session 9] Root cause: `apply_eval_ih` uses `qpat_x_assum` with untyped backtick terms → type inference fails in SML context → FIRST_ASSUM error
L016: [Session 9] Fix: `first_x_assum (fn th => if is_forall (concl th) then mp_tac (SPECL [type-annotated terms] th) else NO_TAC)`
L017: [Session 9] Raise3 NOT YET VERIFIED via holmake
L018: [Session 9] `qspecl_then` with untyped terms is the SPECIFIC failure point; SPECL with typed terms works

## Session 11

L019: [eval types] VERIFIED all eval function return types via HOL session: eval_stmt/eval_stmts = `unit + exception`, eval_expr = `toplevel_value + exception`, eval_iterator = `value list + exception`, eval_target = `assignment_value + exception`, eval_targets = `assignment_value list + exception`, eval_base_target = `(location # subscript list) + exception`
L020: [apply_eval_ih] REWROTE from qpat_x_assum-based to first_x_assum + is_forall + SPECL approach using IH's own bound vars for first n-2 args. STILL FAILS with FIRST_ASSUM error
L021: [KEY][apply_eval_ih] DIAGNOSED: SPECL raises HOL_ERR exception when types don't match → `first_x_assum` treats exception as failure → ALL ∀-assumptions skipped → FIRST_ASSUM error. FIX NEEDED: wrap SPECL in exception handler (handle HOL_ERR _ => raise UNCHANGED)
L022: [close_inr_err_tac] REWROTE to accept typed res_term and st_term params. Default uses eval_expr types
L023: [tp_bind_err_tac] REWROTE to use typed backtick terms
L024: [Raise3] RESTRUCTURED to use new apply_eval_ih. Still fails at FIRST_ASSUM (same root cause as L021)
L025: [Assert3] After cheating Raise3, Assert3 fails at `Cases_on 'b'` — "No var with name b free in goal". Root cause: `drule_all` at line 1141 doesn't properly apply IH — new `accounts_well_typed` antecedent may not resolve from assumptions
L026: [KEY][debugging] HOLMAKE-ONLY debugging is TOO SLOW (16-45s/cycle). Should use `hol_state_at` for interactive proof state inspection. Cheating all failing blocks first then inspecting each with hol_state_at is the right workflow
L027: [KEY][SPECL vars] IH bound variable NAMES from strip_forall may not be usable directly as SPECL terms — the types might differ after theorem instantiation. Need to test this interactively with hol_state_at
