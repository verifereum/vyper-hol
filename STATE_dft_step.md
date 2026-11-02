# STATE_dft_step
Updated: 2026-11-02

## Cursor
- component: C1.6
- status: in_progress
- active_file: venom/compiler/o1DftStepScript.sml
- next_action: Fix dft_shape_first_no_phi around lines107-112: after rpt strip_tac the live instruction is i, but subsequent quoted facts use free e. Add rename1 `MEM e (HD (dft_fn fn).fn_blocks).bb_instructions` before the pseudo-filter membership assertion, or consistently use i. Then build. dft_shape_first_no_preds below it is not yet verified. Continue complete o1_fn_shape transport using the already proved copy-PHI/opaque-use and dftLifting boundaries.
- expected_goal_shape: First failing subgoal is is_pseudo e.inst_opcode /\ MEM e first_output_instructions, while assumptions instead give MEM i first_output_instructions and i.inst_opcode=PHI. Correct binder resolves this routine error; there is no counterexample or strategic blocker.
- verify_with: holbuild(targets=['o1DftStepTheory'], timeout=1800)

## If This Fails
- Inspect the new small boundary goal. Keep C1.6 active and checkpoint useful progress. If the relation lacks a needed interface or shape transport becomes structurally hard, close C1.6 stuck with exact evidence and request strategist review.

## Do Not Retry
- strip_tac on the source provenance existential/disjunction before splitting opaque-use gas/retpc implications: Creates multiple source cases and then four conjunct branches; use qx_choose_then `j` (CONJUNCTS_THEN assume_tac) to keep disjunction intact.
  - evidence: tool_output:TO_dft_step-20261102T123913Z_m0445_t001
  - evidence: tool_output:TO_dft_step-20261102T123913Z_m0447_t001
- pure_rewrite_tac[Abbr `dstep`,Abbr `initial`] on FUNPOW result target: Timed out; simp[NoAsms,Abbr ...] is the verified choice when the result equation must not simplify away the target.
  - evidence: tool_output:TO_dft_step-20261102T123913Z_m0401_t001
  - evidence: tool_output:TO_dft_step-20261102T123913Z_m0403_t001

## Reflection
### Tunnel Vision Check
- The scheduler and function-loop infrastructure is finished; do not reprove it. C1.5 was reviewed and committed as 7bf1b37a1.
- Outside-the-box route for remaining entry/no-return/no-params/nonentry restrictions: prove generic transport of opcode exclusions via exact special-source membership, rather than a new induction per predicate.
- PLAN abstraction remains sound: one aligned-block relation handled the whole function loop, and copy_phi_var rule induction handled the genuinely nonlocal shape condition.
- A fresh expert should first fix the binder typo, then check metadata reuse: dft_fn_labels_map is public in dftCorrectness; dft_fn_entry_label is in dftCorrectnessFinal, not dftCorrectness. Avoid adding a near-duplicate when deciding whether to import or derive a small shape-specific consequence.
- Do not optimize opaque-use further: dft_shape_opaque_use is verified. Most remaining work is first-block facts, invocation/label references and assembling o1_fn_shape.

### What Went Wrong
- Private Triviality lemmas in dftCorrectness are not available as exports. Used public dft_block_instruction_source plus a finite flip case analysis for unique terminator position.
- irule often strips conclusion universals: introduce the quantified instruction/index before application. Its generated antecedents can be reordered; use goal-pattern selectors rather than guessed conjunct positions.
- In opaque-use, strip_tac on existential source provenance split its disjunction early, leaving four branches. Keeping the disjunction with qx_choose_then and CONJUNCTS_THEN assume_tac kept one goal and solved the proof.
- The current failing PHI proof used an auto-generated i while quoting e. Read the live goal and rename before writing local facts.
- pure_rewrite_tac[Abbr ...] timed out; simp[NoAsms,Abbr ...] unfolded abbreviations without rewriting the FUNPOW target by its result equation.

### Ignored Signals
- gvs on both source and output bb_well_formed internals can exceed the tactic budget. Extract just nonemptiness/LAST and kill the large relation assumptions before constructor cases.
- Using a constant name step as qmatch abbreviation failed; fresh dstep worked.
- Builds sometimes report invalid checkpoints and rebuild from earlier contexts, but always progress; this is not an operational blocker.

### Strategy Adjustments
- Use dftLiftingTheory exports dft_fn_block_rel, dft_fn_wf_function, dft_fn_inst_wf, dft_fn_inst_shape, dft_fn_ir_inst_ids_subset as consumer boundaries.
- No source definitions or existing proved theorems changed. Only dftLiftingScript.sml was added and compiler helpers were inserted before the frozen final theorem.
- C1.6 verified helpers in current file: dft_shape_instruction_source, dft_shape_special_source, copy_phi_var_mono, dft_shape_copy_phi_var, opaque_use_not_flippable, dft_shape_opaque_use, dft_shape_first_rel. First_no_phi is the current failure; first_no_preds is unverified.
- Final dft_step_contract still has its original cheat, covered by C1.7. Do not edit it while C1.6 remains active.

### Oracle Feedback
- E0008 accepted: deletion/provenance relation, pseudo-filter equality and LAST transport suffice; no SSA/permutation needed. Transitivity and LIST_REL loop lifting were validated.
- C1.6's predicted difficult step held: GAS/RETPC closure is monotone by rule induction, and allowed opaque-use instructions cannot flip.

## Evidence Pointers
- episode:E0008 - C1.5 proved/reviewed, committed 7bf1b37a1
- tool_output:TO_dft_step-20261102T123913Z_m0424_t001 - clean complete dftLifting build
- tool_output:TO_dft_step-20261102T123913Z_m0426_t001 - strategist accepts C1.5
- episode:E0009 - C1.6 partial checkpoint
- tool_output:TO_dft_step-20261102T123913Z_m0447_t001 - opaque-use helpers build
- tool_output:TO_dft_step-20261102T123913Z_m0452_t001 - current first-PHI binder failure
- tool_output:TO_dft_step-20261102T123913Z_m0455_t001 - full current failing goals
