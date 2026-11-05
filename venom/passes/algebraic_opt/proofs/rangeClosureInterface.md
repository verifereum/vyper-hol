# Reachable range closure interface audit

Scope: C1.I.3.RANGE.CLOSURE_INTERFACE. This document is a premise ledger, not a proved closure theorem.

## Proposed consumer statement

With wf_function fn, wf_ssa fn, fn_inst_wf fn, EVERY label_positions_ok (fn_insts fn), s0.vs_inst_idx = 0, s0.vs_prev_bb = NONE, fn_entry_label fn = SOME s0.vs_current_bb, every function output absent in s0, and ao_source_prefix ctx fn s0 n k phase s, conclude

```
in_range_state
  (range_at_inst (range_analyze fn) s.vs_current_bb
    (if phase then 0 else s.vs_inst_idx)) s.vs_vars
```

An evaluated-operand range corollary then follows from ao_range_eval_operand_sound. Do not add global dfg_sound or dfg_block_local premises.

## Cache meaning

* dfAnalyzeWidenDefsScript.sml:41-60: df_widen_at, boundary and entry return their bottom argument for a missing outer finite-map lookup. Here bottom is NONE. A stored NONE is indistinguishable at these interfaces from a missing outer key.
* rangeAnalysisDefsScript.sml:247-260: range_unwrap NONE = FEMPTY, while join treats NONE as abstract bottom/unprocessed. Thus consumer soundness of an unwrapped cache cannot establish cache presence.
* rangeAnalysisDefsScript.sml:280-288: range_transfer_opt converts even NONE to SOME (range_evaluate_inst ... FEMPTY). Hence positive instruction indices have a structural SOME argument independent of dynamic DFG soundness.
* rangeAnalysisProofsScript.sml:276-281: range_sound NONE s is T. The checked ao_range_phis_sound converts both cache cases correctly; it does not infer presence.

## Transition ledger

The source-prefix constructors are algebraicOptReachabilityProofsScript.sml:54-78.

| Transition | Available boundary | Result/index | Remaining structural interface |
|---|---|---|---|
| initial T s0 | ao_range_at_inst_initial_sound (algebraicOptRangeProofs:1146) | sound at index 0, indeed any index in initial vars | entry DFS membership and entry lookup for later induction |
| T -> F atomic PHIs | ao_range_phis_sound (algebraicOptRangeConditionProofs:455) | sound at phi_prefix_length, exactly index assigned by prefix rule | current label = block label; DFS membership; eval_phis preserves label |
| F -> F ordinary | ao_range_step_sound (algebraicOptRangeProofs:1156) | sound at SUC old index | get_instruction implies valid index; successful nonterminator preserves current label; index update preserves vars |
| F -> T terminator | ao_source_trace_branch_refine_sound + range_refined_boundary_entry_sound | edge refinement of sound boundary is sound at destination entry | final-position-to-boundary absorption; successor DFS/pred membership; range_entry_eq |

For each F->T event obtain a replay trace with HD initial state using ao_source_prefix_has_trace (algebraicOptTraceProofs:69). The trace keeps initial output absence available to TAKEN_EDGE. No new producer invariant is needed.

## Exit cache bridge (not yet packaged as a theorem)

At a terminator idx = PRE (LENGTH instructions), so one additional successful transfer yields soundness at LENGTH via ao_range_step_sound. The block is nonempty. assertElimProofsScript.sml:1018-1059 range_widen_at_some provides SOME exit_rs for 0 < n <= LENGTH on a DFS block. It needs wf_function, block membership and ALL_DISTINCT fn_labels (the latter supplied by wf_function).

assertElimProofsScript.sml:865 range_fixpoint_absorbs yields boundary = join boundary exit. With exit SOME, range_join_opt's equations rule out boundary NONE. range_join_opt_some_sound_right transports exit soundness to boundary soundness. The existing range_sound_at_successor proof explicitly does this at lines 1258-1287; its structural fragment can be reused without adopting that theorem's global dfg_sound/dfg_block_local premises.

Feed the resulting arbitrary boundary_rs to TAKEN_EDGE, then range_refined_boundary_entry_sound (assertElimProofs:1171-1207). This latter theorem already owns join/widen absorption; do not duplicate it. range_entry_eq (assertElimProofs:743-749) converts destination entry to index zero. No SOME witness is required at initialization, post-PHI zero indices, or destination entry; only the predecessor exit bridge requires one, and positive-index transfer supplies it.

## CFG/index facts

algebraicOptTraceProofs:322-347 ao_source_step_exit_cfg proves fn_cfg_edge for successful nonhalting terminators, including self-loops. CFG successor closure (analysisSimProps.cfg_dfs_pre_succs_closed) and cfg_edge_symmetry_uncond are used by existing range_sound_at_successor:1266-1298. A closure induction should carry DFS membership and phase-sensitive index bounds. T indices are analysis zero even on return from a terminator; do not query t.vs_inst_idx there. F indices are after PHIs or incremented ordinary steps. A trace replay bridges prefix induction to TAKEN_EDGE.

## Trust audit and limitations

Source searches found no cheat in variable_range, dataflow, or assertElimProofsScript.sml. Candidate shared facts range_widen_at_some, range_entry_eq, range_fixpoint_absorbs, range_refined_boundary_entry_sound and eval_phis_range_sound have explicit proofs rather than admissions. The accepted local boundaries build without CHEAT warnings in algebraicOptRangeConditionProofsTheory. Do not use range_sound_at_successor wholesale: its advertised global DFG premises are unsupported in this task.

A full transitive kernel-tag certification has NOT been completed: neither .holbuild/gen nor searched public theorem-index locations supplied Theory.txt files in this run. Source audit is not a substitute for the final no-oracle check. This is a remaining certification item, not a mathematical premise to assume.

## Finite remaining obligations for strategist

1. Package the positive-exit-cache/boundary-soundness bridge, using the structural fragment above, without global DFG assumptions.
2. Package or reuse CFG DFS membership and phase-sensitive prefix structural facts (including valid observation indices and label preservation).
3. Authorize the phase-indexed prefix induction only after these interfaces are checked; reuse replay traces for TAKEN_EDGE.
4. Obtain public generated theorem indexes or equivalent checked tag output for transitive trust certification before final integration.
