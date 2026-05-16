# STATE_type_system_rewrite
Updated: 2026-05-16

## Cursor
- component: C5
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Investigate whether env_context_consistent can derive get_module_code cx src = SOME code when FLOOKUP env.toplevel_vtypes (src,id) = SOME vt. If not, either strengthen env_context_consistent or prove per-target-type bridge lemmas for assign_target_assignable_context. Start with ScopedVar/ImmutableVar (trivial), then TopLevelVar (the hard case), then TupleTargetV. After bridge lemmas, update Assign branch (line 799+) to use them.
- expected_goal_shape: assign_target_assignable_context cx gv st2 from target_runtime_typed + runtime_consistent + well_typed_atarget
- verify_with: holbuild(targets=['vyperTypeStmtSoundnessTheory'])

## If This Fails
- If TopLevelVar bridge is impossible from current invariant, escalate to plan_oracle: env_context_consistent may need strengthening with FLOOKUP env.toplevel_vtypes (src,id) = SOME vt => get_module_code cx src = SOME code

## Do Not Retry
- Derive assign_target_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) st from target_runtime_typed + runtime_consistent alone: IMPOSSIBLE: target_runtime_typed gives only FLOOKUP env.toplevel_vtypes = SOME vt. env_context_consistent uses get_module_code as antecedent condition only. No existing invariant derives get_module_code from FLOOKUP toplevel_vtypes.
  - evidence: source:semantics/prop/vyperTypeExprSoundnessScript.sml:258-259
  - evidence: source:semantics/prop/vyperTypeSystemScript.sml:713-731
- Use assign_target_TopLevelVar_no_type_error_imp_get_module_code contrapositive to derive no-TypeError for TopLevelVar: Contrapositive gives NOT get_module_code => TypeError. Cant use this to prove no-TypeError because it is consistent with TypeError occurring when get_module_code = NONE
  - evidence: source:semantics/prop/vyperTypeAssignSoundnessScript.sml:407-419
- EVERY (assign_target_assignable_context cx st) gvs partial application: Wrong argument order: assign_target_assignable_context takes cx gv st, not cx st gv. Must use lambda form EVERY (\gv. assign_target_assignable_context cx gv st) gvs
  - evidence: tool_output:TO_type_system_rewrite-20260515T192259Z_m13043_t002

## Reflection
### Tunnel Vision Check
- Spent too much time reading definitions serially instead of identifying the CORE GAP: assign_target_assignable_context for TopLevelVar needs get_module_code which CANNOT be derived from target_runtime_typed or runtime_consistent. Should have identified this gap immediately and either found a workaround or escalated.
- The PLAN C5.2 correctly identifies deriving assign_target_assignable_context as the key bridge, but underestimates the TopLevelVar gap. The existing invariants provide get_module_code facts only conditionally (as antecedents), never as unconditional conclusions.
- Alternative approach not tried: Could the Assign branch proof avoid assign_target_no_type_error entirely for the TypeError contradiction case, and instead directly unfold assign_target_def for each gv constructor and use case-specific reasoning? This might bypass the assignable_context requirement.

### What Went Wrong
- C4 completed successfully (just lambda form fix). C5 analysis revealed a fundamental gap: assign_target_assignable_context for TopLevelVar requires get_module_code cx src = SOME code + find_var_decl_by_num facts, but env_context_consistent only uses get_module_code as a CONDITION in implications (line 718: FLOOKUP bare_globals ... /\ get_module_code cx src = SOME ts => ...), never derives it as a conclusion.
- target_runtime_typed for TopLevelVar only provides FLOOKUP env.toplevel_vtypes = SOME vt (line 259 of vyperTypeExprSoundnessScript.sml). It does NOT provide get_module_code or declaration/slot facts.
- assign_target_TopLevelVar_no_type_error_imp_get_module_code (line 407 of vyperTypeAssignSoundnessScript) uses a CONTRAPOSITIVE but can't help prove no-TypeError - it only says if no TypeError then get_module_code exists

### Ignored Signals
- LEARNING L0425 explicitly states the circular dependency: runtime_consistent does NOT provide get_module_code for TopLevelVar. Should have focused on this gap immediately instead of reading more definitions.
- LEARNING L0423 suggests using assign_target_preserves_state_well_typed_mutual directly for preservation (weaker premises). For no-TypeError, a similar approach may be needed - use a weaker no-TypeError theorem or a direct execution-based proof.

### Strategy Adjustments
- For C5, prove bridge lemmas for ScopedVar (possible via eval_target_assignable + env_scopes_consistent) and ImmutableVar (trivially T) first, then tackle TopLevelVar.
- TopLevelVar approach options: (A) Add FLOOKUP env.toplevel_vtypes => get_module_code to env_context_consistent or a consequence lemma, (B) Extract get_module_code from the execution result in statement branches via case analysis, (C) Prove a direct no-TypeError for TopLevelVar that doesn't need assignable_context but instead does execution-level reasoning inside the statement proof.
- Start with the easy cases (ScopedVar, ImmutableVar, TupleTargetV componentwise) to make partial progress, then resolve the TopLevelVar gap.

### Oracle Feedback
- PLAN C5.2 correctly identifies the assignable_context bridge as essential, but the dependency on get_module_code for TopLevelVar is a genuine architectural gap not addressed by the current invariants. This may need either definition repair (add to env_context_consistent) or a different proof strategy for the TopLevelVar case.
- The PLAN says If a lemma needs to assume a top-level slot/layout fact not derivable from runtime consistency and target typing, thats a failure sign requiring escalation. This IS that failure sign for TopLevelVar.

## Evidence Pointers
- source:semantics/prop/vyperTypeSystemScript.sml:713-731 - env_context_consistent_def: get_module_code only appears as antecedent condition, never as conclusion
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:258-259 - location_runtime_typed TopLevelVar: only FLOOKUP env.toplevel_vtypes, no get_module_code
- source:semantics/prop/vyperTypeStatePreservationScript.sml:949-966 - assign_target_assignable_context_def: TopLevelVar case needs get_module_code + find_var_decl_by_num + evaluate_type/lookup_var_slot IS_SOME
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:798-810 - Assign branch failing proof tries drule assign_target_no_type_error but cant derive assign_target_assignable_context cx gv st2
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13050_t002 - Build failure showing exact goal shape at line 801
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13049_t001 - C4 theorems all build clean
