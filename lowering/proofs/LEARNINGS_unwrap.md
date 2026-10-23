# LEARNINGS_unwrap

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C1' tags=shape_step,higher_order,BETA_RULE,ho_match_mp_tac
shape: Applying shape_step rules with lambda pre/post invariants
pattern: Use ho_match_mp_tac for fresh_label, fresh_var, frame, pure_pre and emission-under interfaces; BETA_TAC after bind continuation introduction. For primitive emit_op with explicitly fixed R, BETA_RULE(Q.SPECL [internal,LP,R] shape_step_emit_op) preserves syntactic EVERY structure unlike aggressive simplification.
works_when: unspecified
evidence:
- episode:E0001
- episode:E0006
- source:lowering/proofs/loweringShapePropsScript.sml

## L0002 scope='C1.3' tags=Resume,suspend,markerLib
shape: One named suspension used for multiple branches
pattern: Resume goal is a resumption connective; split with qualified markerLib.RESUME_TAC, then parenthesize the entire common tactic to avoid >- applying across unrelated branches. Unqualified RESUME_TAC is not exported.
works_when: unspecified
evidence:
- tool_output:TO_unwrap-20261023T092756Z_m0149_t001
- tool_output:TO_unwrap-20261023T092756Z_m0150_t001
