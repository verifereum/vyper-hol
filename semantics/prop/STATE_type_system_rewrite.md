# STATE_type_system_rewrite
Updated: 2026-05-17

## Cursor
- component: C7
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Read vyperTypeStmtSoundnessScript.sml cheat sections (lines 935-945, 1600-1700, 1720-1810) using small targeted reads. Then replace cheats starting with simplest IH-consumption branches: Targets_nil (1648), Exprs_nil (1802), Exprs_cons (1806), Log (941). For each: expand evaluate_def, split INL/INR, use IH conjuncts.
- expected_goal_shape: Various eval_all_type_sound_mutual branches consuming existing IH conjuncts for stmts/exprs/targets
- verify_with: holbuild(targets=['vyperTypeStmtSoundnessTheory'], tactic_timeout=30, timeout=300)

## If This Fails
- If a branch is hard, use FAIL_TAC probe to inspect goal state. If it needs C1 builtin theorems, skip and try next. If decomposition wrong, close_episode and escalate via plan_oracle.

## Do Not Retry
- none recorded

## Reflection
### Tunnel Vision Check
- Got stuck in read_file loop for >100 calls trying to read vyperTypeStmtSoundnessScript.sml - should have used much smaller limit/offset and accepted partial reads
- Should have focused on editing/building instead of exhaustively reading the entire interpreter file
- Could have used grep more effectively to find evaluator patterns instead of trying to read the whole file

### What Went Wrong
- Massive context waste from read_file loop - repeated identical reads at offset 245 returned 'identical params' errors, compounded by auto-retries
- Never actually read the cheat sections of vyperTypeStmtSoundnessScript.sml properly - kept trying to start from line 245 and got stuck

### Ignored Signals
- The file has 1954 lines - should have read it in chunks with different offsets, not tried to re-read the same offset repeatedly

### Strategy Adjustments
- Read files in small targeted chunks (30-50 lines) at the exact line numbers needed, not large reads from the beginning
- Focus on the simplest cheats first (IH consumption) to build momentum before tackling harder branches
- Use grep to find relevant theorems/definitions instead of reading entire source files

### Oracle Feedback
- none recorded

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17746_t008 - holbuild passes with cheats
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17733_t001 - grep showing all 34 cheat locations
