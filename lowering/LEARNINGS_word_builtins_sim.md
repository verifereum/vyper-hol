# LEARNINGS_word_builtins_sim

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C1.3' tags=names,dispatch,lower_value,ambient-type
shape: Word builtin compilation on arbitrary expressions, including all-name shortcuts
pattern: compile_ternary_modular_dispatch and compile_binary_modular_dispatch equate the shortcuts with ordinary dispatcher compilation at arbitrary ambient ty. lower_value_ternary_modular and lower_value_pow_mod256 therefore need no names exclusion; use the same operand composition for shortcut and generic cases.
works_when: unspecified
evidence:
- episode:E0002
- source:lowering/exprSimWordBuiltinsScript.sml

## L0002 scope='C1.2' tags=frag_exec,higher-order,straight_fresh,type-instantiation
shape: Lifting a list-indexed run contract to frag_exec with predicate-valued pre/postconditions
pattern: ho_match_mp_tac frag_exec_straight_fresh matches the LIST_REL precondition and frames directly; choose code xs and false abort predicate. For abort-only lifting first instantiate frag_exec_straight_fresh_abort's result type to operand, then choose code xs, op and equality-to-Revert_abort. word_operands_drop_fresh discharges predicate invariance.
works_when: unspecified
evidence:
- episode:E0003
- source:lowering/exprSimWordBuiltinsScript.sml

## L0003 scope='C1.4' tags=modexp,word_exp,EXP
shape: Relating EVM EXP to source PowMod256
pattern: vfmExecutionTheory.modexp_exp reduces accumulator modexp to modular exponentiation. Together with wordsTheory.word_exp_def it proves word_exp a b = n2w (modexp (w2n a) (w2n b) (dimword (:256)) 1) by simp; no recursive modexp proof is needed.
works_when: unspecified
evidence:
- source:lowering/exprSimWordBuiltinsScript.sml:word_exp_modexp
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0215_t001

## L0004 scope='C1.4' tags=run_inst_seq,step_inst_base,Once,timeout
shape: Small straight-line instruction execution proof times out under broad simplification
pattern: After computing emitted_insts, alternate simp[Once run_inst_seq_def] and simp[Once step_inst_base_def, mk_inst_def, exec_pureN_def], resolving conditions between instructions. Avoid unfolding the whole step dispatcher repeatedly in one simp.
works_when: unspecified
evidence:
- source:lowering/exprSimWordBuiltinsScript.sml:compile_modular_run
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0204_t001

## L0005 scope='C1.5' tags=conditional_rewrite,not_fresh_at,eval_operand,update_var
shape: Conditional rewrite has compile-state variable only in premises, absent from conclusion.
pattern: Specialize that state once (qspec_then `sa` assume_tac eval_operand_update_not_fresh); the remaining universally quantified assumption then rewrites each update under sa's freshness hypotheses. Unspecialized simp cannot infer sa.
works_when: unspecified
evidence:
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0443_t001
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0447_t001

## L0006 scope='C1.7' tags=EVERY_MEM,higher_order,metis
shape: EVERY (lambda e. P e /\ Q e) args and MEM e args
pattern: Use gvs[EVERY_MEM] then first_x_assum drule and simp[] to extract the conjunctive property. Metis over EVERY_MEM can be expensive because its predicate argument is higher-order.
works_when: unspecified
evidence:
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0602_t001
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0608_t001

## L0007 scope='C1.7' tags=strip_tac,disjunction,THEN1,branching
shape: rpt strip_tac splits constructor alternatives before a proof containing >-
pattern: Parenthesize the entire continuation after the splitting tactic so each alternative gets its own complete subgoal-management chain. Otherwise >- closes only the first global goal while later >> acts on unfinished sibling goals.
works_when: unspecified
evidence:
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0694_t001
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0697_t001
