# DOSSIER: word_builtins_sim

PLAN: `lowering/PLAN_word_builtins_sim.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0002 | Review C1.1 and proceed with C1.2 fragment interface. Owner points to builtinProps compile_floor_correct/compile_select_correct and run helpers. |
| C1.2 | proved |  | E0003 | Review then commit. C1.3 list composition can consume word_builtin_frag and explicit eval_exprs_cons_cases. |
| C1.3 | progressed | other | E0004 | Specify the shared list execution postcondition and continuation/builtin composition interface; then prove frames and execution by list induction. |
| C1.3.1 | proved |  | E0006 | Review and commit; next source readiness/list evaluation boundary C1.3.2. |
| C1.3.2 | proved |  | E0007 | Review, commit, begin C1.3.3 lower_word_args execution. |
| C1.3.3 | proved |  | E0009 |  |
| C1.3.4 | proved |  | E0010 |  |
| C1.4 | proved |  | E0005 | Review closure and commit clean helper theory progress (also contains prior C1.3 lower_word_args prefix). Then scheduled frame/source-list components. |
| C1.5 | proved |  | E0012 |  |
| C1.6 | proved |  | E0013 |  |
| C1.7 | proved |  | E0017 | Review closure, commit stable integration; C1.8 inherited dependency audit remains. |
| C1.8 | proved |  | E0018 | Review final audit and complete task; committed source checkpoint bb3d1a92. |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0002`
- blocker: 
- actual effort: 1 sessions, 6 msgs, 96 steps, 95 tools, 23 holbuild, 7,614,913 tok (7,600,996 in, 13,917 out, 7,472,128 cached), 803.4s, $1.1441188
- next: Review C1.1 and proceed with C1.2 fragment interface. Owner points to builtinProps compile_floor_correct/compile_select_correct and run helpers.

### Attempts / Evidence

- `E0001` (progressed, other, actual effort: 1 sessions, 4 msgs, 61 steps, 60 tools, 13 holbuild, 4,220,886 tok (4,214,717 in, 6,169 out, 4,131,712 cached), 472.5s, $0.6408712)
  - Typed builtin inversion, general source eval_exprs/evaluate_builtin boundary, unary compiler boundary and lower_value decompositions -> New exprSimWordBuiltinsTheory builds with no cheats. word_builtin_unary_types and word_builtin_modular_types establish typing. eval_expr_builtin_cases retains accounts and early exceptions. compile_expr_unary_builtin handles all unary builtins; lower_value_floor and lower_value_as_wei_value retain actual lowering types. (`TO_word_builtins_sim-20261025T190154Z_m0060_t001`)
- `E0002` (proved, , actual effort: 1 sessions, 6 msgs, 96 steps, 95 tools, 23 holbuild, 7,614,913 tok (7,600,996 in, 13,917 out, 7,472,128 cached), 803.4s, $1.1441188)
  - Prove typed inversion, eval_expr_builtin_cases and eval_exprs_cons_cases; expose generic dispatch and names shortcuts; extract word lowering sequences and StackValue shape -> exprSimWordBuiltinsTheory builds cheat-free. Generalized ternary and binary modular dispatch lemmas eliminate the names/non-names distinction at the lowering boundary, so lower_value decompositions now cover names too. All statements retain ambient ty; AsWeiValue uses expr_type e. Source boundaries explicitly preserve early exceptions and non-Value possibilities. (`TO_word_builtins_sim-20261025T190154Z_m0097_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0097_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0003`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 41 steps, 40 tools, 13 holbuild, 4,933,270 tok (4,928,068 in, 5,202 out, 4,871,552 cached), 361.5s, $0.6522072
- next: Review then commit. C1.3 list composition can consume word_builtin_frag and explicit eval_exprs_cons_cases.

### Attempts / Evidence

- `E0003` (proved, , actual effort: 1 sessions, 3 msgs, 41 steps, 40 tools, 13 holbuild, 4,933,270 tok (4,928,068 in, 5,202 out, 4,871,552 cached), 361.5s, $0.6522072)
  - List-indexed fragment contract, operand drop_fresh/frame lemmas, separate success/revert lifting, constant and operand no-code probes -> New theory builds clean. Lifting uses ho_match_mp_tac on the existing fresh execution interfaces with two/three small witnesses, no copied long instantiation lists. Projection probe handles singleton or arbitrary nonempty operand lists; constant probe covers empty and arbitrary lists. Framing requires non-Label operands explicitly, as eval_operand_frame does. (`TO_word_builtins_sim-20261025T190154Z_m0143_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0143_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `progressed`
- diagnosis: `other`
- latest episode: `E0004`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 10 steps, 9 tools, 2 holbuild, 575,411 tok (573,932 in, 1,479 out, 548,864 cached), 84.1s, $0.1198124
- next: Specify the shared list execution postcondition and continuation/builtin composition interface; then prove frames and execution by list induction.

### Attempts / Evidence

- `E0004` (progressed, other, actual effort: 1 sessions, 1 msgs, 10 steps, 9 tools, 2 holbuild, 575,411 tok (573,932 in, 1,479 out, 548,864 cached), 84.1s, $0.1198124)
  - Define lower_word_args cenv arg_ty as recursive left-to-right lower_value sequence; prove nil/cons equations and shape by list induction. -> All three computation/shape lemmas build cleanly. Shape carries cs_extends, variable/id monotonicity, list length and every operand's final nonfresh/nonlabel property. (`TO_word_builtins_sim-20261025T190154Z_m0168_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0168_t001` (use `read_tool_output` for exact output)

## C1.3.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0006`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 16 steps, 15 tools, 6 holbuild, 1,877,880 tok (1,875,441 in, 2,439 out, 1,853,952 cached), 134.1s, $0.2527632
- next: Review and commit; next source readiness/list evaluation boundary C1.3.2.

### Attempts / Evidence

- `E0006` (proved, , actual effort: 1 sessions, 1 msgs, 16 steps, 15 tools, 6 holbuild, 1,877,880 tok (1,875,441 in, 2,439 out, 1,853,952 cached), 134.1s, $0.2527632)
  - Extract wb_frame from expr_post; prove projections, word introduction, readonly-tail and transitivity. -> All requested boundary theorems build cleanly. Frame transitivity transports excluded local regions using local_region_frame; no stronger memory preservation assumption added. Consumers can now avoid expr_post unfolding. (`TO_word_builtins_sim-20261025T190154Z_m0272_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0272_t001` (use `read_tool_output` for exact output)

## C1.3.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 9 steps, 8 tools, 3 holbuild, 1,146,553 tok (1,144,967 in, 1,586 out, 1,132,160 cached), 61.9s, $0.1546900
- next: Review, commit, begin C1.3.3 lower_word_args execution.

### Attempts / Evidence

- `E0007` (proved, , actual effort: 1 sessions, 1 msgs, 9 steps, 8 tools, 3 holbuild, 1,146,553 tok (1,144,967 in, 1,586 out, 1,132,160 cached), 61.9s, $0.1546900)
  - Define wb_args_ready at all invariant states; prove head/tail projections, nil eval, ready-cons inversion and list success preservation; define wb_args_exit. -> Complete source boundary builds cleanly. Cons inversion eliminates non-Value successes using readiness, success induction preserves invariant, word values and list length. Exit definition annotates INR's unused success type to avoid an unbound polymorphic variable. (`TO_word_builtins_sim-20261025T190154Z_m0287_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0287_t001` (use `read_tool_output` for exact output)

## C1.3.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0009`
- blocker: 
- actual effort: 1 sessions, 4 msgs, 58 steps, 57 tools, 18 holbuild, 4,186,956 tok (4,181,869 in, 5,087 out, 4,101,760 cached), 410.9s, $0.6212640

### Attempts / Evidence

- `E0008` (progressed, other, actual effort: 1 sessions, 1 msgs, 7 steps, 6 tools, 1 holbuild, 956,655 tok (954,925 in, 1,730 out, 846,336 cached), 54.0s, $0.3191116)
  - Added wb_args_post/wb_args_shape, tail shape, shape application wrapper, expr_sim application, nil execution probe and cons post composition boundary. -> Build passed definitions and wb_args_shape_tail but times out in lower_word_args_shape_ready's metis_tac[lower_word_args_shape]. This is a routine higher-order matching issue: wrapper should directly apply/drule the existing shape theorem after introducing premises, rather than run unconstrained metis. Following expr_sim_apply, lower_word_args_nil_sim and wb_args_post_cons are unverified text, not yet reached. (`TO_word_builtins_sim-20261025T190154Z_m0297_t001`)
- `E0009` (proved, , actual effort: 1 sessions, 4 msgs, 58 steps, 57 tools, 18 holbuild, 4,186,956 tok (4,181,869 in, 5,087 out, 4,101,760 cached), 410.9s, $0.6212640)
  - Direct shape application; expr_sim_apply and nil probes; compositional cons post and no-exit sequencing; generalized list induction. -> All owned outputs build clean. Induction handles false initial relation, head exception via exit prefix, and tail success/error via pointwise sequencing and weakening. Proof is 44 lines, no internal frag_exec unfolding or copied assumptions. (`TO_word_builtins_sim-20261025T190154Z_m0360_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0360_t001` (use `read_tool_output` for exact output)

## C1.3.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0010`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 8 holbuild, 2,112,269 tok (2,110,205 in, 2,064 out, 2,080,000 cached), 167.3s, $0.2890500

### Attempts / Evidence

- `E0010` (proved, , actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 8 holbuild, 2,112,269 tok (2,110,205 in, 2,064 out, 2,080,000 cached), 167.3s, $0.2890500)
  - Generic consumer using lower_word_args_sim, evaluator inversion, word_builtin_frag, dedicated expr_post_word_builtin frame boundary. -> Both boundary and compile_word_builtin_sim build clean; generic theorem proof 28 lines with head exceptions exited by prefix, successful arguments sequenced with the fragment. No arity specialization. (`TO_word_builtins_sim-20261025T190154Z_m0386_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0386_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0005`
- blocker: 
- actual effort: 1 sessions, 5 msgs, 77 steps, 76 tools, 17 holbuild, 6,796,835 tok (6,788,602 in, 8,233 out, 6,699,904 cached), 624.2s, $0.9297164
- next: Review closure and commit clean helper theory progress (also contains prior C1.3 lower_word_args prefix). Then scheduled frame/source-list components.

### Attempts / Evidence

- `E0005` (proved, , actual effort: 1 sessions, 5 msgs, 77 steps, 76 tools, 17 holbuild, 6,796,835 tok (6,788,602 in, 8,233 out, 6,699,904 cached), 624.2s, $0.9297164)
  - Uniform compile_modular_run for ADDMOD/MULMOD after ASSERT and compile_pow_mod256_run for EXP; straight_fresh facts for all three. -> Runs proved at arbitrary operand words, with zero modulus reverting and nonzero modulus using unbounded natural sum/product. Staged Once unfolding prevents step_inst_base simplifier blowup. (`TO_word_builtins_sim-20261025T190154Z_m0204_t001`, `TO_word_builtins_sim-20261025T190154Z_m0208_t001`)
  - Use vfmExecutionTheory.modexp_exp to prove word_exp_modexp, package canonical-word fragment contracts, and derive typed contracts with uint_value_word_rep. -> All fragment contracts build, including reverts for zero modulus. The existing modexp_exp bridge made new exponentiation induction unnecessary. Final helper target clean. (`TO_word_builtins_sim-20261025T190154Z_m0215_t001`, `TO_word_builtins_sim-20261025T190154Z_m0249_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0249_t001` (use `read_tool_output` for exact output)

## C1.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0012`
- blocker: 
- actual effort: 1 sessions, 4 msgs, 57 steps, 56 tools, 17 holbuild, 3,787,417 tok (3,782,916 in, 4,501 out, 3,704,960 cached), 506.5s, $0.5714180

### Attempts / Evidence

- `E0011` (progressed, other, actual effort: 1 sessions, 4 msgs, 61 steps, 60 tools, 15 holbuild, 7,509,117 tok (7,503,066 in, 6,051 out, 7,329,536 cached), 473.4s, $1.1405236)
  - Proved natural mul_mod_div_no_overflow, word analogue, denomination bounds and straight_fresh_as_wei_value_int. -> All built clean before beginning run proof. Word bridge removes quotient MOD using DIV_LESS_EQ; no new arithmetic assumptions needed. (`TO_word_builtins_sim-20261025T190154Z_m0424_t001`)
  - Staged instruction run proof and general eval_operand_update_not_fresh boundary. -> Run verified through MUL, Div, EQ and ISZERO. Last checked state contains OR and ASSERT plus nested updates. Latest edit adds OR/ASSERT reduction but is unbuilt; still ends FAIL_TAC. Run theorem incomplete, source unchanged except task helper theory. (`TO_word_builtins_sim-20261025T190154Z_m0449_t001`, `TO_word_builtins_sim-20261025T190154Z_m0450_t001`)
- `E0012` (proved, , actual effort: 1 sessions, 4 msgs, 57 steps, 56 tools, 17 holbuild, 3,787,417 tok (3,782,916 in, 4,501 out, 3,704,960 cached), 506.5s, $0.5714180)
  - Finish staged OR/ASSERT run using word_mul_div_no_overflow and WORD_OR_CLAUSES. -> compile_as_wei_value_int_run builds for success and overflow, including scale-one. (`TO_word_builtins_sim-20261025T190154Z_m0471_t001`)
  - Prove unsigned source agreement by naturalizing nonnegative input, then package success/revert via word_builtin_frag boundaries. -> evaluate_as_wei_value_uint and compile_as_wei_value_word_frag build clean. Uses no cheated theorems. (`TO_word_builtins_sim-20261025T190154Z_m0492_t001`, `TO_word_builtins_sim-20261025T190154Z_m0512_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0512_t001` (use `read_tool_output` for exact output)

## C1.6

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0013`
- blocker: 
- actual effort: 1 sessions, 4 msgs, 65 steps, 64 tools, 19 holbuild, 6,554,926 tok (6,548,775 in, 6,151 out, 6,468,224 cached), 638.7s, $0.8694344

### Attempts / Evidence

- `E0013` (proved, , actual effort: 1 sessions, 4 msgs, 65 steps, 64 tools, 19 holbuild, 6,554,926 tok (6,548,775 in, 6,151 out, 6,468,224 cached), 638.7s, $0.8694344)
  - Prove floor/truncating quotient identity by INT_DIVISION and INT_QUOT_UNIQUE with adjusted remainder. -> int_floor_via_quot proved for every positive integer divisor, including x=0. (`TO_word_builtins_sim-20261025T190154Z_m0531_t001`)
  - Stage floor instruction run; prove representable word arithmetic bridge and specialize decimal bounds; package fragment. -> straight_fresh_floor, compile_floor_run, word_floor_via_quot, decimal_floor_word and compile_floor_word_frag build clean. Arithmetic boundary uses existing proved word_i2w_sub from arithmeticProps; no new cheats. (`TO_word_builtins_sim-20261025T190154Z_m0583_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0583_t001` (use `read_tool_output` for exact output)

## C1.7

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0017`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 4 steps, 3 tools, 1 holbuild, 211,600 tok (211,313 in, 287 out, 204,416 cached), 14.8s, $0.0371056
- next: Review closure, commit stable integration; C1.8 inherited dependency audit remains.

### Attempts / Evidence

- `E0014` (progressed, other, actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 7 holbuild, 3,465,857 tok (3,462,852 in, 3,005 out, 3,420,800 cached), 266.1s, $0.4562340)
  - Add typed_word_args_ready adapter from expr_sim_pre and per-argument expr_sim_ok/word types to wb_args_ready and wb_args_shape. -> Build clean. Uses only allowed lower_value_word_shape inherited cheat and proved public pre/result boundaries. EVERY_MEM handled by rewriting, not higher-order metis. (`TO_word_builtins_sim-20261025T190154Z_m0608_t001`)
  - Prove general successful word-argument list value typing by induction and expr_sim_pre_word_result. -> word_args_values_typed builds clean and supplies LIST_REL evaluate_type/value_has_type for arithmetic typed fragments. All eight final proofs and typed application instantiations remain. (`TO_word_builtins_sim-20261025T190154Z_m0615_t001`)
- `E0015` (progressed, other, actual effort: 1 sessions, 3 msgs, 48 steps, 47 tools, 15 holbuild, 3,081,724 tok (3,078,329 in, 3,395 out, 3,010,688 cached), 347.5s, $0.4703008)
  - Instantiate compile_word_builtin_sim for Floor using typed_word_args_ready, lower_value_floor, word_args_values_typed and compile_floor_word_frag. -> compile_floor_typed_sim builds clean in 38 lines. No frozen proof yet changed. Reveals repeated per-builtin readiness, state-invariant and list-typing plumbing that could be shared before four more instantiations. (`TO_word_builtins_sim-20261025T190154Z_m0668_t001`)
- `E0016` (progressed, other, actual effort: 1 sessions, 9 msgs, 118 steps, 117 tools, 27 holbuild, 12,993,755 tok (12,980,093 in, 13,662 out, 12,732,544 cached), 950.7s, $1.9049724)
  - Extract strategist-approved typed_builtin_args_values and compile_typed_word_builtin_sim; refactor Floor and instantiate wei, modular pair, pow. -> All typed consumers build clean; shared composition isolates invariant/readiness/evaluator plumbing. Uint width bounds come from successful evaluate_type in fragment typing, not just is_uint_type. (`TO_word_builtins_sim-20261025T190154Z_m0716_t001`)
  - Add word_name_sim_ok from well_typed_Name_lookup and compile_name_word_sim; general public induction and names adapters; replace all eight frozen cheats unchanged. -> exprSimBuiltinsTheory and exprSimMainTheory both build clean. Diff confirms only ancestor plus eight proof bodies changed in builtins. New helper source contains no cheat/TRY/ORELSE/hh. Final inherited dependency/oracle audit and commit still pending. (`TO_word_builtins_sim-20261025T190154Z_m0772_t001`, `TO_word_builtins_sim-20261025T190154Z_m0773_t001`, `TO_word_builtins_sim-20261025T190154Z_m0785_t001`)
- `E0017` (proved, , actual effort: 1 sessions, 1 msgs, 4 steps, 3 tools, 1 holbuild, 211,600 tok (211,313 in, 287 out, 204,416 cached), 14.8s, $0.0371056)
  - Reverify completed typed consumer integrations and eight exact frozen public proofs against both requested build targets; inspect public-file diff. -> Both targets build clean. Public changes are ancestor plus eight proof bodies only; typed consumers and names route completed in helper theory. (`TO_word_builtins_sim-20261025T190154Z_m0793_t001`, `TO_word_builtins_sim-20261025T190154Z_m0795_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0793_t001` (use `read_tool_output` for exact output)
- `TO_word_builtins_sim-20261025T190154Z_m0795_t001` (use `read_tool_output` for exact output)

## C1.8

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0018`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 39 steps, 38 tools, 6 holbuild, 2,718,354 tok (2,714,315 in, 4,039 out, 2,658,944 cached), 266.3s, $0.4170264
- next: Review final audit and complete task; committed source checkpoint bb3d1a92.

### Attempts / Evidence

- `E0018` (proved, , actual effort: 1 sessions, 2 msgs, 39 steps, 38 tools, 6 holbuild, 2,718,354 tok (2,714,315 in, 4,039 out, 2,658,944 cached), 266.3s, $0.4170264)
  - Run temporary kernel-tag/dependency diagnostic over all eight outputs and all helper exports, stopping at the permitted shape axioms; inspect anonymous library dependencies' Theory.dat files for cheat tags. -> Only lower_value_word_shape contributes inherited cheat provenance. No forbidden exprSim dependency found; unresolved anonymous dependencies belong to generated datatype/library facts, with project library Theory.dat files checked cheat-free. No unexpected oracle tags. (`TO_word_builtins_sim-20261025T190154Z_m0817_t001`, `TO_word_builtins_sim-20261025T190154Z_m0821_t001`, `TO_word_builtins_sim-20261025T190154Z_m0823_t001`, `TO_word_builtins_sim-20261025T190154Z_m0824_t001`, `TO_word_builtins_sim-20261025T190154Z_m0825_t001`, `TO_word_builtins_sim-20261025T190154Z_m0826_t001`, `TO_word_builtins_sim-20261025T190154Z_m0832_t001`)
  - Audit proof length and prohibited tactic text, frozen-statement diff, remove temporary diagnostics and rebuild final source. -> Longest helper proof 46 lines. No cheat/TRY/ORELSE/hh or programmatic theorem creation in helpers. Eight statements unchanged, unrelated builtins preserved, final both-target build clean; diagnostic code removed. (`TO_word_builtins_sim-20261025T190154Z_m0827_t001`, `TO_word_builtins_sim-20261025T190154Z_m0832_t001`, `TO_word_builtins_sim-20261025T190154Z_m0795_t001`, `TO_word_builtins_sim-20261025T190154Z_m0837_t001`)

### Evidence refs

- `TO_word_builtins_sim-20261025T190154Z_m0832_t001` (use `read_tool_output` for exact output)
- `TO_word_builtins_sim-20261025T190154Z_m0837_t001` (use `read_tool_output` for exact output)
