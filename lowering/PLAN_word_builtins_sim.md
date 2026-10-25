# PLAN

## Structured Components

### C1: Word builtin expression simulation
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The five dispatch branches are word-only straight-line fragments; operand composition follows the existing exprSimOps and exprSimConvert interfaces. The three names branches reduce to the same operand lowering, with the proved word-name theorem.
- Required for completion: yes

#### Summary
Prove exactly the eight frozen theorems in TASK_word_builtins_sim.md. Put all new definitions and helpers in exprSimWordBuiltinsScript.sml, and add that theory to exprSimBuiltins' ancestors. Compose left-to-right operand simulation with independently verified word arithmetic fragments. Cover operand errors and fragment assertion failures as well as successful results. Leave other builtin cheats and all protected files untouched.

#### Not to try
Do not use compile_name_sim, exprSimMain induction, or other cheated case lemmas. Do not prove expression composition separately eight times. Do not unfold run_inst_seq, source evaluation and the full expression compiler together in consumer proofs. No changes to frozen statements or expr_sim_pre/expr_sim_inv. If checked evidence refutes a frozen theorem, stop and report the counterexample and tightest non-executable repair.

#### Argument
Typing restricts AsWeiValue to unsigned integers, Floor to decimals, and modular operations to uint256 operands. The existing expression hypothesis supplies simulation of each argument at every intermediate source state; type soundness preserves expr_sim_inv and supplies word values. Preserve earlier operand values through subsequent operand fragments using their variable frame, not an assumption that evaluation is pure. Once all operands are available, the builtin fragment is straight_fresh: it preserves source-related state, old variables, allocations and memory, and either produces the source result or reverts on its RuntimeError. AsWeiValue checks unsigned multiplication overflow; Floor adjusts negative scaled integers before signed truncating division; modular addition/multiplication use full-width mathematical arithmetic before modulus; exponentiation agrees modulo 2^256. Names shortcuts have the same lowering as the generic operand sequence and use compile_name_word_sim without an induction hypothesis. StackValue lowering converts the resulting expr_sim proof to expr_vv_sim.

#### Definition design
Introduce a general builtin_result wrapper around evaluate_builtin, mapping INL v to INL (Value v) and INR err to INR (Error err). Introduce a parameterized word fragment contract: a compiler on an operand list, a source result, and a value list; its precondition is pointwise eval_operand agreement plus state relation, and its postcondition is the successful word result plus the same frames as binop_frag_def. Use a small recursive word-argument lowering sequence (parameterized by the per-argument lowering type, since dispatch uses ambient ty except AsWeiValue). Its composition invariant retains the entire already-computed operand/value prefix and the initial expr_post frames. These are proof-only abstractions; do not change production lowering or judgments. Probe nil/cons and early-error behavior before using the list interface. Unfold internals only in boundary lemmas.

#### Code structure
Create lowering/exprSimWordBuiltinsScript.sml with sections for source/lowering boundaries, word-fragment interface, operand composition, arithmetic runs, and typed application helpers. All helpers, including arithmetic lemmas, belong there. In exprSimBuiltinsScript.sml change only the ancestor list and the eight requested proofs; preserve the other cheated theorems. No edits to existing theorems elsewhere. Use holbuild only, rename1 for names, proofs under roughly 50 lines, no speculative search wrappers and no timeout increases. Audit used theorem dependencies: lower_value_word_shape and compile_binop_shape are the only permitted inherited cheats; importing a theory does not license use of its other cheated results.

### C1.1: Typed source and lowering boundaries
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Finite builtin typing cases and one-step compiler/evaluator equations; existing convert and bop boundary proofs provide the exact pattern.

#### Summary
Establish typed arities and operand/result types for the five word builtins. Expose dispatch and names lowering as operand sequences followed by their arithmetic fragment. Expose source evaluation as left-to-right argument evaluation followed by evaluate_builtin. Keep arbitrary ambient lowering ty in the interface.

#### Statement
Outputs: typed inversion lemmas for AsWeiValue, Floor, AddMod, MulMod, PowMod256; StackValue shape lemmas for their complete lowerings; lowering decomposition equations for dispatch and each names shortcut; source evaluation boundary for value arguments, with early exceptions and non-Value alternatives explicit.

#### Approach
Use well_typed_builtin_app_def and expr_sim_pre_builtin_arg to expose legal argument lists and types. Follow lower_value_convert and eval_expr_bop_cases, using one-step compile_expr_raw_def/evaluate_def expansion only here; prove names shortcuts equal the corresponding sequence of lower_value calls by reducing compile_name_vv and unwrap_value. Retain actual argument lowering types from the source equations rather than silently replacing ambient ty by expr_type.

#### Not to try
Do not assume source materialisation is identity before proving the argument is Value; do not discard early errors or infer argument arity from HD/EL alone.

### C1.2: General word fragment interface and boundary probes
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Direct abstraction of binop_frag_straight and convert_frag_straight over a pointwise list relation; no new execution principle is required.
- Dependencies: C1.1
- Checkpoint: yes

#### Summary
Define builtin_result and a word-fragment contract usable by all five arithmetic compilers. Lift straight_fresh run facts to that contract, separately for success and Revert_abort. Prove pointwise operand framing and nil/cons simplifications to validate the interface. Export conclusions matching the later composition use site.

#### Statement
Outputs: builtin_result_def; word builtin fragment contract parameterized by the compiler and source result; successful-run and runtime-error lifting lemmas using frag_exec_straight_fresh and frag_exec_straight_fresh_abort; list operand preservation under variable frames; computation probes for empty/singleton/cons operand lists.

#### Approach
Use the exact frames and freshness premises of binop_frag_def, replacing its two operand equalities with LIST_REL eval_operand/value agreement. Prove the list framing helper by list induction from eval_operand_frame; isolate drop_fresh invariance at this boundary so consumers apply the lifting theorem directly.

#### Not to try
Do not copy the large qspecl_then instantiations of binop_frag_straight into each arithmetic proof. Make successful and abort lifting separate helpers with directly matching conclusions.

### C1.3: Left-to-right word operand composition
- Kind: `proof_group`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: The recursion is structural on the argument list. A transitive frame boundary removes the nonlocal-memory bookkeeping from induction, and an invariant parameter supplies operand simulation at intermediate source states.
- Progress transition: `refinement`
- Carries progress/evidence from: E0004

#### Progress note
Retain the built computation/shape prefix unchanged. New descendants own only the missing semantic and execution interfaces; no continuity certification is claimed for them.

#### Summary
Keep lower_word_args and its three existing lemmas unchanged. Factor the three preservation clauses of expr_post into a composable frame. Use an arbitrary source-state invariant I and per-member hypotheses valid at every I-state. Prove list execution once, then compose with word_builtin_frag through a generic lowering-decomposition premise. No saved-prefix parameter is needed: the tail frame preserves the head operand.

#### Not to try
Do not copy compile_bop_sim's repeated manual instantiation blocks or expand expr_post in every induction branch. Do not introduce a saved-prefix accumulator: old-variable preservation already keeps the head through the tail. Do not assume operands are pure or that source accounts are unchanged. builtin_result must use the final argument state's accounts.

#### Argument
Induct on arguments, generalizing source and target states and compiler endpoints. In the successful cons case, the head simulation produces a word operand and the invariant for the tail; tail simulation preserves that operand because it is not fresh at the tail's starting compile state. Compose frames using preservation of scope domains and local_region_frame. If either the head or tail raises, only the executed prefix matters and frag_exec_exit_prefix accounts for all remaining code. At the builtin boundary, eval_expr_builtin_cases separates an operand exception from a completed value list; only the latter invokes word_builtin_frag. The final pure fragment preserves all memory, so the accumulated list frame supplies precisely expr_post's nonlocal-memory clause.

#### Definition design
Use wb_frame cenv es sa s0 s for exactly the old-variable, allocation, and nonlocal-memory conjuncts of expr_post (not a stronger all-memory frame). Use wb_args_post for final state relation, LIST_REL word operands, and wb_frame. Source-state admissibility is a separate predicate parameterized by I; it must quantify over all I-states, not just the original state. Define the exit predicate for list results by case: INL vs maps to (\r. F), INR exc maps to expr_exit (INR exc). Probe reflexivity/transitivity, nil execution, and success/error evaluator inversion before the induction. Existing lower_word_args_shape remains the only list compiler-shape interface.

#### Code structure
All additions go in lowering/exprSimWordBuiltinsScript.sml after the existing lower_word_args_shape, in order: frames, source list boundary, list execution, builtin consumer. Add no edits to protected theories. Keep each proof under roughly 50 lines by giving the success and exception composition branches named lemmas within their owning leaf; these are explicitly included outputs, not an extra work queue.

### C1.3.1: Composable expression frame boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: The predicate is exactly three existing expr_post conjuncts; transitivity uses the already-proved local_region_frame and monotone freshness/id bounds.

#### Summary
Extract the preservation clauses verbatim into wb_frame. Prove reflexivity and transitivity with the required scope and freshness assumptions. Provide expr_post projection and word-result reconstruction so later proofs do not unfold expr_post.

#### Statement
Define:
wb_frame cenv es sa s0 s <=>
 (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
 (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
   (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) ==>
   mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory).

Outputs: wb_frame_refl; wb_frame_vars (first conjunct projection); expr_post_frame; expr_post_state; expr_post_word_operand (using expr_val_rel_word's word/evaluated-type hypotheses).

wb_frame_trans:
 stmt_state_rel func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
 MAP FDOM es.scopes = MAP FDOM es1.scopes /\
 sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
 wb_frame cenv es sa s0 t /\ wb_frame cenv es1 s1 t u
 ==> wb_frame cenv es sa s0 u.

wb_frame_readonly_tail:
 wb_frame cenv es sa s0 t /\ sa.cs_next_var <= s1.cs_next_var /\
 (!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==> lookup_var z u = SOME w) /\
 (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\ u.vs_memory = t.vs_memory
 ==> wb_frame cenv es sa s0 u.

expr_post_word_intro:
 stmt_state_rel func cenv cx es' s /\ is_word_type (expr_type e) /\ word_value v /\
 eval_operand op s = SOME (val_to_w256 v) /\ wb_frame cenv es sa s0 s
 ==> expr_post func cenv cx e es sa sb s0 es' v op s.

#### Approach
Prove the independent projection and reconstruction lemmas by unfolding only at this boundary. For transitivity, transport each initial excluded local region backwards from es1/t with local_region_frame, then apply the second memory frame followed by the first; use id monotonicity for the second frame's allocation bound.

#### Not to try
Do not replace nonlocal memory preservation by whole-memory equality; operands may modify local memory. Do not omit the initial state relation or scope-domain equality from frame transitivity.

### C1.3.2: Invariant-indexed source list evaluation boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: A structural list induction exposes evaluate's left-to-right bind; successful expression outcomes are restricted to Value by the admissibility hypothesis.

#### Summary
Define the member contract at arbitrary invariant states. Expose successful/error evaluation of nil and cons without repeatedly unfolding the interpreter. Show successful lists preserve I and produce word values. Separate source evaluation facts from fragment execution.

#### Statement
Define wb_args_ready ctx func cenv cx arg_ty I args as:
 !e es. MEM e args /\ I es ==>
   expr_sim ctx func cenv cx (arg_ty e) e es /\
   is_word_type (expr_type e) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
   (!res es'. eval_expr cx e es = (res,es') ==> expr_res_ok res) /\
   (!tv es'. eval_expr cx e es = (INL tv,es') ==>
       ?v. tv = Value v /\ word_value v /\ I es').

Outputs: ready projections for head and tail; eval_exprs_nil; ready-cons inversion with exactly these alternatives:
 (head raises INR exc, and list result/state are that exception/state), or
 (head returns Value v at es1, I es1, word_value v, and tail evaluates to (rr,es'), with list result equal to INL (v::vs) when rr=INL vs, or INR exc when rr=INR exc).
 The inversion assumes wb_args_ready ... (e::args), I es and eval_exprs cx (e::args) es = (rr0,es').

wb_args_eval_success:
 wb_args_ready ctx func cenv cx arg_ty I args /\ I es /\
 eval_exprs cx args es = (INL vs,es') ==>
 I es' /\ EVERY word_value vs /\ LENGTH vs = LENGTH args.

Define wb_args_exit rr = case rr of INL vs => (\r. F) | INR exc => expr_exit (INR exc).

#### Approach
Inspect the eval_exprs equations in evaluate_def to prove the cons inversion under the no-nonvalue-success clause. Induct on args for preservation, using readiness at es1 for the tail; do not require invariant preservation on exceptional outcomes, since there is no continuation there.

#### Not to try
Do not state member simulation only at the original es. Do not equate expr_res_ok on expression results with a predicate on value-list results: the sum types differ. Avoid introducing a new evaluator.

### C1.3.3: Execute lower_word_args with a compositional list postcondition
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: After frame and evaluator boundaries, this is a nil/cons induction with a single success sequencing case and prefix-exit cases.
- Dependencies: C1.3.1, C1.3.2
- Checkpoint: yes

#### Summary
Define the list postcondition using the shared frame. Prove a named nil execution probe and head/tail sequencing boundaries. Prove the general list simulation by induction using lower_word_args_cons and lower_word_args_shape. Preserve each earlier operand through the next fragment using word_operands_frame or eval_operand_frame.

#### Statement
Define wb_args_post func cenv cx es sa s0 es' xs vs s <=>
 stmt_state_rel func cenv cx es' s /\
 LIST_REL (\x v. eval_operand x s = SOME (val_to_w256 v)) xs vs /\
 wb_frame cenv es sa s0 s.

Define wb_args_shape cenv arg_ty args as precisely the universally quantified per-member hypothesis of lower_word_args_shape (including cs_next_id monotonicity and no Label operands).

lower_word_args_sim:
 wb_args_ready ctx func cenv cx arg_ty I args /\ I es /\
 wb_args_shape cenv arg_ty args /\
 lower_word_args cenv arg_ty args sa = (xs,sb) /\
 eval_exprs cx args es = (rr,es') /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa
 ==>
 frag_exec ctx sa sb
   (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
   (\s. ?vs. rr = INL vs /\ wb_args_post func cenv cx es sa s0 es' xs vs s)
   (wb_args_exit rr).

Additional owned outputs: nil execution probe; a direct application boundary for expr_sim (same premises as expr_sim_def, conclusion its frag_exec) so consumers use drule/irule rather than manual REWRITE_RULE/qspecl blocks; success-cons sequencing and exception-prefix helpers as needed to keep the induction proof below 50 lines.

#### Approach
Generalize all endpoints and initial states before list induction. Obtain code containment/reservations for subfragments from shape and fn_has_code_mid; use eval_expr_preserves_scopes_dom for the successful head, and wb_frame_trans for the postcondition. Separate false initial state relation, head error, tail error, and both-success branches into small named boundary proofs if needed.

#### Not to try
Do not inline frag_exec_def or expand frame internals in the induction. Do not use large manually instantiated copies of expr_sim_def. The target post is false on list errors, so frag_exec_exit_prefix handles unexecuted suffix code without any simulation of that suffix at an exceptional source state.

### C1.3.4: Generic builtin application consumer of list simulation
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: The existing eval_expr_builtin_cases and word_builtin_frag interfaces match the list execution output; only one sequencing and final frame reconstruction remain.
- Dependencies: C1.3.3
- Checkpoint: yes

#### Summary
Provide a generic compile_word_builtin_sim theorem independent of the five concrete builtin implementations. Accept a compiler-decomposition premise rather than unfold the dispatcher in the consumer. Use the final argument state's accounts in builtin_result. Both generic and names-specialized clients can discharge the same member-simulation contract by their own permitted routes.

#### Statement
compile_word_builtin_sim:
 Assume bt <> Len, builtin_args_length_ok bt (LENGTH args), is_word_type ann,
 wb_args_ready ctx func cenv cx arg_ty I args, I es,
 wb_args_shape cenv arg_ty args;
 assume !sa sb op. lower_value compile_expr cenv ty (Builtin ann bt args) sa = (op,sb) ==>
   ?xs sm. lower_word_args cenv arg_ty args sa = (xs,sm) /\ code xs sm = (op,sb);
 assume !xs sm sb op. code xs sm = (op,sb) ==> cs_extends sm sb;
 assume !vs es'. eval_exprs cx args es = (INL vs,es') ==>
   word_builtin_frag ctx func cenv cx code
     (builtin_result cx es'.accounts ann bt (MAP expr_type args) vs) vs es';
 conclude expr_sim ctx func cenv cx ty (Builtin ann bt args) es.

Also provide a list-post-plus-fragment-post boundary concluding expr_post for Builtin ann bt args, with premises wb_args_post, sa.cs_next_var <= sm.cs_next_var, is_word_type ann, and exactly the successful postcondition conjuncts from word_builtin_frag at sm. This boundary uses wb_frame_readonly_tail and expr_post_word_intro.

#### Approach
Unfold expr_sim once and split eval_expr_builtin_cases. Operand exceptions use lower_word_args_sim followed by frag_exec_exit_prefix. Completed operands use frag_exec_then with the word_builtin_frag premise; derive its operand freshness premise from lower_word_args_shape and reconstruct the final expr_post through the dedicated boundary, not by expanding frames.

#### Not to try
Do not demand expr_res_ok for every builtin_result in the universal fragment hypothesis: word_builtin_frag itself is conditional on that premise, and the current outer expression simulation supplies it. Do not specialize this theorem to one arity or depend on compile_name_sim; names clients must eventually use the permitted word-name route. Concrete lowering/typing adapters remain owned by existing sibling components, not this subtree.

### C1.4: Modular arithmetic fragments
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: ADDMOD/MULMOD have the exact source integer-modulus semantics, with a preceding zero assertion; EXP requires only the definition-level modular exponentiation bridge.
- Dependencies: C1.2

#### Summary
Prove straight_fresh and run correctness for compile_addmod, compile_mulmod and compile_pow_mod256. Distinguish zero modulus reversion from nonzero modulus success. Relate EXP to the source modexp without expanding exponentiation at concrete large powers. Package each as the common word-fragment contract.

#### Statement
Outputs: straight_fresh facts for all three compilers; full-width addmod/mulmod run lemmas for arbitrary uint256 words with zero/nonzero modulus cases; word_exp/modexp bridge and exponentiation run lemma; three typed word-fragment correctness results.

#### Approach
Reduce compile_addmod_def and compile_mulmod_def into ASSERT followed by one pure ternary instruction; use venom addmod_def/mulmod_def, not wrapped word addition/multiplication. For exponentiation inspect word_exp and vfmExecution modexp definitions and reuse any existing bridge found before adding one; if needed prove the accumulator modular-power invariant using modexp's own recursion. Lift the runs with C1.2.

#### Not to try
Do not assert (a+b) as a word before modulus: ADDMOD intentionally uses the unbounded sum. Do not compute large exponents by EVAL. Check the exponentiation bridge signature before citing it; none has yet been identified.

### C1.5: Unsigned denomination scaling fragment
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: The overflow test is characterized by elementary quotient/remainder bounds with positive bounded scale; all denomination constants satisfy these bounds.
- Dependencies: C1.2

#### Summary
Prove the multiplication overflow criterion with an abstract positive modulus and scale. Specialize to 256-bit words and denomination_multiplier. Handle zero input, overflow, and the scale-one no-code case explicitly. Package compile_as_wei_value_int with is_signed = F as a word fragment matching evaluate_as_wei_value.

#### Statement
Arithmetic interface: for natural N,x,m with 0 < N, x < N, 0 < m and m < N, ((x*m MOD N) DIV x = m \/ x = 0) <=> x*m < N. Outputs also include denomination multiplier bounds/source agreement, straight_fresh compile_as_wei_value_int, and success/revert run and fragment lemmas.

#### Approach
Split x=0; for x>0, if x*m<N remove MOD and divide the product, while if x*m>=N the remainder is less than x*m and hence its quotient is strictly below m. Reduce the emitted MUL/Div/EQ/ISZERO/OR/ASSERT sequence using this lemma and unsigned encoding; separate scale=1 before the instruction proof.

#### Not to try
Do not cover signed or decimal AsWeiValue branches not admitted by typing. Do not replace the overflow criterion by a claim about signed multiplication.

### C1.6: Decimal floor fragment
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: Decimal range is safely within signed 256 bits, making the negative adjustment non-overflowing; remaining equality is Euclidean floor versus truncating division.
- Dependencies: C1.2

#### Summary
Establish the signed division identity for positive divisors and representable adjusted inputs. Derive the required margin from the actual decimal value bounds. Prove the SLT/SUB/select/SDIV run and its straight_fresh property. Package the result as the Floor word fragment.

#### Statement
Outputs: general integer floor/truncation identity, with x<0 selecting x-(d-1) and x>=0 selecting x, for d>0; decimal bound specialization at d=10000000000; compile_floor straight_fresh and successful run theorem matching IntV (i / decimal_scale); typed Floor fragment correctness.

#### Approach
Split on the sign of i, use quotient/remainder arithmetic to relate truncation of the adjusted negative numerator to integer division, and prove signed representability before rewriting w2i/i2w. Reduce compile_select once in the run proof and keep its bit-level behavior separate from the arithmetic identity.

#### Not to try
Do not claim the adjustment works for all signed words: the minimum signed input may wrap. The run theorem needs a representability margin, supplied by decimal typing.

### C1.7: Typed consumer interface, builtin applications, and eight frozen proofs
- Kind: `proof`
- Risk: 2
- Work priority: 70
- Work units: 8
- Rationale: Floor has checked integration evidence. The new consumer packages precisely its existing readiness and successful-list typing steps around compile_word_builtin_sim; no new semantic invariant is needed.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0015

#### Progress note
E0015 is partial-progress evidence for the Floor integration, not certification of this still unfinished leaf. Preserve its successful argument while extracting its repeated interface. All frozen outputs remain unchanged.

#### Summary
Factor a typed consumer of compile_word_builtin_sim in exprSimWordBuiltinsScript.sml. Refactor the successful Floor integration to use it, then finish the other four typed builtin integrations. Obtain name-operand simulations only through compile_name_word_sim. Finish exactly the eight frozen proofs in exprSimBuiltinsScript.sml and build both requested theories.

#### Description
Owned outputs remain the typed integrations for AsWeiValue, Floor, AddMod, MulMod and PowMod256, word-name adapters, and the eight exact public theorems. Put all new helpers and typed integrations in exprSimWordBuiltinsScript.sml; only the eight target proof bodies and necessary Ancestors change belong in exprSimBuiltinsScript.sml. Preserve unrelated cheated builtins and protected files. This interface intentionally requires the fragment for every typed value list and final state; existing typed fragments have that generality, and this avoids exporting evaluator plumbing to consumers.

#### Statement
Add compile_typed_word_builtin_sim with the following interface (universally quantify all free variables):
```
expr_sim_pre cenv cx env (Builtin ann bt args) es /\
EVERY (\e. word_value_type (expr_type e) /\ expr_sim_ok cenv e) args /\
bt <> Len /\ builtin_args_length_ok bt (LENGTH args) /\ is_word_type ann /\
(!sa sb op. lower_value compile_expr cenv ty (Builtin ann bt args) sa = (op,sb) ==>
  ?xs sm. lower_word_args cenv arg_ty args sa = (xs,sm) /\ code xs sm = (op,sb)) /\
(!xs. straight_fresh (code xs)) /\
(!vs es'. LIST_REL
   (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v)
   args vs ==>
   word_builtin_frag ctx func cenv cx code
     (builtin_result cx es'.accounts ann bt (MAP expr_type args) vs) vs es')
==> expr_sim ctx func cenv cx ty (Builtin ann bt args) es
```
Also add typed_builtin_args_values: the first two premises above together with `eval_exprs cx args es = (INL vs,es')` imply the displayed LIST_REL. These are general adapters, not builtin-specific facts.

#### Approach
First prove typed_builtin_args_values by word_args_values_typed: EVERY_MEM supplies word typing, expr_sim_pre_builtin_arg supplies the child precondition at any state satisfying expr_sim_inv, and expr_sim_pre_def supplies the initial invariant. Prove compile_typed_word_builtin_sim by typed_word_args_ready and compile_word_builtin_sim, choosing Inv = expr_sim_inv cenv cx env; use typed_builtin_args_values for its final premise, and unfold straight_fresh_def/cs_extends_def only here to discharge extension (as in the successful Floor proof).
Refactor compile_floor_typed_sim so that after typing inversion it applies the new consumer with arg_ty = (\e. ty) and code = (\xs. compile_floor (EL 0 xs) 10000000000); retain lower_value_floor for decomposition and straight_fresh_floor for freshness, and invert LIST_REL/value_has_type before compile_floor_word_frag. Repeat this boundary pattern for the remaining builtins using their existing lowering and fragment lemmas; modular cases use compile_modular_typed_frag and compile_pow_mod256_typed_frag. Public proofs derive argument simulations from expr_sim_below, invert typing for arity/word types, and use the existing stack bridge; name proofs obtain word-local simulation from compile_name_word_sim. Build exprSimBuiltinsTheory and exprSimMainTheory and audit theorem dependencies for forbidden cheats.

#### Not to try
Do not copy Floor's lines 1377–1387 and 1395–1404 into every integration. Do not expose Inv/readiness/list-evaluation preservation obligations to each typed consumer. Do not use compile_name_sim or compile_name_other_sim. Avoid new builtin-specific copies of the general list typing adapter, manual ASSUME/MATCH_MP theorem plumbing, or broad search over unfolded evaluator/compiler definitions. Keep proofs under roughly 50 lines, no TRY/ORELSE search wrappers, and never increase tactic timeouts. If a fragment genuinely requires evaluation information beyond typed values, report the exact mismatch rather than weakening frozen statements.

### C1.8: Task build and dependency audit
- Kind: `build_probe`
- Risk: 1
- Work priority: 70
- Work units: 2
- Rationale: Mechanical verification of frozen statements, source scope, dependency provenance and the requested targets.
- Dependencies: C1.7
- Checkpoint: yes

#### Summary
Run holbuild -j4 build exprSimBuiltinsTheory exprSimMainTheory. Audit the eight proofs and new helpers for cheats and prohibited inherited axioms. Verify frozen statements and protected files are unchanged. Confirm proof lengths and tactic timing respect the task requirements.

#### Approach
Inspect theorem provenance rather than treating absence of new cheat text as sufficient: only lower_value_word_shape and compile_binop_shape may contribute cheats to these outputs. Keep unrelated builtin cheats as requested, report them as out-of-scope rather than attempting cleanup; use a larger whole-build timeout if needed, never raise the tactic timeout.

#### Not to try
A successful exprSimMain build alone does not certify the eight proofs' dependency discipline. Do not remove or repair unrelated cheated theorems.
