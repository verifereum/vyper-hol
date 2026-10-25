# PLAN

## Structured Components

### C1: Frozen ABI fragment correctness
- Kind: `proof_group`
- Risk: 3
- Work priority: 10
- Work units: 0
- Rationale: Derived from child component C1.4 risk 3. Instruction/frame component too broad; scratch preservation through memory-only operations needs a projection boundary to avoid timeout from unfolding full state records and alloca invariants.
- Required for completion: yes

#### Summary
Prove exactly the four conjuncts of compile_abi_encode_frag, without changing the frozen definitions. Separate layout algebra, scratch/frame reasoning, instruction effects, and recursive branch proofs. Use compile_abi_encode_child_ind for the final mutual theorem and frag_exec_loop for both array loops. Leave the old decoder and single-block encoder cheats untouched.

#### Not to try
Do not reuse compile_abi_encode_to_buf_correct: its single-block contract is known false. Do not assume fresh_vars_wrt, empty scratch maps, or globally fresh initial SSA variables; the contract guarantees only preservation of not_fresh_at operands. Do not unfold all four compiler definitions inside a monolithic semantic proof. Do not repair the frozen theorem if a counterexample emerges: escalate with a checked instance and report the tightest fix only as a proposal.

#### Argument
Induct along compile_abi_encode_child_ind, keeping all semantic arguments universally quantified. Each recursive call reads a subvalue of the original source and writes a subregion of the designated output; all such regions are below lo, while scratch allocations are above lo. Fragment instruction-id intervals split at intermediate compile states, so unused allocation credit can be reserved for later code while earlier scratch cells remain available for repeated loop iterations. At a loop header k records the number of encoded elements: the first k heads and tails are correct, the source and outer scratch cells are preserved, and the counter cells contain k and the current tail end. The variant is LENGTH vs - k. At exit these prefix facts become the full ABI encoding. The complex-elements case uses the same head/tail decomposition without a runtime loop. Compose effects using frag_exec_seq/conseq and package the exact enc_frame only at branch boundaries.

#### Definition design
Keep abi_enc_plan(s), frag_ids, enc_scratch, enc_frame, enc_pre and frag_exec_loop unchanged. Introduce only proof-local prefix/layout and memory-effect predicates if they reduce repeated unfolding. A memory-effect interface must describe padded byte observations, effects fields, old variables, and allocation preservation; the existing copy theorem alone does not supply every enc_frame conjunct. Prefix invariants must be position-independent (unchanged by jump_to), include source preservation and allocation budget for the entire enclosing fragment, and quantify over arbitrary pre-existing allocated scratch cells. Test these interfaces with reflexivity, interval splitting, zero iterations, and one-element head/tail append before writing recursive consumers.

#### Code structure
Put new results after the frozen definitions and before compile_abi_encode_frag in lowering/abiEncoderPropsScript.sml; earlier existing lemmas remain unchanged. If infrastructure becomes large, move only independent general memory/fragment helpers to a new lowering script and register it using holproject.toml conventions, without creating a cyclic dependency on these frozen definitions. No edits under semantics/, venom/, or lowering/defs/. Keep individual proofs around 50 lines or less by naming semantic boundary lemmas, not by hiding long tactic chains in ML. Use holbuild only; do not raise tactic timeouts or use TRY/ORELSE around search.

### C1.1: Plan inversion and ABI head/tail layout
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: These are rule-inversion and structural list/value facts; no execution reasoning is involved.

#### Summary
Expose the information carried by each encoding-plan constructor. Relate element head sizes and memory strides to evaluated types. Supply ABI head/tail append facts in the form used by complex elements and array prefixes.

#### Statement
Outputs: inversion lemmas for abi_enc_plan and abi_enc_plans; static-plan classification (~is_dynamic (vyper_to_abi_type env ty) /\ abi_enc_plan env ty ei ==> ei = AbiPrimWord \/ ?n. ei = AbiCopy n); SUM of plan memory strides = SUM (MAP type_memory_size tvs) under the LIST_REL evaluation hypothesis; SUM of head sizes = the ABI head-length sum; static enc length = type_memory_size tv under the task's evaluation/typing/conversion hypotheses. Provide head/tail prefix decompositions of enc_tuple d 0 types values [] [] and the dynamic-array DROP 32 encoding, including empty-list equations and tail-length subtraction identities.

#### Approach
Use abi_enc_plan rule inversion for dispatch and list induction for paired types/plans/values. Inspect the existing ABI length and append theorem signatures before adding helpers, reusing enc_has_static_length, enc_tuple_append, enc_tuple_static or val_in_memory_static_abi only where their hypotheses match. State append facts with a current tail offset and separate head and tail byte lists, so recursive consumers do not manipulate reverse accumulators.

#### Not to try
Do not assume abi_enc_plan is the unique output of type_to_abi_enc_info: its copy rule deliberately allows multiple plans for static types. Do not infer memory-size bounds from evaluate_type alone.

### C1.10: Mutual theorem assembly and task audit
- Kind: `proof`
- Risk: 2
- Work priority: 100
- Work units: 3
- Rationale: All semantic branches have matching closure lemmas; the remaining induction and contract/build checks are mechanical.
- Dependencies: C1.7, C1.8, C1.9
- Checkpoint: yes

#### Summary
Apply the compiler's mutual induction theorem and discharge each branch with its boundary lemma. Preserve the frozen theorem verbatim. Build and audit only the task theorem and newly added helpers for cheats and proof-quality requirements.

#### Statement
compile_abi_encode_frag exactly as frozen in lowering/TASK_abi_encode_frag.md, with no changed quantifiers, premises, postconditions or supporting definitions.

#### Approach
Use compile_abi_encode_child_ind, generalizing all semantic parameters before induction; select branches explicitly and apply the matching closure results. Run holbuild -j4 build abiEncoderPropsTheory and inspect the new theorem/helper dependency chain, distinguishing the permitted pre-existing cheats and frozen frag_exec_loop from any newly introduced admissions. Check no duplicate helpers, no forbidden edits, no search fallback combinators, and small proof/tactic times.

#### Not to try
A passing build with a cheat in a newly introduced helper does not meet completion. If the induction shape differs from expectations, improve the branch-helper interface rather than introducing long manual MATCH_MP/CONJ plumbing.

### C1.2: Typed source footprints, subvalue extraction and region preservation
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: value_has_type_def rules out mismatched primitive types and supplies exactly the lengths, key bounds and recursive hypotheses required by val_wf_def. All aggregate auxiliary predicates align recursively. Bytes/string cases require only ceiling-to-word arithmetic. Existing checked memory boundaries handle preservation once this bridge is supplied.
- Progress transition: `refinement`
- Carries progress/evidence from: E0003

#### Progress note
Retain the nine checked boundary helpers from E0003 unchanged. That episode reports partial progress, not a completed obligation; no continuity certification is requested. Complete the missing typing bridge and frame/source preservation in this same leaf.

#### Summary
Retain enc_pre_bounds, regions_disjoint_subregions, enc_scratch_alloca_bound/outside_disjoint, tuple_in_memory_append/EL, elems_in_memory_EL, mem_bytes_at_pointwise and val_in_memory_pointwise. Prove value_has_type implies val_wf without an evaluate_type premise. Package typed source preservation across an enc_frame so consumers do not unfold the frame. Reuse existing static-array and struct extraction lemmas rather than duplicate them. Check the abiEncoderPropsTheory build and leave the frozen theorem and definitions unchanged.

#### Description
Exact extraction scope remaining: the already proved tuple_in_memory_EL and elems_in_memory_EL supply indexed tuple/homogeneous elements. Use val_in_memory_dynarray to enter the element region at src+32; use val_in_memory_sarray together with kvs_in_memory_lookup for present keys and the existing default clause for absent keys; use fields_in_memory_tuple to expose struct fields as a tuple. These existing facts are the extraction interface and need no new wrappers unless a consumer demonstrably needs a missing semantic conclusion. Region containment uses regions_disjoint_subregions and type_memory_size_def; do not invent a general source extraction framework. Put the typing bridge, its local mutual helper/arithmetic fact, and the two preservation boundaries near the current Source and region boundaries section in lowering/abiEncoderPropsScript.sml. Each proof must remain short under the task limit; split the local arithmetic or recursive interface lemmas rather than expanding large tactic chains.

#### Statement
New required outputs:
1. `!tv v. value_has_type tv v ==> val_wf tv v`.
2. A typed pointwise corollary: `value_has_type tv v /\ val_in_memory tv v src mem /\ (!a. src <= a /\ a < src + type_memory_size tv ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 mem') ==> val_in_memory tv v src mem'`.
3. A frame boundary: `enc_frame st st' lo top outs s0 s /\ value_has_type tv v /\ val_in_memory tv v src s0.vs_memory /\ src + type_memory_size tv <= lo /\ EVERY (regions_disjoint (src,type_memory_size tv)) outs ==> val_in_memory tv v src s.vs_memory`.
For output 1 use a local simultaneous strengthening with `values_have_types tvs vs ==> tuple_val_wf vs tvs`, `sparse_has_type tv n kvs ==> kvs_val_wf kvs tv n`, `all_have_type tv vs ==> elems_val_wf vs tv`, and `struct_has_type ftypes fields ==> fields_val_wf fields ftypes`. Add the local arithmetic fact `n <= 32 * word_size n` if no equivalent exported lemma is found.

#### Approach
Prove the typing bridge by recursion-matching induction on value_has_type_def and its four mutual auxiliary predicates; simplify val_wf_def and type_memory_size_def in each matching branch. For bytes and strings use word_size n = (n+31) DIV 32 and quotient/remainder arithmetic to prove the ceiling bound, then combine with LENGTH <= n; sparse typing supplies both k<n and typed stored values, and defaults require no new premise because kvs_val_wf checks stored entries only. Derive typed pointwise preservation from the existing val_in_memory_pointwise; for frame preservation establish one-byte agreement using output disjointness and the final enc_scratch lower bound on every fragment-owned cell, then apply that corollary (reverse equality orientation as needed).

#### Not to try
Do not prove val_wf from val_in_memory alone or drop wellformedness from memory agreement: mismatched or oversized values invalidate that route. Do not add evaluate_type unless an actual counterexample to the stronger typing bridge is found; every value_has_type constructor already determines the required layout. Do not prove defaults typed for this bridge: sparse val_wf requires only stored keys and values. Do not unfold enc_frame repeatedly in recursive encoder consumers, duplicate existing extraction lemmas, or add wrapper proofs solely to restate their conclusions. Do not alter any frozen definition, theorem statement, semantics file or encoder definition.

### C1.3: Qualified operand preservation and reserved-credit frame calculus
- Kind: `proof_group`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: The Label failure is an omitted hypothesis in an auxiliary interface, not a counterexample to the target. Explicit label equality and a reserved-credit split give direct definitional and finite-set proofs.
- Progress transition: `refinement`
- Carries progress/evidence from: E0006

#### Progress note
Retain frag_ids_finite, frag_ids_same, frag_ids_split, frag_ids_disjoint and enc_frame_refl unchanged. E0006 establishes partial progress only; the new leaves require their own proofs.

#### Summary
Preserve the five checked interval/reflexivity helpers without duplicating them. Operand preservation requires explicit label-map preservation. Scratch splitting reserves the budget of untouched ids rather than discarding it. Frame composition receives restored whole-fragment scratch as an explicit premise.

#### Approach
Complete the three interface leaves below, then expose them to downstream consumers. Consumers should use the boundary lemmas rather than unfold enc_frame repeatedly.

#### Not to try
Do not assert arbitrary operand preservation from enc_frame alone. Do not compose local enc_scratch facts at the same top and assume they imply the union budget. Do not weaken target operand quantification to exclude Label.

#### Argument
The frame controls old variables but not label operands, so arbitrary operand transport combines the frame with equality of vs_labels. For disjoint id sets I and J, the missing allocation count of their union is the sum of their missing counts. Reserving 32 times the missing J count by reducing the local top lets an I-fragment run without consuming J's budget. Since allocation entries at J are unchanged, the same reserved amount restores whole-fragment scratch afterward. Composition of byte frames uses preservation of all previously allocated cells to transfer final scratch exclusion back to intermediate scratch exclusion.

#### Definition design
Do not change enc_frame, enc_pre or enc_scratch. No new runtime predicate is needed. Use an arithmetic reserve expressed as 32 * CARD {i | i IN J /\ FLOOKUP s0.vs_allocas i = NONE}. Keep label equality as a separate conjunct in internal execution postconditions; it is discharged by actual instruction semantics, never inferred from enc_frame. Whole-fragment scratch is an explicit composition boundary, supplied by reserved-credit restoration.

#### Code structure
Place all helpers in the existing scratch/frame calculus section of lowering/abiEncoderPropsScript.sml. Keep existing five helpers verbatim. Each proof stays below approximately 50 lines; extract finite-set arithmetic facts locally if needed. No changes in semantics/, venom/, lowering/defs/, or frozen statements.

### C1.3.1: Operand transport with explicit label preservation
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: Constructor case analysis on operands isolates exactly the missing Label premise.

#### Summary
Prove an operand transport theorem qualified by label-map equality. The Var case uses the frame and the explicit freshness premise. The Label case uses the added equality, not search.

#### Statement
enc_frame st st' lo top outs s0 s /\
s.vs_labels = s0.vs_labels /\
(!x. op = Var x ==> not_fresh_at st x) /\
eval_operand op s0 = SOME w
==> eval_operand op s = SOME w

#### Approach
Case split op and simplify eval_operand_def. Extract only the variable preservation conjunct of enc_frame for Var; rewrite labels directly for Label. Document the required separate label-equality conjunct for internal consumer postconditions.

#### Not to try
Do not retry metis on the Label goal without label equality. The frozen frame cannot prove it.

### C1.3.2: Disjoint scratch budget restriction and restoration
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: Missing-id sets partition over disjoint finite sets; unchanged suffix lookups keep the reserve constant, and natural subtraction is justified by the original budget.
- Checkpoint: yes

#### Summary
Provide a finite-set missing-count partition helper. Restrict union scratch to a prefix with suffix credit subtracted from top. Restore union scratch after a prefix execution that leaves suffix allocation entries unchanged. This works for repeated loop allocations as well as newly allocated cells.

#### Statement
Write M K s for {i | i IN K /\ FLOOKUP s.vs_allocas i = NONE} below (notation only; a definition is optional).

1. FINITE I /\ FINITE J /\ DISJOINT I J ==> CARD (M (I UNION J) s) = CARD (M I s) + CARD (M J s).

2. FINITE I /\ FINITE J /\ DISJOINT I J /\ enc_scratch (I UNION J) lo top s ==> enc_scratch I lo (top - 32 * CARD (M J s)) s.

3. FINITE I /\ FINITE J /\ DISJOINT I J /\ enc_scratch (I UNION J) lo top s0 /\ (!i. i IN J ==> FLOOKUP s.vs_allocas i = FLOOKUP s0.vs_allocas i) /\ enc_scratch I lo (top - 32 * CARD (M J s0)) s ==> enc_scratch (I UNION J) lo top s.

#### Approach
Prove the cardinal identity by partitioning M over UNION and proving disjointness of the two subsets. For restriction, obtain reserve <= top from the original budget before subtraction arithmetic. For restoration, J lookups give both equality of missing sets and the required lo/size bounds for allocated J entries; I supplies alloca_inv and frontier bounds.

#### Not to try
Do not use a constant 32 * CARD J reserve: already allocated cells need no credit. Do not restore union scratch from unchanged frontier or separate same-top scratch facts; these omit the combined missing-id budget.

### C1.3.3: Frame weakening and sequential composition boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Each frame conjunct composes directly once monotone freshness, interval inclusion, and final whole-fragment scratch are explicit.
- Dependencies: C1.3.2

#### Summary
Prove output-list weakening and sequential frame composition. Composition keeps a single global lo/top and accepts final whole-interval scratch explicitly. Existing allocation persistence is essential to transport byte-exclusion premises to the intermediate state. Reserved-credit restoration supplies the scratch premise in actual consumers.

#### Statement
Output weakening:
enc_frame st st' lo top outs s0 s /\ (!r. MEM r outs ==> MEM r larger) ==> enc_frame st st' lo top larger s0 s.

Composition (local tops may differ):
st0.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= st2.cs_next_id /\
(!x. not_fresh_at st0 x ==> not_fresh_at st1 x) /\
enc_frame st0 st1 lo top1 outs1 s0 s1 /\
enc_frame st1 st2 lo top2 outs2 s1 s2 /\
enc_scratch (frag_ids st0 st2) lo top s2
==> enc_frame st0 st2 lo top (outs1 ++ outs2) s0 s2.

#### Approach
Use frag_ids_split to reduce whole-interval membership and nonmembership. For memory composition, exclusion from final prefix scratch implies exclusion from intermediate prefix scratch because the second frame preserves every existing allocation entry. Transport old variables using the explicit freshness-monotonicity premise, compose outside-id equalities and effects, and take final scratch from its premise.

#### Not to try
Do not attempt to infer the final global budget from the two frames alone. Do not assume prefix scratch cells disappear at the second stage; use the existing-allocation persistence conjunct. Do not add vs_labels equality to the frozen frame: it remains a separate execution invariant.

### C1.4: Instruction effects and base encoders
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: The observed timeout comes from mixing memory implementation expansion with allocation invariants. Equality of the two allocation-state projections suffices to transport scratch invariants without memory reasoning.
- Progress transition: `refinement`

#### Progress note
E0010 establishes two retained memory-disjointness helpers but does not close the original component. Remaining work is separated at the metadata boundary.

#### Summary
Retain enc_write_memory_disjoint and enc_mcopy_disjoint. Establish allocation-state congruence before framing instructions. Complete the original instruction-effect and base-encoder outputs using that interface; frozen definitions and statements remain unchanged.

#### Not to try
Do not simplify enc_scratch with mcopy_def, write_memory_with_expansion_def and allocation invariant definitions in one call. This expands irrelevant memory records and has already exceeded the tactic limit.

#### Argument
enc_scratch depends on the state only through vs_allocas and vs_alloca_next, including its alloca_inv conjunct. Memory-only operations preserve those projections. Prove this transport fact once, then combine it with disjoint byte observations to establish frames; base encoders compose the resulting instruction facts.

#### Definition design
Do not change enc_scratch or enc_frame. Expose scratch congruence under equality of allocation map and frontier. Separate projection equations for memory operations from their byte-observation equations. A consumer should never unfold both write_memory_with_expansion and alloca_inv.

#### Code structure
Keep the existing two disjoint-write helpers in lowering/abiEncoderPropsScript.sml. Place allocation congruence and projection lemmas before instruction frames, and instruction frames before base encoder proofs. No protected files are edited.

### C1.4.1: Allocation-state congruence and memory-operation projections
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: The invariant depends only on two projections; unfolding only allocation predicates on abstract states avoids the demonstrated record explosion.
- Checkpoint: yes

#### Summary
Prove scratch transport from equality of allocation map and frontier. Prove projection preservation for memory-only operations used by encoder frames. Validate the interface on MCOPY scratch preservation without unfolding memory in the consumer.

#### Statement
!ids lo top s t. t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==> (enc_scratch ids lo top t <=> enc_scratch ids lo top s). Also prove the corresponding projection equalities for write_memory_with_expansion and mcopy, and enc_scratch ids lo top (mcopy dst src len s) <=> enc_scratch ids lo top s.

#### Approach
Prove allocation-invariant congruence on abstract states by unfolding allocation predicates only, then scratch congruence using it. Separately unfold memory operations only beneath individual record selectors; derive scratch preservation by congruence. Build abiEncoderPropsTheory to test that each boundary stays below the unchanged tactic limit.

#### Not to try
Do not unfold memory implementations inside the scratch transport proof, and do not expand dimword arithmetic just to transport unchanged data.

### C1.4.2: Framed base encoder consumers, including bytestrings
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Copy and primitive consumers already build; bytestring is straight-line execution with two memory writes and elementary padded-byte layout.
- Progress transition: `refinement`
- Carries progress/evidence from: E0017

#### Progress note
E0017 remains supporting evidence for the existing copy and primitive consumers; this grouping does not certify any new child. Preserve all previously proved source.

#### Summary
Copy and primitive operational and ABI consumers are already present and must be preserved. Remaining work is the AbiBytestring branch only. Separate fixed-frame instruction composition, rounding/layout, operational execution, and typed ABI integration. No changes to frozen definitions or theorem.

#### Not to try
Do not scale prim_run into a ten-level update_var witness. Do not use fresh_vars_wrt-based emit correctness lemmas by assuming freshness absent from enc_pre. Do not split scratch intervals for this allocation-free branch. Do not modify the two out-of-scope cheated theorems.

#### Argument
Let l be the live byte length and r = 32 * ((l + 31) DIV 32). The compiler zeros the word at dst+r and then copies 32+l bytes from src; the source is disjoint from the complete output region. The copy supplies the length word and live payload, and the zero word supplies exactly the remaining padding through dst+32+r. Arithmetic computes r and returns 32+r. Every instruction preserves allocation metadata, and all writes lie in this output region, so one ambient frame can be carried throughout without partitioning scratch budgets.

#### Definition design
Do not introduce a second memory or execution semantics. Use run_inst_seq with existential intermediate states and enc_frame indexed by the entire branch. A fixed-index transitivity lemma supplies the frame interface. Instruction lemmas must not require fresh_vars_wrt: enc_pre only protects operands by not_fresh_at, and pre-existing bindings for future variables are permitted. Probe this interface on ADD/AND before composing the branch.

#### Code structure
Add helpers in lowering/abiEncoderPropsScript.sml next to the existing frame and base-consumer helpers. Preserve compile_abi_encode_copy_abi_frag and compile_abi_encode_prim_abi_frag unchanged. Keep arithmetic/layout independent of compiler expansion; keep instruction unfolding in boundary lemmas, not in the typed consumer. Build abiEncoderPropsTheory after each child.

### C1.4.2.1: Fixed-frame straight-line instruction boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Fixed-frame transitivity follows directly from preservation of existing allocations; opcode rules are single-instruction computations.
- Checkpoint: yes

#### Summary
Provide fixed-index frame composition and allocation-free instruction execution facts. Preserve operands old at the local compiler state, not every operand in the initial state. Validate ADD and AND with this weaker, task-compatible interface. Include MLOAD, MSTORE and MCOPY boundaries needed by the bytestring branch.

#### Statement
Core frame lemma: enc_frame a b lo top outs s0 s1 /\ enc_frame a b lo top outs s1 s2 ==> enc_frame a b lo top outs s0 s2. Instruction boundaries return an existential run_inst_seq successor, evaluated result (where present), unchanged labels, and the ambient frame. Parameterize ambient a,b independently of the local emit state; require a.cs_next_var <= local.cs_next_var for fresh result writes. Memory instructions require their written interval to be contained in outs.

#### Approach
Prove fixed-frame transitivity by unfolding enc_frame once: old scratch allocations persist into the final state, which transports the memory-disjoint premise backwards. Derive local emit execution rules from emitted_insts_emit_op/emit_void and step semantics, using enc_frame_update_var and enc_eval_operand_update_old; provide interval-containment frame weakening where membership-only enc_frame_enlarge_outputs is insufficient. Return existential states so later proofs use strip_tac and sequence composition instead of explicit state expressions.

#### Not to try
Do not assert preservation of arbitrary operands: newly emitted variables can overwrite old bindings. Do not use compiler-state split enc_frame_compose when both frames already describe the same ambient interval. Keep each opcode proof small; shared pure-op computation belongs in one parameterized boundary, not duplicated ADD/AND proofs.

### C1.4.2.2: Rounded length and prezero-copy byte layout
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The rounding identity is a low-five-bit mask fact; layout is interval reasoning on one zero store followed by padded MCOPY.

#### Summary
Prove natural/word rounding agreement without overflow. Prove exact bytes produced by the prezero/copy algorithm. Handle l=0 and multiples of 32 explicitly in the argument. Keep these facts independent of compiler state.

#### Statement
For r = 32 * ((l+31) DIV 32), establish l <= r, r < l+32, and, under l+31 < dimword(:256), (n2w(l+31):bytes32) && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w = n2w r. Under regions_disjoint (src,32+l) (dst,32+r), the bytes at dst of length 32+r after mcopy dst src (32+l) (mstore (dst+r) 0w s) equal mem_bytes_at src (32+l) s.vs_memory ++ REPLICATE (r-l) 0w. Also expose preservation of the source read across the prezero store.

#### Approach
Use division with remainder by 32 to prove the arithmetic; locate existing word-mask and byte-slice facts before adding duplicates (their exact names are not verified here). For layout, partition output into copied prefix and remaining suffix: suffix starts at dst+32+l, lies inside the zeroed word [dst+r,dst+r+32), and has length r-l. Source disjointness ensures MCOPY reads the original prefix, including when memory expands.

#### Not to try
Do not equate raw memory lists after writes; reason with padded mem_bytes_at observations. Do not assume positive l or a nonempty padding suffix. Do not assume MCOPY reads the original source without proving the zero store misses it.

### C1.4.2.3: Operational framed bytestring encoder
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: With instruction boundaries and rounding established, this is sequential composition of ten allocation-free instructions.
- Dependencies: C1.4.2.1, C1.4.2.2

#### Summary
Prove compile_abi_encode_bytes_frame_frag with a natural live length parameter. Return exact observed bytes, returned size, unchanged labels and enc_frame. Use existential intermediate states and a fixed ambient output region. No typing or ABI conversion is unfolded here.

#### Statement
Given compile_abi_encode_to_buf dst src (AbiBytestring max_len) st = (op,st'), eval_operand dst s0 = SOME dst_w, eval_operand src s0 = SOME src_w, oldness of dst/src at st, mem_word_at (w2n src_w) s0.vs_memory = n2w l, l+31 < dimword(:256), r = 32*((l+31) DIV 32), w2n dst_w+32+r < dimword(:256), regions_disjoint (w2n src_w,32+l) (w2n dst_w,32+r), and enc_scratch (frag_ids st st') lo top s0, conclude frag_exec with bytes equal mem_bytes_at (w2n src_w) (32+l) s0.vs_memory ++ REPLICATE (r-l) 0w, op evaluating to n2w(32+r), unchanged labels, and enc_frame st st' lo top [(w2n dst_w,32+r)] s0 s. R may remain arbitrary.

#### Approach
Expand the compiler branch once and name its intermediate compile states/operands. Compose existential instruction results using emitted instruction concatenation, keeping operand preservation indexed by local emission order and frames indexed by the complete branch; lift the successful run with frag_exec_run_inst_seq. If needed for the 50-line limit, extract semantic prefix (load/rounded pointer), write pair, and size-suffix run helpers as outputs of this component, rather than suspending a giant raw-state calculation.

#### Not to try
Do not unfold enc_frame in the ten-instruction consumer. Do not introduce nested update_var witnesses or large manual theorem instantiation lists. The prefix and suffix arithmetic operate on the loaded length, which must remain available across the memory writes.

### C1.4.2.4: Typed exact ABI bytestring consumer
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: Typing and value-memory definitions identify length/payload; operational postcondition then matches bytes/string ABI padding.
- Dependencies: C1.4.2.2, C1.4.2.3
- Checkpoint: yes

#### Summary
Provide exact ABI-byte framed consumers for the bytes and string plan constructors. Derive all word bounds and disjointness from enc_pre and typed memory facts. Preserve unchanged labels for downstream composition. Audit retained base consumers and build the target theory.

#### Statement
Add compile_abi_encode_bytes_abi_frag (or separate bytes and string specializations if their inversion differs): the to_buf conjunct of the frozen target specialized to BaseT(BytesT(Dynamic n)) and BaseT(StringT n), ei = AbiBytestring n, with additional unchanged-label postcondition and arbitrary R. Include any necessary value-memory/ABI inversion helpers as outputs here.

#### Approach
Invert evaluate_type, value_has_type, vyper_to_abi and val_in_memory for bytes/string to obtain live length, length word and live payload; prove the ABI encoding is that prefix followed by r-l zeros and has length 32+r. enc_pre_bounds supplies output end below dimword via lo/top, hence l+31 and address additions do not wrap; source disjointness restricts to 32+l. Apply the operational consumer through frag_exec_conseq, as for the already proved copy/primitive consumers.

#### Not to try
Do not assume max_len itself is word-bounded when only live/output sizes are needed. Do not alter frozen plan definitions or the final statement. Do not reprove the completed copy and primitive integrations.

### C1.5: Concrete array prefix and loop-invariant interfaces
- Kind: `proof_group`
- Risk: 2
- Work priority: 5
- Work units: 0
- Rationale: Prefix algebra follows the existing enc_tuple_cons_parts equation; runtime interfaces expose explicit preservation premises rather than hiding an unproved body theorem.
- Progress transition: `refinement`

#### Progress note
Refines the active, unedited definition probe into three semantic interfaces. No prior proof is claimed or invalidated.

#### Summary
Represent encoded prefixes as separate head and tail byte lists with a fixed full head boundary. Keep the memory prefix predicate independent of typing and allocation. Parameterize runtime invariants by a stable context K, which later loop integration supplies. Prove initialization, one-element extension, exit assembly, and jump stability before execution integration.

#### Approach
Build the ABI prefix interface first, then prove memory assembly independently of writes, then package the position-independent runtime invariant. Use separately named short facts so consumers never expand enc_tuple recursion or the full K definition.

#### Not to try
Do not define the prefix as TAKE of the final encoding: dynamic heads and tails are separated and offsets use the full head boundary. Do not use an enc_tuple on TAKE k with its own head_lengths as boundary. Do not combine source typing, scratch allocation, prefix arithmetic, and instruction execution into one initialization/step proof.

#### Argument
For N elements the head boundary B is fixed before iteration (N*asz in both homogeneous loops). At iteration k, H contains the heads of the first k values, T their dynamic payloads, and the next dynamic offset is B+LENGTH T. Appending one element adds its static encoding or offset word to H and its dynamic encoding, if any, to T. A static-element loop is the same memory-prefix abstraction with an empty T, payload base equal to full destination plus 32, and no tail cell. Source stability, allocation credit, and protected cells belong to a separate context K and are transported independently. This matches frag_exec_loop's position-independent I and J; header temporaries are not part of the prefix algebra.

#### Definition design
Define ABI-level functions enc_prefix_tail ts vs and enc_prefix_head q ts vs. Tail recursion: [] for either empty list; on t::ts,v::vs let z=if is_dynamic t then enc t v else []; return z ++ enc_prefix_tail ts vs. Head recursion: [] for either empty list; on t::ts,v::vs use (if is_dynamic t then enc_number (Uint 256) (NumV q) else enc t v) ++ enc_prefix_head (q+LENGTH z) ts vs. Define HP B ts vs k = enc_prefix_head B (TAKE k ts) (TAKE k vs), TP ts vs k analogously, and DP B ts vs k = B+LENGTH(TP ts vs k). Total mismatched-list cases may return []; every semantic theorem requires equal lengths or has_types. Define enc_prefix_mem p B ts vs k s iff mem_bytes_at p (LENGTH(HP B ts vs k)) s.vs_memory = HP B ts vs k and mem_bytes_at (p+B) (LENGTH(TP ts vs k)) s.vs_memory = TP ts vs k. Define enc_array_inv K p B ts vs ip cp k s iff K s /\ k<=LENGTH vs /\ enc_prefix_mem p B ts vs k s /\ mem_word_at ip s.vs_memory=n2w k /\ (case cp of NONE => T | SOME c => mem_word_at c s.vs_memory=n2w(DP B ts vs k)). K is deliberately a predicate argument, not a new record containing the whole theorem environment. Dynamic loop uses cp=SOME c; static loop uses NONE. The intended K includes stable operand evaluations, source val_in_memory, source/output bounds, global enc_frame from the original state, fixed allocated count/tail cell ownership, and protected outer alloca lookups; see child C1.5.3 for the exact composition contract. Never assert K preservation without premises.

#### Code structure
Add definitions and short pure lemmas immediately after the existing ABI layout lemmas in lowering/abiEncoderPropsScript.sml. Put memory and runtime interface lemmas after those definitions. Keep compiler decomposition and actual frag_exec header/body proofs in their existing owning components. Do not modify frozen definitions, frag_exec_loop, or files under forbidden directories.

### C1.5.1: Pure separated ABI prefix algebra
- Kind: `definition_probe`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: The proposed recursion is exactly the head/tail decomposition of enc_tuple; append laws are structural list inductions.
- Checkpoint: yes

#### Summary
Define separated prefix heads, tails, and dynamic offset. Establish empty, successor, and final assembly laws. Test both static and dynamic homogeneous element cases. No runtime state or frame is involved.

#### Statement
Use definitions in C1.5. Required outputs: (1) LENGTH ts=LENGTH vs ==> enc_prefix_head B ts vs ++ enc_prefix_tail ts vs = enc_tuple B 0 ts vs [] []; (2) HP B ts vs 0=[] and TP ts vs 0=[] and DP B ts vs 0=B; (3) under LENGTH ts=LENGTH vs and k<LENGTH vs, with t=EL k ts, v=EL k vs, z=if is_dynamic t then enc t v else [], h=if is_dynamic t then enc_number (Uint 256) (NumV(DP B ts vs k)) else enc t v: HP B ts vs (SUC k)=HP B ts vs k ++ h; TP ts vs (SUC k)=TP ts vs k ++ z; DP B ts vs (SUC k)=DP B ts vs k+LENGTH z; (4) has_types ts vs ==> LENGTH(HP B ts vs k)=head_lengths (TAKE k ts) 0 for k<=LENGTH vs; (5) homogeneous static specialization TP (REPLICATE N t) vs k=[] when ~is_dynamic t; homogeneous dynamic specialization LENGTH(HP B (REPLICATE N t) vs k)=32*k under typing and k<=N=LENGTH vs. Final assembly at k=LENGTH vs must recover enc_tuple B 0 ts vs [] [].

#### Approach
First prove the more general assembly law enc_prefix_head q ts vs ++ enc_prefix_tail ts vs = enc_tuple hl tl ts vs [] [] when q=hl+tl, using enc_tuple_cons_parts and typed lists (use has_types rather than mere equal lengths if that existing lemma requires it). Prove paired append laws with equal list lengths; successor laws then use TAKE (SUC k). Prove head length using enc_has_static_length after checking its signature; all enc_tuple assembly laws may carry has_types.

#### Not to try
Do not force an untyped assembly proof through the typed enc_tuple_cons_parts lemma. State assembly under has_types if needed; the task supplies typed ABI values. Do not introduce recursive runtime invariants to prove this pure algebra.

### C1.5.2: Memory-prefix initialization, extension and exit boundaries
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: These facts only assemble adjacent byte slices; actual store/frame preservation remains explicit in their premises.
- Dependencies: C1.5.1

#### Summary
Define enc_prefix_mem without allocation or variable context. Prove its empty case for arbitrary memory. Provide a successor rule from four readable byte-slice facts in the resulting memory. Provide final head/tail assembly for use at loop exit.

#### Statement
Outputs: enc_prefix_mem p B ts vs 0 s. Successor rule, under has_types ts vs and k<LENGTH vs: if in s' the old head slice at p equals HP B ts vs k, the old tail slice at p+B equals TP ts vs k, the slice at p+LENGTH(HP B ts vs k) of length LENGTH h equals h, and the slice at p+DP B ts vs k of length LENGTH z equals z, then enc_prefix_mem p B ts vs (SUC k) s', where h,z are the C1.5.1 successor expressions. Exit rule: has_types ts vs /\ B=head_lengths ts 0 /\ enc_prefix_mem p B ts vs (LENGTH vs) s ==> mem_bytes_at p (LENGTH(enc_tuple B 0 ts vs [] [])) s.vs_memory=enc_tuple B 0 ts vs [] []. Also export head/tail exit assembly without B=head_lengths ts 0 for consumers that keep regions separate.

#### Approach
Use the existing mem_bytes_at append/slice interface after locating its actual signatures; if absent, add only the needed adjacent-slice concatenation lemma here. The successor rule deliberately refers solely to s': the body proof must obtain the two preserved old slices from its frame and the two new slices from its child/store postconditions. This avoids claiming preservation of arbitrary memory updates.

#### Not to try
Do not assume a child frame preserves the old prefix automatically: disjointness from its output and scratch cells must be established by the body integration. Do not put an operational child execution premise in this lemma.

### C1.5.3: Runtime invariant packaging and position stability
- Kind: `definition_probe`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: The invariant is a small conjunction parameterized by context. Its transport rules are logical packaging, not an unsupported claim about allocator or instruction behavior.
- Dependencies: C1.5.2
- Checkpoint: yes

#### Summary
Define enc_array_inv using a parameterized stable context K and optional tail cell. Export zero, successor packaging, elimination and jump rules. Specify exactly what later loop integration must put into K and preserve. Header condition facts remain separate from the memory prefix.

#### Description
At integration, K s is the conjunction of: original source val_in_memory and numeric source/output bounds; evaluations of externally supplied stable operands (dst, src, len_op); enc_frame st_global st_final lo top outs s0 s for the entire loop-containing fragment; fixed allocation lookups SOME(ip,32) and, if dynamic, SOME(c,32) at the allocated loop-cell IDs; and any enclosing protected alloca lookups. The enc_frame conjunct already supplies global enc_scratch, unchanged effects and old-variable preservation: do not duplicate those expansions inside K. Ownership and non-overlap of loop cells are obtained from alloca_inv and their distinct IDs. K does not freeze the contents of the count or tail cell. Protected enclosing cell contents, when required by a caller, must be proved preserved from frame separation, not arbitrarily assumed to survive. The dynamic offset B+LENGTH TP is a natural number; word non-wrap needed by arithmetic instructions is a separate body arithmetic obligation, not a condition hidden in this packaging definition.

#### Statement
Initialization: K s /\ mem_word_at ip s.vs_memory=0w /\ (case cp of NONE=>T | SOME c=>mem_word_at c s.vs_memory=n2w B) ==> enc_array_inv K p B ts vs ip cp 0 s. Successor packaging: K s' /\ SUC k<=LENGTH vs /\ enc_prefix_mem p B ts vs (SUC k) s' /\ mem_word_at ip s'.vs_memory=n2w(SUC k) /\ (case cp of NONE=>T | SOME c=>mem_word_at c s'.vs_memory=n2w(DP B ts vs (SUC k))) ==> enc_array_inv K p B ts vs ip cp (SUC k) s'. Jump rule: (!s l. K s ==> K(jump_to l s)) /\ enc_array_inv K p B ts vs ip cp k s ==> enc_array_inv K p B ts vs ip cp k (jump_to l s). Export separate elimination lemmas for K, count, prefix and tail-cell value. Define header predicate J k s = enc_array_inv K p B ts vs ip cp k s /\ eval_operand cnd s=SOME(if k<LENGTH vs then 0w else 1w), or use this lambda directly; prove jump stability when operand evaluation is jump-stable and the condition-extraction obligation of frag_exec_loop.

#### Approach
Prove packaging and elimination by unfolding only enc_array_inv; prove jump stability using unchanged memory and operand evaluation under jump_to. For the concrete later K, expose a general enc_frame jump-preservation lemma here if no such lemma already exists, plus enc_prefix_mem jump-preservation; neither proof should unfold ABI encoding. Keep header instruction correctness out of this subtree.

#### Not to try
Do not freeze all generated variables: header and body reassign their own SSA names on each iteration. Do not assert enc_pre for the whole original source after every child without deriving it from preserved source bytes. Do not claim K s implies K s' merely from a local child frame; global frame composition and remaining scratch credit are separate integration premises.

### C1.6: Static-element dynamic-array loop
- Kind: `proof`
- Risk: 2
- Work priority: 60
- Work units: 8
- Rationale: The loop body calls only static_info, whose correctness is independent of the mutual encoder theorem.
- Dependencies: C1.4, C1.5

#### Summary
Prove compile_abi_encode_dyn_static_loop using frag_exec_loop. Write only the payload after the existing length word and return the whole encoded size. Preserve all outer cells, including the dispatcher parent counter.

#### Statement
Output: framed fragment correctness of compile_abi_encode_dyn_static_loop dst src ei asz msz len_op under a valid static element plan, a typed dynamic-array source, len_op=LENGTH vs, and bounded separated output. The payload at dst+32 is the concatenation of element encodings, the returned size is 32+LENGTH vs*asz, and the memory footprint excludes any unperformed write to the length word.

#### Approach
Initialize the counter cell and instantiate frag_exec_loop with N=LENGTH vs and the static invariant. Prove a header boundary lemma yielding cnd=0 iff k<N and a body boundary lemma extending the prefix and incrementing the counter; then use the exit MLOAD of the preserved source length. Use the static-plan classification to exclude static_info's default no-op branch.

### C1.7: Child wrapper and complex-elements recursion steps
- Kind: `proof`
- Risk: 2
- Work priority: 70
- Work units: 8
- Rationale: These branches sequence recursive calls and arithmetic; C1.1-C1.4 expose the necessary region and frame facts.
- Dependencies: C1.4

#### Summary
Prove branch lemmas parameterized by the recursive correctness assumptions supplied by compiler induction. Cover both child branches and nil/cons complex-elements branches. Keep parameterized helpers matched to the final induction goals.

#### Statement
Outputs: child static and dynamic branch closure under the to_buf induction hypothesis; complex_elems nil and cons branch closure under the child and suffix induction hypotheses. Conclusions are exactly the corresponding frozen theorem clauses, including arbitrary src_offset/head_offset and the outside-id counter cell.

#### Approach
For a dynamic child, save d before encoding the payload, write d into the head, and update the preserved external counter by the returned length. For a complex cons, extract the first value and suffix source, split head/tail output regions using C1.1, instantiate the child then suffix hypotheses, and combine their memory equalities and frames. Package arbitrary recursive correctness assumptions as readable named predicates if needed, without adding stronger premises to the final theorem.

#### Not to try
Do not specialize the induction hypotheses to src_offset=0 or d=head size. When the suffix has no dynamic entries, retain the counter fact via framing rather than demanding the suffix theorem update it.

### C1.8: Dynamic-element array loop recursion step
- Kind: `proof`
- Risk: 2
- Work priority: 80
- Work units: 13
- Rationale: The supplied loop rule reduces the branch to a straight-line header, one recursively encoded child and prefix extension.
- Dependencies: C1.4, C1.5
- Checkpoint: yes

#### Summary
Prove the fourth frozen clause as a branch closure under the element to_buf induction hypothesis. Cover allocation reuse, empty arrays and arbitrary typed lengths. Return the total encoding length while writing only DROP 32.

#### Statement
Output: compile_abi_encode_dyn_loop branch closure with exactly the fourth task clause as conclusion and the recursive to_buf correctness assumption for the element plan as its additional helper premise.

#### Approach
Initialize i=0 and dyn=length*asz; plan inversion forces asz=32 because the array plan's dynamic-element flag is T. The body encodes one source element at dst+D_k, stores D_k in head slot k, advances the tail counter by the child result and advances i. Apply frag_exec_loop with the dynamic invariant, then load final_dyn and add 32; source and output bounds justify every word/natural conversion.

#### Not to try
Do not unroll the runtime loop by compiler induction. Do not reset alloca state between iterations: the recursive body runs repeatedly with the same fragment ids and must satisfy the reused-cell scratch invariant.

### C1.9: Aggregate and array dispatcher recursion steps
- Kind: `proof`
- Risk: 2
- Work priority: 90
- Work units: 8
- Rationale: These branches wrap the established child/list/loop results with local scratch setup and size loads.
- Dependencies: C1.6, C1.7, C1.8

#### Summary
Cover the remaining to_buf branches under their recursive induction hypotheses. Include tuple, fixed-array and struct source representations. Preserve the dispatcher parent offset cell around nested loops.

#### Statement
Outputs: to_buf AbiDynArray closure for static and dynamic elements; to_buf AbiComplex [] and nonempty closure for each permitted plan constructor. Include struct environment deletion and conversion/list typing transport, fixed-array replication transport, and empty dynamic aggregates.

#### Approach
For arrays, allocate the parent cell, write the length word, select the appropriate loop, and add its returned total length to the preserved zero parent counter. For complex values, use C1.1/C1.2 to transport tuple/struct/fixed-array semantics to the list clause, initialize the head-size counter when a dynamic member exists, and read the final size. Handle dynamic aggregates with no elements directly rather than assuming dynamic type implies a nonempty plan.
