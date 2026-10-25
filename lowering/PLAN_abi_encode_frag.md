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

### C1.4.2: Instruction frames and base encoder consumers
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: With scratch transport isolated, frames separate into unchanged metadata/effects, variable preservation and the already checked disjoint-memory observation.
- Dependencies: C1.4.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0010

#### Progress note
Retains the two checked disjoint-write helpers as source progress, not a certificate for this remaining obligation.

#### Summary
Complete all instruction-effect and base-encoder obligations originally owned by C1.4. Start with framed MCOPY using the retained disjoint-memory theorem. Use the metadata boundary in the base cases rather than repeatedly expanding allocation invariants.

#### Description
This leaf inherits the original C1.4 coverage of instruction operations and its three base encoder cases; no original output is dropped by the split. Retain enc_write_memory_disjoint and enc_mcopy_disjoint, with no duplicate variants. Prove instruction-frame facts needed by the AbiPrimWord, AbiCopy and AbiBytestring consumers, and complete those base encoder fragment cases.

#### Approach
For each memory-only instruction, discharge allocation/scratch conjuncts through C1.4.1 and memory conjuncts through disjoint-observation helpers; prove unchanged variable/effect projections separately. Compose these facts with existing straight-line fragment rules for base encoder cases, keeping consumer proofs free of low-level memory splice and allocation-invariant expansions.

#### Not to try
Do not restore the failed full-record simplification experiment. Do not use one large search to unpack every frame conjunct, raise tactic timeouts, or weaken frozen preconditions.

### C1.5: Prefix invariant interface for array loops
- Kind: `definition_probe`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: The interface is tested by pure layout and preservation facts before any loop integration; the supplied loop rule fixes exactly which invariance properties are needed.
- Dependencies: C1.1, C1.2, C1.3
- Checkpoint: yes

#### Summary
Define compact, data-only loop invariants for static and dynamic element encodings. Establish initialization, prefix extension, and exit projections. Check zero and one iterations and jump invariance explicitly.

#### Statement
Outputs: static-prefix invariant for k encoded elements at dst+32 with counter k; dynamic-prefix invariant for k heads at dst and concatenated tails beginning at dst+32*LENGTH vs, with counter k and tail-end offset D_k = 32*LENGTH vs + SUM (MAP encoded_length (TAKE k vs)). Include k<=LENGTH vs, frozen source/operands, protected outer cells, and full-fragment scratch credit. Prove I 0 initialization, jump_to stability, prefix-byte extension, and full-prefix exit consequences.

#### Approach
Define invariants using separate head and tail byte lists obtained from C1.1, not an equality for the final encoding with holes. State extension lemmas assuming a child wrote its exact next head/tail regions and framed everything else; this makes the later body proof a direct application. The static loop addresses dst+32 while compile_abi_encode_dyn_loop's dst already points past the length word.

#### Not to try
Do not equate the current output to enc of TAKE k vs with its own head size: dynamic offsets are relative to the full array head size, not the prefix head size. Do not include vs_current_bb or vs_inst_idx in I/J.

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
