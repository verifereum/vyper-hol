# PLAN

## Structured Components

### C1: Frozen ABI fragment correctness
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The compiler recursion matches the four clauses. The loop rule is supplied by the task, and source/output/scratch separation supplies the preservation invariant needed to apply recursive calls.
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

### C1.2: Source subvalues and bounded region arithmetic
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: The required bounds follow from enc_pre, enc_scratch and alloca_inv; subvalue extraction follows the memory layout definition.
- Dependencies: C1.1

#### Summary
Make enc_pre usable at recursive calls without unfolding value layout in consumers. Extract tuple suffixes, individual aggregate members and array elements. Derive no-wrap bounds and output/source/scratch separation.

#### Statement
Outputs: source subvalue and suffix lemmas for tuples, structs, fixed arrays and dynamic arrays; preservation of val_in_memory when all padded byte observations in the source extent are unchanged; enc_pre bounds implying src + type_memory_size tv <= lo <= top < dimword (:256); child-output region containment and disjointness lemmas; from an outside-id alloca (c,32), alloca_inv and enc_scratch derive c+32 <= top and its disjointness from fragment-owned scratch cells.

#### Approach
Unfold val_in_memory only in these boundary lemmas, with structural list induction where necessary. Use the whole source extent to bound all source-pointer additions, and whole output extents plus C1.1 length decompositions to bound destination additions. Treat zero-size regions explicitly: regions_disjoint admits them, so do not extract strict bounds or nonempty-byte facts from empty intervals.

#### Not to try
Do not require output regions pairwise disjoint in general enc_pre. For dynamic head/tail regions derive the needed ordering from static_ofst+32<=d or head_offset+head_size<=d at the use site.

### C1.3: Scratch budget and frame composition interface
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 30
- Work units: 13
- Rationale: Finite instruction-id intervals, allocation monotonicity, and bytewise framing permit compositional proofs; repeated allocations retain the same cells.
- Dependencies: C1.2
- Checkpoint: yes

#### Summary
Prove the interval and allocation-credit calculus required for sequencing and loop reuse. Provide source/operand preservation and frame composition through a compact boundary interface. Probe the interface on empty fragments, nested id intervals and already-allocated cells before proceeding.

#### Statement
Outputs: finite frag_ids and interval splitting under ordered cs_next_id; enc_scratch restriction with reserved credit for the complementary interval; scratch restoration after executing a subinterval while preserving outside-id allocas; enc_frame reflexivity, output enlargement by region containment, and sequential composition for adjacent compile intervals; operand and protected-memory preservation consequences of enc_frame; jump_to invariance of all data-only predicates used later.

#### Approach
Count missing allocations by partitioning the full id interval, not by counting only actual ALLOCA instructions. Carry the enclosing budget as a reserved-credit invariant through subfragments: a plain restricted enc_scratch fact loses the credit needed for the suffix. Frame composition uses preservation of old allocations to retain previously allocated scratch regions, and lower bounds lo to protect source/output memory from every scratch store.

#### Not to try
Do not claim that two independent enc_scratch bounds for disjoint intervals imply the bound for their union. Do not assume a scratch id is absent on loop reentry. Avoid repeatedly expanding enc_frame in branch proofs; expose separate preservation and composition lemmas.

### C1.4: Instruction effects and base encoders
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 40
- Work units: 13
- Rationale: These are straight-line instruction proofs over MLOAD, MSTORE, MCOPY, arithmetic and ALLOCA, following the existing copy-fragment pattern.
- Dependencies: C1.3

#### Summary
Lift primitive instruction effects to the scratch/frame interface. Prove the AbiPrimWord, AbiCopy and AbiBytestring cases with the exact output footprint and effect frame. Cover compile_abi_encode_static_info on valid static plans.

#### Statement
Outputs: frame-aware rules for the emitted arithmetic/load/store/copy and compile_alloc_buffer 32 operations used by the encoder; exact framed fragment contracts for primitive word, static copy, bytestring and static_info encoders under the matching task hypotheses. These contracts must include all enc_frame fields, not merely memory equality and variable preservation.

#### Approach
Follow compile_abi_encode_copy_frag and frag_exec_run_inst_seq, reusing existing memory and emit lemmas after checking signatures. For bytestring length l, prove the rounded length and last-word zeroing equations first: the MSTORE at dst+ceil32(l) lies inside the total 32+ceil32(l) output, and MCOPY copies exactly 32+l bytes from the separated source. Split l=0 from positive lengths when proving padding; ALLOCA needs separate reused-cell and new-cell branches.

#### Not to try
The existing copy theorem's EL frame only protects addresses inside the old memory length and does not mention effects; do not silently treat it as enc_frame. Use padded-byte framing to cover memory growth and establish the missing unchanged fields from execution.

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
