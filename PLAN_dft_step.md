# PLAN

## Structured Components

### C1: Prove the frozen DFT step contract without SSA
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The required invariant is deletion-and-guarded-flipping, not permutation. DFS termination uses an existing decreasing measure without needing acyclic data dependencies; the remaining obligations split into local scheduler and shape interfaces.
- Required for completion: yes

#### Summary
Prove exactly dft_step_contract, keeping all existing definitions and theorem statements unchanged. Establish a non-SSA scheduler interface: termination of the work stack, unique emitted ids, final terminator preservation, and safe flips. Lift a block relation through the bounded function loop, then transport every conjunct of o1_fn_shape. Finish freshness and supply obligations using the dispatcher equation and instruction-id inclusion.

#### Not to try
Do not prove semantic correctness, wf_ssa, full permutation, all-nonpseudos coverage, or other O1 pass contracts. Do not use schedule_output_all_distinct or schedule_terminator_last by silently assuming their topology hypotheses. Do not change the frozen target or existing proved code.

#### Argument
Cycles may cause omissions but cannot cause duplication: processing marks an id before pushing its children, and only that first processing creates an emit item. The existing dfs_measure strictly decreases whenever the work stack is nonempty, independently of topological compatibility; empty stack, not zero unvisited count, is the required endpoint. A well-formed final terminator has no outputs and no later EDA user, hence is the last entry and cannot be reached from another entry. Its eventual emission is last. Pseudo filtering preserves the PHI prefix. Instructions retain ids, outputs, operand membership and relevant opcode classes; the only label-position-sensitive flip, ADD [op; Label "code_end"], is excluded because its child list has length at most one. These facts yield a block relation closed under repeated scheduling and enough to preserve all function shape conditions, including monotonicity of GAS/RETPC copy-PHI closures.

#### Definition design
Do not change production definitions. Add only proof predicates where needed: an emit-accounting invariant and a block relation packaging equal labels, equal final instructions, distinct output ids, source provenance, and instruction-shape preservation. Probe these at initialization and one DFS step before using FUNPOW. Keep ordinary from_block provenance for ids and operand membership, but do not treat it as sufficient for label_positions_ok. The consumer boundary must explicitly provide safe label positions. A failed attempt to prove coverage or permutation in cyclic graphs is not a failure of this contract.

#### Code structure
Keep final contract and O1-specific shape lemmas in venom/compiler/o1DftStepScript.sml. Put non-SSA scheduler helpers in a new neighboring DFT proof theory, and if necessary its block/function lifting helpers in a second theory. Use modern Theory/Ancestors syntax and no new Lib automation. Search for existing matching results before adding any helper; do not duplicate existing SSA statements under new names. Proofs should stay within approximately 50 lines each. Build only with holbuild --max-heap 7000 -j4; retain the 2.5-second tactic limit, avoid TRY/ORELSE around search, and read docs/HOL4_PROOF_CONTROL_LESSONS.md before branching proofs.

### C1.1: Non-SSA DFS termination boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: dfs_step_measure_dec already has precisely the non-SSA assumptions needed; only its endpoint must change from complete coverage to an empty stack.
- Checkpoint: yes

#### Summary
Reuse dfs_measure, dfs_good_state and dfs_step_measure_dec from dftCompleteness. Prove stack emptiness after any budget at least the initial measure. Specialize to the actual schedule budget and entry list. This does not assert that all input instructions are visited.

#### Statement
eda_wf eda bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ dfs_good_state bi st /\ dfs_measure bi st <= fuel ==> (FUNPOW (dfs_step bi order eda om fl) fuel st).ds_stack = []
Also specialize this to the initial state of schedule_from_entries with entries = entry_instructions bi order eda and fuel = (LENGTH bi + 1) * (LENGTH bi + 1).

#### Approach
Induct on fuel, generalizing st. Split first on empty stack: it is a fixed point; otherwise use dfs_step_measure_dec and dfs_step_preserves_good to invoke the IH. Bound initial stack length by LENGTH bi and unvisited_count by LENGTH bi, obtaining n + n*(n+1) <= (n+1)^2.

#### Not to try
Do not reuse measure_reaches_zero: it assumes eda_topo_compatible and proves the stronger, false-for-cycles coverage conclusion. Do not introduce a new termination measure.

### C1.2: Emit accounting and distinct scheduled ids
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The guard on ds_visited directly enforces unique creation of emit items; no dependency ordering hypothesis is needed.

#### Summary
Define a small invariant tracking the ids of emitted instructions and pending DfsEmit items together. Prove initialization and one-step preservation, then lift over FUNPOW. Export non-SSA distinctness of schedule output and absence of pseudo instructions. Combine with pseudo filtering to obtain distinct ids for dft_block.

#### Statement
Under eda_wf eda bi and input id distinctness, the schedule from entry_instructions has ALL_DISTINCT emitted ids and every emitted instruction is non-pseudo. Under input id distinctness, dft_block order bb has distinct instruction ids.

#### Approach
Require ALL_DISTINCT of output ids appended to pending-emit ids, and membership of each such id in ds_visited; additionally require all these instructions non-pseudo. DfsEmit transfers one id between the two portions, while first-time DfsProcess introduces an id outside the visited set. Use existing flip_operands_inst_id, flip_operands_is_pseudo and source provenance to show disjointness from the pseudo prefix.

#### Not to try
Do not track order/topology of all dependencies or require every visited id to be emitted: visited pseudo instructions have no emit item. Do not use a set-only invariant, which cannot establish absence of duplicates.

### C1.3: Final terminator survives without SSA
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: The terminator exclusion argument needs only no outputs, distinct ids, and backward EDA, not backward data dependencies for all instructions.
- Dependencies: C1.1
- Checkpoint: yes

#### Summary
Prove the original final terminator is not a dependency target. Show entry_instructions ends in that terminator. Use empty-stack completion and a bottom-of-stack invariant to prove that the schedule is nonempty and ends in exactly the original terminator. Export equality of bb_succs for dft_block.

#### Statement
bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\ ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==> (dft_block order bb).bb_instructions <> [] /\ LAST (dft_block order bb).bb_instructions = LAST bb.bb_instructions.
Export a separate bb_succs equality corollary.

#### Approach
Inspect eda_deps_backward_plain in dftWf and reuse its actual signature for the EDA half; for DDA use producing_inst_def and empty terminator outputs. Inspect the existing id_not_in_stack and bottom-stack lemmas in dftWf, reusing those without topology premises; otherwise prove the narrow bottom-stack invariant needed here. C1.1 guarantees the bottom Process/Emit pair is eventually consumed, and the terminator is not flippable.

#### Not to try
Do not infer the terminator survives merely from provenance. Do not require the whole dependency graph acyclic; cycles elsewhere are harmless. Do not assume the existing schedule_terminator_last theorem has weak enough premises.

### C1.4: Safe instruction-shape transport through scheduling
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 8
- Rationale: All flip cases are finite opcode/operand cases; the sole asymmetric label case can be excluded before scheduling.
- Checkpoint: yes

#### Summary
Provide the shape-sensitive refinement missing from from_block. Prove ADD with a code_end label has at most one dependency and hence is never flipped. Establish preservation of inst_wf and inst_shape_ok, operand membership, outputs and the opcode classes used by O1. Propagate these properties by a DFS good-state invariant.

#### Statement
EVERY inst_shape_ok bb.bb_instructions /\ EVERY inst_wf bb.bb_instructions /\ ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==> EVERY inst_shape_ok (dft_block order bb).bb_instructions /\ EVERY inst_wf (dft_block order bb).bb_instructions.
Supply separate consumer lemmas for operand membership, unchanged ASSIGN/PHI/GAS/RETPC_PARAM/INVOKE instructions and preservation of forbidden-opcode classes used in o1_fn_shape.

#### Approach
For ADD [op; Label "code_end"], show build_eda contributes no effects and inst_data_deps contains at most one producer; sorting lists of length at most one is identity. For other flippable opcodes, label_positions_ok implies no labels, so operand permutation is safe. Prove initialization and dfs_step preservation for the refined instruction predicate, then FUNPOW and dft_block corollaries; reuse existing flip field lemmas instead of reproving them.

#### Not to try
Do not claim inst_shape_ok i ==> inst_shape_ok (flip_operands i): it fails for the code_end ADD. Do not prove label preservation solely from unordered operand membership. Keep case explosions inside local boundary lemmas, not downstream consumers.

### C1.5: Block relation and function-loop lifting
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 40
- Work units: 8
- Rationale: Once local scheduler facts are established, the function loop only replaces a looked-up block by a related block; induction is on FUNPOW iterations, not CFG structure.
- Dependencies: C1.2, C1.3, C1.4

#### Summary
Package exactly the structural facts needed by the O1 consumer. Include block labels, final terminator, source instruction provenance, distinct ids, well-formed PHI prefix, and local instruction shape. Prove closure under dft_block and transitivity where needed. Lift aligned blocks through dft_process_one, dft_loop_step and FUNPOW to dft_fn.

#### Statement
For well-formed input with fn_inst_wf and EVERY inst_shape_ok (fn_insts fn), derive aligned source/output blocks for dft_fn: same labels and successors, output ids a distinct subset blockwise, from_block provenance, bb_well_formed output, and preserved local instruction predicates. Export fn_ir_inst_ids inclusion and wf_function (dft_fn fn), fn_inst_wf (dft_fn fn).

#### Approach
Use dft_block_from_orig and from_block_trans for provenance. Derive PHI-prefix preservation directly: the pseudo filter keeps original relative order, original PHIs precede every non-PHI, and scheduled instructions are non-pseudo. For function lifting maintain LIST_REL on original/current blocks; distinct labels ensure lookup-and-replace changes only the matching block, and blockwise id inclusion plus original global distinctness gives global distinctness.

#### Not to try
Do not assert that original pseudos were already a prefix: bb_well_formed only requires the PHI prefix. Do not repeat a separate function-loop induction for every shape conjunct; package one aligned-block interface. Search dftCorrectness for existing label-map/entry-label results rather than adding duplicates.

### C1.6: Transport the complete O1 function shape
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: The nonlocal opaque-use property is monotone under deletion once seed and copy instructions remain unchanged; other conjuncts use the block interface.
- Dependencies: C1.5
- Checkpoint: yes

#### Summary
Prove o1_fn_shape ctx fn implies o1_fn_shape ctx (dft_fn fn). Handle opaque-use restrictions explicitly with copy_phi_var rule induction. Cover first-block facts, invocation and label references, and entry/nonentry opcode exclusions. Do not add SSA hypotheses.

#### Statement
o1_fn_shape ctx fn ==> o1_fn_shape ctx (dft_fn fn).
Strict helper: for origin GAS or RETPC_PARAM, copy_phi_var origin (dft_fn fn) x ==> copy_phi_var origin fn x.

#### Approach
Use rule induction on output copy_phi_var: GAS/RETPC_PARAM seeds and ASSIGN/PHI copies arise unchanged from input instructions, so each constructor transports. For an output opaque operand, input opacity plus operand membership gives an allowed use; allowed opcodes are not flippable, so their positional constraint is unchanged. Discharge remaining o1_fn_shape conjuncts using C1.5 labels/successors, provenance and C1.4 opcode boundaries.

#### Not to try
Do not assume fn_shape_ok is an EVERY predicate: opaque_use_ok depends on an inductively defined whole-function closure. Do not attempt equality of opaque-variable sets; deletion may shrink them.

### C1.7: Discharge and audit the frozen contract
- Kind: `proof`
- Risk: 1
- Work priority: 60
- Work units: 3
- Rationale: After shape preservation and id inclusion, the dispatcher leaves only definitional empty-map and unchanged-supply obligations.
- Dependencies: C1.6
- Checkpoint: yes

#### Summary
Replace only the target admission and add necessary imports. Extract input shape from unique lookup and o1_ctx_shape. Apply the DFT dispatcher equation, shape preservation and name inclusion. Build the exact requested target and audit all added theories for admissions and duplicate helpers.

#### Statement
Theorem dft_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_DFT)

#### Approach
Unfold o1_step_contract_def and fn_pass_step_def, use execute_configured_fn_pass_dft to identify output fields, and extract membership of fn from its unique lookup (reuse an existing lookup membership lemma if available). Apply C1.6; freshness follows from labels/ids inclusion, label_map_sources_ok from the empty list, and ir_supply_inst_ok from unchanged supply. Run holbuild --max-heap 7000 -j4 build o1DftStepTheory and confirm zero CHEAT warnings in the target and every added helper theory.

#### Not to try
Do not change the target, production definitions or existing proved theorems. Do not repair unrelated admissions or build semantic stage contracts. A tool wall-clock timeout is grounds for a longer holbuild call, not for raising the tactic timeout.
