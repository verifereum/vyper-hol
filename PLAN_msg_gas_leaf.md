# PLAN

## Structured Components

### C1: Concrete counted msg.gas leaf
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: All five proof children are reviewed proved, including the repaired concrete GAS boundary and both frozen roots. No unresolved mathematical integration risk remains; only final build and audit remain.
- Required for completion: yes
- Progress transition: `refinement`

#### Progress note
Remove historical Risk 3 inherited from the now-proved C1.2. Existing C1.1–C1.5 are omitted from this merge deliberately and retain their reviewed proof identities; this parent update makes no claim to certify a new leaf from their evidence.

#### Summary
Both frozen roots are implemented and reviewed proved. Placement, actual counted GAS execution, and full source builtin evaluation are established by existing local helpers. Preserve all five proved children and the frozen definitions/statements. Complete only the final default-limit build and dependency/tag audit.

#### Approach
Proceed directly to C1.6 after the already accepted proof children. If validation exposes an actual defect, report the exact evidence rather than reopening proved children speculatively.

#### Not to try
Do not reopen the repaired singleton-prefix tactic issue, change frozen statements, add helper definitions, or call the admitted generic lowering theorem.

#### Argument
Compilation places exactly one GAS instruction at the actual entry index in the same block. Its actual execution consumes one counted event, including zero-padding on an exhausted oracle, and yields the compiler endpoint. The singleton explicit source trace evaluates to the matching integer and empties source gas observations. These witnesses establish every unconditional strict summary obligation.

#### Definition design
No definitions may be introduced or changed. The existing msg_gas_placement, msg_gas_edge, and msg_gas_source helpers are the established proof interfaces; their consumers are the two frozen roots. Both empty and nonempty target oracle branches are already covered.

#### Code structure
Only lowering/msgGasSimScript.sml is in edit scope. Preserve the current Theory/Ancestors header, three local helpers, and two frozen root statements. Final validation should require no source changes.

### C1.1: Expose compiled GAS placement
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Direct unfolding of the concrete emit_op branch and use of an existing instruction containment lemma.

#### Summary
Expose the returned variable and singleton appended GAS instruction. Preserve block identity and derive endpoint length. Locate that instruction in the supplied function without assuming anything about subsequent code.

#### Statement
Local helper: compile_env_var MsgGas sa = (op,sb) /\ fn_has_code sa sb func ==> ?out id bb. op = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\ LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\ lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\ get_instruction bb (LENGTH sa.cs_current_insts) = SOME (mk_inst id GAS [] [out]).

#### Approach
Unfold compile_env_var_def and emit_op_def, then the existing fresh_id, fresh_var, emit and compiler-monad definitions as necessary (inspect their exact equations before use). Establish singleton append and block preservation, and apply fn_has_code_same_block at index zero. Keep out and id existential rather than exposing their generated names.

#### Not to try
Do not reason from emitted length alone to instruction identity, or reconstruct fn_has_code internals when fn_has_code_same_block supplies the required lookup.

### C1.2: Actual counted GAS instruction boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: The failures were a numeral rewrite loop and selecting the fuel witness while the word existential was still open. Isolating prefix computation from execution eliminates both issues; the GAS normal-success branch is a direct concrete semantic calculation.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0002

#### Progress note
E0002 supplies failure diagnosis only, not proved progress or continuity. Reopens the same concrete instruction boundary at risk 2 under the explicit staged repair required by review.

#### Summary
Prove a local boundary lemma for one actual GAS instruction at the current instruction index. Handle empty and nonempty target readings explicitly, including the zero default. Stage prefix computation separately from counted execution and successor-state equality. Keep all edits in msgGasSimScript.sml and all tactic limits unchanged.

#### Description
Resume the rejected episode as pending proof work rather than accepting its blocked conclusion. Use direct GAS execution to obtain the intermediate state with readings dropped and output updated; the edge definition then increments the index. Verify record updates commute at this final isolated equality. Supply a checked helper build at the default tactic limit, or report the precise remaining staged semantic goal if it still fails. This helper does not require compiler placement; that remains a consumer input. Frozen roots and all existing definitions remain untouched.

#### Statement
Local helper interface: ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\ get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) ==> ?w. gas_prefix 1 s.vs_gas_readings = [w] /\ gas_path_edge ctx func s 1 (OK (update_var out w (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings; vs_inst_idx := SUC s.vs_inst_idx|>))).

#### Approach
Split the readings list, choose the word witness first (0w for [], head for cons), and then split the prefix equality from the edge obligation. On the isolated prefix equality use a controlled one-shot rewrite with the local numerical equality `1 = SUC 0` proved by decide_tac, followed by simp only [gas_prefix_suc, gas_prefix_zero]; local prefix computation lemmas in this script are also permitted. Only after discharging that conjunct unfold gas_path_edge_def and choose fuel `0:num`, the supplied block and instruction, and the concrete execution result; discharge lookup, step execution, count, and normal successor-state equality as separate goals, selecting the nonterminator branch.

#### Not to try
Do not add arithmeticTheory.ONE to an unrestricted simplifier: it can create a numeral rewrite loop. Do not supply a fuel witness while the word existential remains open. Do not simplify the entire edge plus execution semantics in one broad call. Do not introduce timeout overrides, search fallbacks, helper definitions, or admitted lowering dependencies.

### C1.3: Full source builtin singleton-event evaluation
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 2
- Work units: 3
- Rationale: The builtin explicitly selects next_gas_reading; the remaining obligations are concrete arity, value reading, and any unsigned-word bound checks.
- Checkpoint: yes

#### Summary
Prove the source computation for every 256-bit event and arbitrary tail. Include the full eval_expr/read_result composition. Establish exact preservation of every source field other than gas_obs.

#### Statement
Local helper, with w : 256 word: bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])) (read_result cx) (es with gas_obs := w::tail) = (INL (IntV (&w2n w)), es with gas_obs := tail).

#### Approach
Use the Builtin equation of eval_expr: the empty argument list passes builtin_args_length_ok, the Env MsgGas branch calls next_gas_reading, and the returned Value is consumed by read_result. Inspect the exact read_result and arity definitions and simplify their selected branches only. If type bounds arise, discharge the unsigned 256-bit bound using the library word-to-number bound after verifying its signature; retain arbitrary w and tail.

#### Not to try
Do not stop at a theorem for next_gas_reading alone or assume source and target initial gas lists coincide. Do not assume w is strictly positive or that the suffix is empty.

### C1.4: Prove frozen compile_msg_gas_path
- Kind: `proof`
- Risk: 1
- Work priority: 3
- Work units: 1
- Rationale: The two target boundary helpers supply precisely the instruction and normalized endpoint required by the root.
- Dependencies: C1.1, C1.2

#### Summary
Replace the first placeholder without changing its statement. Transport entry block/index equalities into the instruction-location helper. Rewrite the successor index to the compiled endpoint.

#### Statement
compile_msg_gas_path exactly as frozen in TASK_msg_gas_leaf.md and currently in lowering/msgGasSimScript.sml.

#### Approach
Obtain out, id and bb from C1.1, then apply C1.2 using the frozen entry hypotheses. Use endpoint length and block preservation to close the existential conclusion by rewriting.

#### Not to try
Do not re-unfold compiler or execution definitions in this root; improve the local helper interface if their output fails to match.

### C1.5: Prove frozen strict summary and validate theory
- Kind: `proof`
- Risk: 2
- Work priority: 4
- Work units: 3
- Rationale: Explicit existential witnesses in gas_summary_def and elementary target-state projections suffice once the source and path helpers are available.
- Dependencies: C1.3, C1.4
- Checkpoint: yes

#### Summary
Replace the second placeholder with unconditional source/path/post witnesses. Use marks [T] and the actual target path from compile_msg_gas_path. Build msgGasSimTheory at the default tactic limit and audit the two frozen statements and proof dependencies.

#### Statement
compile_msg_gas_summary exactly as frozen in TASK_msg_gas_leaf.md and currently in lowering/msgGasSimScript.sml. Final validation: holbuild -j2 build msgGasSimTheory.

#### Approach
Apply compile_msg_gas_path and unfold gas_summary_def once. Choose marks [T], res INL (IntV (&w2n w)), es_end es, and the OK state supplied by that path; gas_explicit_def and the singleton prefix establish the source equation via C1.3 for every tail. Prove the normal post using eval_operand/update_var and record projection equations, retaining the path theorem's block equality. Build with no tactic-limit override; allow up to 3600 seconds wall-clock if prerequisites or memory waits require it, and inspect dependency/kernel-tag evidence for the roots to ensure neither proof used admitted generic simulation.

#### Not to try
Do not encode the source equation or post as assumptions of the summary, choose a vacuous exit branch, or use a proof of continuation compatibility in place of the counted path. Do not treat a short holbuild wall-clock timeout as a mathematical blocker.

### C1.6: Final default-limit build and root audit
- Kind: `build_probe`
- Risk: 1
- Work priority: 100
- Work units: 1
- Rationale: Both roots already built and passed source review; this is final verification without new proof obligations or edits.
- Dependencies: C1.1, C1.2, C1.3, C1.4, C1.5
- Checkpoint: yes

#### Summary
Run the final msgGasSimTheory validation build at the default tactic limit. Verify the exported frozen roots and record their kernel-tag/dependency evidence. Audit only the task script for forbidden admissions, definitions, shortcuts, and statement drift. Report evidence without unrelated repository cleanup.

#### Statement
Validation target: holbuild -j2 build msgGasSimTheory; both exported roots match TASK_msg_gas_leaf.md exactly and use no new admissions or admitted generic leaf simulation.

#### Approach
Run the requested build with default tactic limits, allowing a larger wall-clock tool budget up to 3600 seconds if required. Record exported theorem statements and kernel tags/dependencies using the available validation workflow, distinguishing permitted pre-existing admitted ancestors from any prohibited generic leaf theorem; inspect the task script for the domain constraints and report the results.

#### Not to try
Do not override tactic timeouts, introduce TRY/ORELSE/FIRST search fallbacks, edit other scripts, or treat permitted pre-existing ancestor admissions as a mandate to repair unrelated theories. Do not add proof code solely for validation.
