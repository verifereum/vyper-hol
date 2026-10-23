# PLAN

## Structured Components

### C1: Prove frozen unwrap_value_shape
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Every reachable branch emits ordinary loads, allocation, arithmetic, stores or structured copy-loop control flow. value_shape_ok excludes LocCode, the only branch emitting disallowed code loads. Existing shape_step rules supply the needed preservation and freshness interfaces.
- Required for completion: yes

#### Summary
Prove only unwrap_value_shape and its necessary load/allocation/copy helpers. Preserve the frozen statement and all definitions. Non-word storage and transient values require the generated word-copy loop; calldata requires allocation and CALLDATACOPY. Exclude LocCode using value_shape_ok rather than proving code-load safety. Finish with the requested theory build and a scoped cheat/duplicate audit.

#### Not to try
Do not use compile_expr_shape to justify unwrap_value: that risks a circular generator argument. Do not expand the entire compile monad or shape_state in consumers. Do not induct on word_count: the compiler emits one runtime loop regardless of its value. Never raise the 2.5-second tactic timeout, use interactive sessions, or wrap search in TRY/ORELSE.

#### Argument
Case analysis on the value separates a returned stack operand from a located value. For located word values, non-code pointer loads produce fresh plain operands. For located non-word values, memory returns the existing plain operand; storage/transient allocate a plain buffer and copy into it; calldata allocates and copies using plain intermediate operands. The storage/transient loop is a finite compiler program producing a runtime loop, not recursive compilation: fresh labels satisfy compiler_label, the fresh counter is plain, and each arithmetic/load/store/control-flow primitive preserves the shape invariant. Carry live source/destination operands across emission using shape_stable_plain_operands and shape_step_frame. The cenv assumption is stronger than needed here; type_memory_bytes can remain an arbitrary natural number throughout.

#### Definition design
No new or changed definitions. Boundary interfaces use shape_step with plain-operand pre/postconditions, and a non-LocCode condition for pointer load and ensure-in-memory. The primitive helper proofs are the initial interface probe: they must compose through frame/consequence without unfolding compile-state semantics. If primitive instruction admissibility or loop label rules fail, report that precise obligation rather than weakening the target.

#### Code structure
Put every new helper directly above unwrap_value_shape in lowering/proofs/loweringShapePropsScript.sml, in dependency order. Do not edit other theorem statements/proofs, definitions, loweringShapeDefsScript.sml, or compiler sources. Reuse existing lemmas before introducing helpers; no new theories or duplicate specialized versions. Keep subproofs small and use the existing shape_step calculus rather than a custom automation library.

### C1.1: Non-code load and buffer-allocation boundary lemmas
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Non-code pointer loading is four direct emit_op cases; buffer allocation is emit_op ALLOCA followed by return. These directly test the existing framework at the required boundary.

#### Summary
Prove compile_ptr_load_shape for non-code locations and compile_alloc_buffer_shape. Use the existing emit_op and return rules, not compiler-state expansion. Check that no equivalent helper already exists before adding these two outputs.

#### Statement
Required interfaces (universally quantify free parameters):
1. loc <> LocCode ==> shape_step internal compiler_label (\st. plain_operand st op) (compile_ptr_load is_ctor loc op) (\x st. plain_operand st x).
2. shape_step internal compiler_label (\st. T) (compile_alloc_buffer size) (\buf st. plain_operand st buf.buf_operand).

#### Approach
Split loc for the first helper and simplify compile_ptr_load_def; discharge instruction-shape premises of shape_step_emit_op for MLOAD, SLOAD, TLOAD and CALLDATALOAD. For allocation unfold only compile_alloc_buffer_def, compose ALLOCA and return, using consequence to remove the trivial frame. Use the existing lowered_inst_ok and opcode-shape definitions only for these primitive side conditions.

#### Not to try
Do not include LocCode under either constructor flag. Do not add separate load lemmas for each opcode when one location-dispatch lemma suffices.

### C1.2: Storage/transient word-copy loop shape
- Kind: `proof_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The generator is a fixed monadic sequence, not an executed recursive loop. State-conditioned emission boundaries isolate the repeated consequence and non-label reasoning.
- Dependencies: C1.1
- Progress transition: `refinement`

#### Progress note
Preserves the loop obligation from C1.2; no loop proof has yet been completed. Adds a strict prerequisite interface instead of repeating emission plumbing.

#### Summary
Prove shape preservation of storage/transient-to-memory word copying. First expose state-conditioned emission rules that accept the invariant used at bind sites. Then compose the fixed generator with existing fresh-label, fresh-var, new-block, pointer-load and pointer-store rules. No compiler definitions or sibling proofs are changed.

#### Not to try
Do not expand compile-monad state updates in the loop proof, prove runtime iteration properties, or copy the C1.1 consequence proof at each emit. Do not require unconditional lowered_inst_ok for arbitrary operands that may syntactically be labels.

#### Argument
The generated control-flow loop is a finite straight-line compilation computation. Preserve plainness of source and destination operands throughout; after fresh_var also preserve plainness of Var counter_var. Fresh labels satisfy compiler_label, allowing new_block. Each arithmetic/load result is plain, stores and control instructions preserve the invariant, and the final exit block preserves shape. No invariant about the runtime counter value or number of loop iterations is needed.

#### Definition design
Introduce no definitions. The key boundary accepts a stable predicate P and instruction validity conditional on P at a state, rather than requiring unconditional validity before plain-input assumptions are available. This resolves the label-operand issue once for all emit sites. Existing shape_step rules remain the trusted primitive interface.

#### Code structure
All new helper theorems go directly above unwrap_value_shape in loweringShapePropsScript.sml. Put the two emission boundaries before the loop theorem. Use named suspend/Resume branches inside the loop proof for readable grouping if necessary; do not introduce theory files or ML proof automation. Do not refactor C1.1 as part of this scoped change.

### C1.2.1: State-conditioned emission boundary rules
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: These are direct semantic consequences of existing emit rules: freeze instruction validity from the initial state and reuse stable P as the frame.

#### Summary
Add exactly two generic consumer-facing rules, one for emit_op and one for emit_inst. Both take the consumer's stable predicate directly. Instruction well-formedness and operand admissibility are checked under that predicate, eliminating unconditional label case splits at consumers.

#### Statement
Prove shape_step_emit_op_under:
!internal LP P opc ops.
 shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM] /\
 (!st. P st ==> EVERY (label_or_plain st) ops /\
                    (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs))) ==>
 shape_step internal LP P (emit_op opc ops)
   (\x st. P st /\ plain_operand st x).

Prove shape_step_emit_inst_under:
!internal LP P opc ops outs.
 shape_stable P /\ ~MEM opc [GAS; RETPC_PARAM] /\
 (!st. P st ==> EVERY (label_or_plain st) ops /\
                    (!id. lowered_inst_ok internal (mk_inst id opc ops outs))) ==>
 shape_step internal LP P (emit_inst opc ops outs) (\x st. P st).

#### Approach
Unfold shape_step_def only at this boundary. For an arbitrary initial state satisfying P, derive the state-independent lowered_inst_ok fact from the conditional hypothesis, then apply shape_step_emit_op or shape_step_emit_inst with R=P and unpack its semantic conclusion. Keep this small local derivation here; consumers apply the resulting rule with irule and simplify their concrete opcode/operand obligations.

#### Not to try
Do not add parallel plain-only wrappers, opcode-by-opcode wrapper families, or an emit_void wrapper without an actual need. The label_or_plain form covers arithmetic, stores, assignments and jumps with one interface. Check existing helpers for the same statement before adding a name.

### C1.2.2: Compose word-copy generation with pure-fact elimination
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: Pure assertions can be moved into the proof context directly from shape_step's definition; remaining generation uses existing emission and stable-frame rules.
- Progress transition: `refinement`
- Carries progress/evidence from: E0004

#### Progress note
Preserves the word-copy obligation; E0004 supplies interface diagnosis, not a completed proof.

#### Summary
Retain the task-scoped word-copy generator proof. Add one general pure-precondition rule to expose allocated-label facts. Use existing frame and consequence rules for state-dependent facts; no additional framing machinery is needed.

#### Not to try
Do not unfold shape_step_def in each continuation. Do not assume a fact in a prepredicate has automatically become a HOL assumption. Do not prove runtime loop termination or duplicate existing framing rules.

#### Argument
This is a finite compile-time sequence, not induction over runtime loop iterations. Fresh labels yield pure compiler_label facts, which can be extracted into the HOL context once. Plain operands and nonfresh counter variables persist through shape extension; emitted branches and block creation then use the label facts independently of the state invariant.

#### Definition design
Do not change definitions. The new interface converts a conditional shape_step proof into a judgment with that pure condition in its precondition. Normalize conjunction order with consequence when fresh_label supplies R st /\ compiler_label l. Existing shape_step_frame transports stable state facts across load and arithmetic generation.

#### Code structure
Place the pure-precondition lemma and word-copy helper immediately above unwrap_value_shape in loweringShapePropsScript.sml, after existing emission-under helpers as appropriate. Do not edit loweringShapeDefsScript.sml or compiler files.

### C1.2.2.1: Expose pure preconditions at the shape-step boundary
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: Immediate from the universally quantified semantic judgment by assuming its pure precondition.

#### Summary
Prove one general pure-assumption rule. It permits fresh compiler_label facts to enter the HOL context. Keep all semantic unfolding confined to this helper.

#### Statement
Theorem shape_step_pure_pre:
  !internal LP b P m Q.
    (b ==> shape_step internal LP P m Q) ==>
    shape_step internal LP (\st. b /\ P st) m Q

#### Approach
Unfold shape_step_def only here; introduce quantified state/run hypotheses and the pure condition, then specialize the assumed judgment. Check the local helper region for an equivalent rule first and reuse it rather than adding a near-duplicate.

#### Not to try
Do not add separate left/right-conjunction variants: consequence and conjunction simplification handle orientation.

### C1.2.2.2: Complete the existing task-scoped word-copy boundary proof
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The missing pure-label interface is supplied by the preceding helper; the rest is finite primitive composition under stable invariants.
- Dependencies: C1.2.2.1, C1.2.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0004

#### Progress note
Continues the original C1.2.2 word-copy obligation; no completed proof is being certified or reused.

#### Summary
Complete the original word-copy shape helper for the two task-required source-location cases, keeping its intended statement and scope. Compose label allocation, initialization, conditional/body/exit blocks, pointer load/store, and counter update. Preserve the emission-under interface already proved in C1.2.1.

#### Approach
After each fresh_label bind, use consequence to order its postpredicate as compiler_label l /\ R st, then apply shape_step_pure_pre and introduce the pure fact before proving the continuation under R. Carry source/destination operands and counter freshness in a stable invariant; frame that invariant over pointer load, and frame plain_operand of val_loaded across destination-offset arithmetic, using shape_step_frame and shape_step_conseq to reassociate conjunctions. Apply existing emission-under rules and shape_step_new_block using labels now in context; check the resulting theory at the default per-step timeout.

#### Not to try
Do not broaden the original source-location scope, introduce new compiler definitions, or unfold shape_step semantics at loop consumers. Do not use large manual theorem instantiations to extract conjuncts; normalize pre/postconditions via consequence and use the pure rule for state-independent facts.

### C1.3: Ensure-in-memory boundary for all non-code locations
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 2
- Work units: 8
- Rationale: Location case analysis reduces to return, the established loop helper, or short fixed emission sequences. Allocation sizes and copy counts impose no additional shape side conditions.
- Dependencies: C1.1, C1.2

#### Summary
Prove compile_ensure_in_memory_shape with arbitrary allocation size and word count. Storage/transient singleton copies use a load and MSTORE; other counts use the loop lemma. Calldata follows CALLDATALOAD, allocation, MSTORE, two ADDs and CALLDATACOPY. The final allocated operand remains plain by stable framing.

#### Statement
loc <> LocCode ==> shape_step internal compiler_label (\st. plain_operand st ptr) (compile_ensure_in_memory ptr loc mem_bytes word_count is_ctor) (\op st. plain_operand st op). Universally quantify all parameters.

#### Approach
Split loc and unfold compile_ensure_in_memory_def only in this helper. For storage/transient split word_count = 1, use C1.1 and C1.2 (unfolding the thin compile_storage_to_memory/compile_transient_to_memory wrappers), and frame the allocated pointer across the copy. In calldata retain ptr and len_op across allocation, then buf, length, data_ptr and src_data as needed; use emit_void for CALLDATACOPY and return buf.

#### Not to try
Do not constrain mem_bytes, word_count or the calldata length: shape preservation does not require semantic bounds. Do not duplicate the loop proof for storage and transient, or prove the unreachable code-copy branch.

### C1.4: Integrate unwrap proof and validate task completion
- Kind: `proof`
- Risk: 1
- Work priority: 3
- Work units: 3
- Rationale: With the two dispatch boundaries proved, the target is value/location case analysis and precondition weakening. The final build and audit are mechanical.
- Dependencies: C1.1, C1.3
- Checkpoint: yes

#### Summary
Replace only the target cheat with a proof of the exact frozen statement. Derive plain input and non-code location from value_shape_ok. Run holbuild -j1 build loweringShapePropsTheory with the default tactic timeout. Audit helper uniqueness, unchanged protected code and absence of new cheats; other task-exempt theorems remain untouched.

#### Statement
!cenv v internal. shape_step internal compiler_label (\st. cenv_shape_ok st cenv /\ value_shape_ok st v) (unwrap_value cenv v) (\op st. plain_operand st op)

#### Approach
Split v and then is_word_type for located values. Stack and non-word memory use shape_step_return; word locations use C1.1, and other non-word locations use C1.3 through shape_step_conseq, extracting the required facts from value_shape_ok_def. Keep type_memory_bytes opaque, perform the requested build, and compare the final changed symbols and remaining cheats against TASK restrictions.

#### Not to try
Do not alter the statement despite the source comment saying weakly frozen: the TASK explicitly freezes it. Do not repair or prove other cheated lemmas as part of final validation. If a real counterexample emerges, stop and seek a checked counterexample plan rather than modifying the theorem.
