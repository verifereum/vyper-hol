# C1.13: unchanged-frame/module interface audit

## Checked boundary

`bodyPtrWordBuiltinsFrame.body_inv_stmt_state_rel_unit` is proved and built
independently. It extracts precisely the actual runtime/deploy unit, equality
of ctx, policy target equality, and exact function lookup. Duplicate search
found no existing combined boundary. It uses the existing proved
`bodyPtrWordBuiltinsContext.stmt_state_rel_lookup_function`, not alloca_room
internals. No target statement or precondition changed.

`bodySimScript.sml:61-87` supplies the unit existential and selected compile
environment fields, including `ce_is_ctor <=> cx.in_deploy`. Thus the
`~cenv.ce_is_ctor` premise of `bodyPtrDefsScript.sml:219-231` rules out deploy
at an expr_sim_ptr use site. The frame does not equate the whole cenv with
a package's environment, nor mention the expression's source occurrence.

## Construction boundary (definitions, not a certificate theorem)

`defs/compileVyperScript.sml:1402-1429` classifies tops, packages external,
internal and fallback functions, installs the policy target, checks return
buffers/allocation bounds and calls run_lowering.
`defs/vyperCompilerScript.sml:630-649` generates runtime code, extracts the
context with internals and checks lowering_context_ok. The lookup boundary
therefore constrains func to this actual extracted context. It does not
supply a must-scalar dataflow solution or associate sa with the package
compilation history. Merely expanding this construction would not prove
such an association.

## Proposed mathematical certificate interface (not implemented)

For the unchanged ctx and func and the particular lower_value equation
`lower_value compile_expr cenv ty e sa = (op,sb)`, a certificate must provide
a predicate I on (G,s) with these three obligations:

1. Every initial frame allowed by the operand judgment satisfies I(G0,s0).
2. I(H,s) and a normal gas_path_ptr_edge from (H,s) to (J,u) imply I(J,u),
   including arbitrary revisits before the witness stops.
3. I(G,t) and t's PC equal to (sb.current_bb,LENGTH sb.current_insts)
   imply op_prov G op = NONE.

The already proved `gas_path_ptr_normal_invariant`
(bodyPtrWordBuiltinsDataflowScript.sml:5-20) transports precisely (1,2) to
any normal counted-path endpoint. It does not synthesize I or give (3).
The finite example's `word_interval_operand_path_scalar`
(bodyPtrWordBuiltinsIntervalDataflowScript.sml:204-220) proves this interface
only for its concrete expression/environment/function.

| Required fact | Available boundary / unresolved obligation |
|---|---|
| Actual containing function | Checked extraction theorem above; exact lookup, not merely same name |
| Initial scalar variables | ghost_inv (bodyPtrDefs:80-93) constrains local pointer coverage, return buffer/PC and storage taint, not all scalar registers. Choosing an initially empty must-set works for the finite example; a general initialization remains unproved |
| Ordinary instruction transfer | ghost_step_scalar_set (bodyPtrWordBuiltinsScalar:45-59) handles non-ALLOCA/non-DALLOCA/non-PARAM/non-INVOKE, and needs scalar inputs for ADD/SUB/ASSIGN. It is proved, but no general module fact establishes its hypotheses |
| Calls | INVOKE is explicitly excluded from that helper. A caller/callee scalar return and ghost transport interface is required, not obtained from lookup membership |
| Entry PHIs | Finite example proves no PHIs and entry_prov identity (IntervalDataflow:53-57,147-155). General code requires a join/entry transfer theorem or certified exclusion; neither follows from current extraction |
| Output identity | Finite example computes op=Var "%6" and exact endpoint (IntervalDataflow:28-39). For arbitrary lower_value, endpoint membership in a must-set must be proved separately |
| Arbitrary interval alignment | expr_sim_ptr universally quantifies sa,sb,op (bodyPtrDefs:219-231). fn_has_code (fragExec:112-118) constrains emitted blocks and a final prefix, not historical source occurrence. body_inv does not supply occurrence alignment or equality of complete cenv |

The existing S1 facts permitted even when locally admitted establish value
simulation, not the missing scalar ghost provenance certificate; no new
admission is used in the extraction. This audit's searches did not locate
a module-wide must-scalar synthesis theorem. This is a bounded search
finding, not a nonexistence theorem.

## Go/no-go

No-go for using a certificate *only for historical source occurrence outputs*
without a separate alignment theorem. A source-occurrence-independent
invariant could in principle avoid historical matching, but it must establish
(3) for every arbitrary compiling interval admitted by fn_has_code and the
current cenv. Lookup membership alone establishes none of that output
identity. No such universal certificate has been validated here. Proceeding
would require strategist authorization and de-risking of this missing
interface, not a large compiler induction smuggled into this probe.

This is successful diagnostic evidence, NOT a counterexample to the frozen
target. No falsehood or tight sufficient repair is asserted.
