# Source constant evaluation and frontend boundaries

The source frontend computes compile-time values from original expressions,
rather than trusting the compiler's `folded_value` or `folded_literal` fields.
This is the constant-evaluation boundary tracked by #135, not a claim of complete
source parsing, independent type inference or compiler correctness.

## Phase structure

1. **Retain syntax.** Capture the program before qualifier erasure and semantic
   analysis. Keep constant initializers, annotation bounds, defaults, decorators,
   executable children and module identities in `sourceSyntax`.
2. **Resolve identities and dependencies.** Resolve lexical/module names and
   builtin identities before evaluation. Compute constant dependencies, including
   forward and imported references; reject duplicates, cycles and unresolved
   names rather than treating them as dynamic values.
3. **Evaluate source constants.** The partial HOL evaluator distinguishes
   `SC_Value`, `SC_NotConstant`, `SC_Invalid` and `SC_Unsupported`. Only a value
   satisfies a required constant position. Compile-time child evaluation is
   eager: a dynamic sibling or runtime short-circuit cannot conceal an invalid
   constant child.
4. **Resolve types and reify executable values.** Resolve original annotation
   bounds using mathematical values. Validate supported source domains and
   runtime representability before emitting typed literals. A computed value
   alone does not establish that its original expression was legal.
5. **Check exact modules.** Retain `SourceRetained original modules`, and apply
   `check_contract T` to those same modules, including deployment bodies.
   Compilation, when requested, must consume precisely the checked modules.

Source arithmetic is distinct from bounded runtime arithmetic. For example,
`uint256[((1 << 256) >> 255) + 1]` has bound 3; intermediate annotation values do
not wrap at 256 bits. Executable expressions retain their width/domain checks.
Normalizing `x ** (1 + 2)` produces a literal exponent 3 before runtime lowering,
while preserving the original addition in the retained source. Likewise,
`method_id` and literal-required ABI options are computed before their syntax is
erased into runtime literals or builtin parameters.

Decimal rounding, the conservative host-logarithm power boundary, supported
builtin domains and value-reification assumptions are specified in
[sourceConstCore.md](sourceConstCore.md),
[sourceConstBuiltin.md](sourceConstBuiltin.md) and
[sourceConstValue.md](sourceConstValue.md). These are local HOL specifications;
they do not themselves prove equivalence to the Python implementation.

## Ordinary public route: paired hybrid normalization

The ordinary `vyperCheckContractFrontendLib` APIs use
`sourceOrdinaryProgramLib`. Their input is
`{fuel, paired, inherited, address}`:

- `paired` comes from `sourceOrdinaryClaimsLib.pair_program`: a pre-erasure
  loader record, its original JSON and matching annotated JSON.
- `inherited` supplies module/nominal trust, runtime translation `contexts` and
  storage `layouts`. It supplies neither replacement constant values nor
  executable bodies.
- Module trust fixes canonical runtime IDs, nominal identities/definitions and
  storage slots. Registry keys must agree with those identities; runtime IDs are
  unique and the main module has ID `NONE`. This is explicit inherited trust,
  not independently established source identity or layout inference.

Pairing removes folded fields recursively before decoding annotated claims. It
checks source constructors, spelling, values, child/keyword/declaration order
and origin identities, retaining original qualifier wrappers despite compiler
erasure. Malformed present claims and source mismatches reject. Two narrow
serialization exceptions remain explicit: matched Decimal spellings may differ
only with exact value equality and valid precision, retaining the original
precision/token; `Bytes[INF]` is confined to original `msg.data` syntax. Imported
nominal claims use inherited canonical qualified identities.

Normalization traverses original declarations, statements and expression
children. Constants, declaration bounds, initializers, defaults, range limits,
tuple indices, ABI flags/selectors and standalone `method_id` use the common
source evaluator. Nonmigrated runtime forms are rebuilt with inherited
type/import/dispatch claims. This **hybrid route is not independent general
source type inference**.

Residual classification occurs before evaluation. Unsupported residual parents
still normalize their executable children; only a genuinely nonconstant outcome
permits residual expression recursion. Invalid, unsupported or exhausted source
evaluation is never retried using compiler folds or whole-program legacy
translation.

```sml
val checked = vyperCheckContractFrontendLib.check_contract_result
  {fuel = ``80:num``, paired = paired_program,
   inherited = {trust = module_trust, contexts = runtime_claims,
                layouts = storage_layouts},
   address = ``0w:address``};
val phase = #equation (#elaboration checked);
val checking = #theorem checked;
val composition = #composition checked;
```

Public entry points:

- `prepare_check_input` returns the pairing, elaboration and actual checker input.
- `check_contract_result` returns those equations, the exact modules and checker
  artifact; `check_contract` returns the checker theorem.
- `check_contract_file_result` / `check_contract_file` take `original_path`,
  `annotated_path`, `fuel`, `inherited` and `address`, and use the same route.
- `compile_checked` and `source_ordinary_compile_equations` expose a successful
  backend callback's equation for exactly those checked modules. They do not
  assert that compilation succeeds for every checked program.

Pairing/projection and phase equations certify computations on decoded HOL
terms. They do not prove the ML decoder, capture tool or source-file authenticity.

## Other entry points and legacy isolation

The base exposes only the ordinary paired route and explicit legacy routes.
The independent full-Source body frontend, its strict JSON adapters and aliases,
and the optional Meaning tower have been extracted. The facade does not load
those developments. See [sourceModule.md](sourceModule.md) for the retained
signature/context interfaces and [sourceModuleLoader.md](sourceModuleLoader.md)
for the pre-erasure protocol still used by ordinary pairing.

Explicit `*_legacy` ordinary APIs retain annotated-only translation and its
older metadata consumers, including some Name, annotation, range and specialized
keyword handling. `check_constant_contract_file_legacy` retains the old bounded
integer evaluator. These are distinct compatibility interfaces, never automatic
fallbacks. Legacy/source whole-module AST equality is not promised: the legacy
initializer may retain arithmetic where the source route emits its value.

Do not extend legacy trust with generic operator/call folded-value wrappers or
make `json_expr_int_opt` follow compiler replacements. Missing constant support
belongs in source evaluation. ABI keyword extraction must distinguish absence
from an invalid present value instead of silently choosing a default.

## Semantic and compiler guarantees

Retention, checking and compilation equations are not definitions of source
meaning. This base does not include the independent full-program/call/location
Meaning relations or an artifact-semantic adapter. Restoring the optional
feature requires reversing its extraction commit; no semantic conclusion is
silently substituted for it here.

At the checked ordinary boundary,
`sourceOrdinarySupport.source_ordinary_checked_remainder` and
`source_ordinary_compiled_supported_program` use genuine checking to discharge
redundant MethodId/Exp/Exp-AugAssign source-domain gates. The underlying
`sourceProgramSupport.checked_program_remainder` states that successful
checking makes `source_program_remainder tops` equivalent to
`supported_program tops` for a member module. All unrelated lowering restrictions
remain. Existing lowering admissions are not discharged by this extraction;
exact compiler equations are not an unrestricted, admission-free bytecode
correctness theorem.

## Further reference and regression entry points

- Syntax and identities: [sourceSyntax.md](sourceSyntax.md),
  [sourceResolve.md](sourceResolve.md), [sourceConstEnv.md](sourceConstEnv.md).
- Type and expression contracts: [sourceType.md](sourceType.md),
  [sourceExpr.md](sourceExpr.md).
- Public regression and fixture-generation workflow:
  [ordinary frontend tests](../tests/sourceOrdinaryAcceptance.md).
- Ordinary bytecode comparison: `sourceOrdinaryProgramParityTest` uses the
  retained `sourceBytecodeFixtureLib` pinned deploy/runtime fixtures.

Regression assertions should compare complete normalized modules, checker
artifacts and equations under deleted and well-formed poisoned folding metadata.
Invalid originals must remain rejected even with plausible replacements. Exact
backend equations, execution checks and semantic transport are separate
obligations; finite examples and old build outputs do not establish universal
coverage or validate a changed checkout.
