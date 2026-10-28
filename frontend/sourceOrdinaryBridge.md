# #543 ordinary frontend: implemented hybrid bridge

The clean ordinary API now uses `sourceOrdinaryProgramLib`, not annotated-only
legacy translation or the broader full-Source body-typing gate. The bridge
normalizes #543 consumers with the common verified source evaluator and rebuilds
residual runtime nodes with explicitly inherited type/import/layout claims.
It preserves supported dynamic forms such as `concat`; it does not add general
builtin inference, full #135 acceptance, source semantics or backend correctness.

## Input and pairing

`sourceOrdinaryProgramLib.input` contains `fuel`, `paired`, `inherited` and
`address`. `paired` comes from `sourceOrdinaryClaimsLib.pair_program`: a genuine
pre-erasure loader record plus its original JSON and matched annotated JSON.
`inherited` supplies `trust`, runtime `contexts` and `layouts`, not executable
bodies or replacement constant values.

The zipper removes folded fields recursively before decoding claims. It checks
source constructors, spelling, values, child/keyword/declaration order and origin
identities; malformed present claims and mismatches reject. Original qualifier
wrappers are retained despite compiler erasure. Projection and shape equations
retain the original Source program. These are kernel equations about decoded
terms, not a proof of the ML parser or capture tool.

Two narrow serialization/metadata boundaries are explicit:

- Decimal spellings, including scientific notation, may differ only at matched
  Decimal nodes with equal exact scaled-integer values and independently valid
  precision. The original token and precision remain; no rounding or folded
  value authorizes a match.
- `Bytes[INF]` is allowed only for the matched original `msg.data` syntax used
  by calldata dispatch, not bounded values, nested claims or replacement syntax.

Pinned original/annotated pairs share input bytes and a source-ID registry.
Imported flag claims use canonical qualified identity from the inherited
translation context. This is identity alignment, not independent nominal/type
inference. Regenerated pairs match all 26 retained ordinary cases.

## Normalization and exact outputs

`sourceOrdinaryExpr*`, `sourceOrdinaryStmt` and `sourceOrdinaryDecl` recursively
traverse expressions, statements and declarations. `sourceOrdinaryProgram`
links original modules/policies, resolves source constants and signatures, and
retains `SourceRetained original modules`. Source declaration types/bounds,
constant initializers, defaults and iteration bounds are not inherited values.

Required #543 consumers include source constants, annotation bounds, tuple
indices, ranges, ABI Boolean flags/selectors and standalone `method_id`.
Optional constant subtrees use checked source reification. Residual mode is
selected explicitly before normalization; executable children are still visited,
so a dynamic sibling cannot hide invalid constant arithmetic. Existing calldata,
pop and call dispatch shapes are preserved. Invalid, unsupported or exhausted
source evaluation is not retried through trusted folds or legacy translation.
Nonmigrated runtime typing/import/layout claims remain explicitly inherited.

The public result retains pairing, phase, original-source, linking and genuine
`check_contract T` equations for the exact normalized modules, including
deployment bodies. `source_ordinary_compile_equations` and `compile_checked`
apply a successful backend callback to those same modules. They do not imply
that every checked program compiles or that its bytecode is semantically correct.

## Public API

| Surface | Current route |
|---|---|
| `prepare_check_input`, `check_contract_result`, `check_contract` | Paired ordinary hybrid input; deployment checked. |
| `check_contract_file_result`, `check_contract_file` | Same route, with `original_path`, `annotated_path` and explicit inherited claims. |
| `compile_checked` | Backend equation for the exact ordinary checked modules. |
| Explicit `*_legacy` ordinary names | Annotated-only compatibility route and its old trust. |
| `Source.*` / explicit source APIs | Separate full-Source interfaces; not the ordinary residual bridge. |
| `check_constant_contract_file` | Strict source adapter using the common evaluator; no legacy retry. |

## Recorded finite validation

- **26/26 ordinary cases:** exact complete AST, independent checker artifact,
  fold deletion/poisoning and kernel-closed equations. Aggregate:
  `sourceOrdinaryProgramInventoryTestTheory`; receipt
  `.agent-files/receipts/decimal-inventory-final25.log` (cached completion).
- **36/36 valid retained witnesses:** clean ordinary modules and artifacts are
  identical to the tested Source results, including constructors; folds are
  deleted/poisoned through the public route. The existing independent **40-body**
  meaning inventory therefore has the same runtime ASTs, with its original
  context premises; this is not new arbitrary-program semantics.
  `.agent-files/issue543-ordinary-final-validation.log` records the inventory
  and witness targets built. That combined command later timed out at parity;
  it is not a whole-command success receipt.
- **9/9 ordinary deploy/runtime parity certificates:** separate successful
  `sourceOrdinaryProgramParityTestTheory` build in
  `.agent-files/issue543-ordinary-parity-final.log` (186.850s).

The wider retained matrix remains **32 matches / 4 external failures / 1 expected
rejection**; these finite successes do not turn it green. See
[ordinary inventory](../tests/sourceOrdinaryProgramInventory.md) and
[scoped checklist](../.agent-files/issue543-scoped-checklist.md).
`sourceOrdinaryProgramMeaningTest` now exports 40 kernel-linked ordinary
body-meaning certificates and nine actual compile/body compositions.
`sourceOrdinarySupport` discharges the redundant source-domain gates at this
clean ordinary checker/compiler boundary. Final forced builds, combined scoped
regressions and strict export audits pass; receipts are listed in
[implementation status](../docs/ISSUE_543_IMPLEMENTATION_STATUS.md). No full
#135, unrestricted backend or global-parity-green claim is made.
