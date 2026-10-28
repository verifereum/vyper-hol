# #543: source-constant acceptance and consumer inventory

## Current scoped audit (supersedes baseline status below)

The user's scoped #543 checklist is verified. This is the current
whitelist/status ledger; §§1–5 preserve the original stage-1 audit, including its then-unknown
results and historical matrix. They are not current failure/coverage claims.
Current receipts are mapped in
[implementation status](ISSUE_543_IMPLEMENTATION_STATUS.md) and
[the scoped acceptance checklist](../.agent-files/issue543-scoped-checklist.md).
Final build, forced-proof, export-audit and parity receipts are linked there;
this document does not claim unrestricted backend or full #135 correctness.

### Exact checker-to-whitelist replacements

The exported contract in `lowering/sourceProgramSupportScript.sml` is:

```text
check_contract T layouts address mods = SOME art /\ MEM (src,tops) mods
  ==> (source_program_remainder tops <=> supported_program tops)
```

`source_program_remainder` is transparent, not an opaque readiness predicate.
It removes **only** the MethodId/Exp builtin gates and the Exp AugAssign literal
operand gate. Integer-width restrictions, all other operators, ABI forms,
headers/names, binding/loop/effect/storage restrictions remain unchanged.
The old `supported_program` definition is not deleted: the new checked wrapper
no longer asks its caller to supply these redundant #543 gates independently.

| Discharged #543 assumption | Named replacement and exact boundary |
|---|---|
| Residual runtime MethodId exclusion | `sourceBuiltinSupport.typed_method_id_rejected`; `sourceElaborationSupport.source_expr_method_id_erased` connects successful source elaboration to runtime rejection. Valid source selectors are reified; `method_id_var` still rejects. |
| Exp literal-base/nonnegative-literal-exponent gate | `vyperTypeSystem.well_typed_power_operands` / `well_typed_power_arguments`, then `sourceBuiltinSupport.typed_power_support` / `typed_builtin_remainder`. `supported_integer_type (expr_type base)` is **retained**. The fact comes from genuine expression checking, not assumed JSON normalization. |
| Exp AugAssign literal exponent gate | `vyperTypeSystem.type_stmt_power_augassign_exponent`, then `sourceStmtSupport.checked_aug_binop_remainder`. Supported integer types/targets and pure RHS restrictions remain. |
| Recursive expressions and statement environments | `sourceExprSupport.checked_pure_remainder`, `checked_effect_remainder`, `checked_expr_remainder`; `sourceStmtSupport.checked_stmt_remainder` lifts through actual sequentially extended typing environments. |
| Checked function/body/default/program boundary | `sourceProgramSupport.checked_function_body_and_defaults`, `checked_function_defaults_remainder`, `checked_function_body_remainder`, `checked_declaration_body_remainder`, **`checked_program_remainder`**, and singleton implication `checked_remainder_supported_program`. The real `function_entry_env`/`defaults_env` is used. Unchanged declaration headers still exclude defaults; exposing their typing does not admit them to this whitelist. |
| Clean ordinary checker/compiler boundary | `sourceOrdinarySupport.source_ordinary_checked_remainder`, `source_ordinary_checked_supported_program`, and `source_ordinary_compiled_supported_program` apply the replacement to the actual normalized ordinary modules, without admissions. |
| Public source wrapper instead of caller-supplied `supported_program` | `sourceModuleCompile.source_module_checked_supported_program` takes successful policy-aware `source_module_check`, exact `retained_executable = [(NONE,tops)]`, and `source_program_remainder tops`. `source_module_checked_runtime_correct` composes it with existing lowering correctness, retaining every unrelated semantic premise and its inherited CHEAT provenance. |

Nonvacuity and retained-exclusion tests are
`sourceProgramSupportTest.power_program_supported_by_replacement`,
`recursive_aug_program_supported_by_replacement`,
`remainder_local_tuple_still_rejected`, and
`remainder_program_tuple_still_rejected`.
`sourceProgramIntegrationTest.source_support_power_public_replacement` starts
from original source and uses the public replacement lemma, not direct
`supported_program` evaluation. Receipt: `.agent-files/source-support-final.log`;
`.agent-files/source-support-recheck.log` is an unchanged-source cached recheck,
not a fresh proof run.

### Exact retained tuple / ABI / backend obligations

* **Tuple #571:** `sourceElaborationSupport.source_expr_local_tuple_index` and
  `well_typed_local_tuple_index` derive a literal integer index, nonnegativity,
  `Num n < LENGTH ts`, and the selected element type. This is **not** a tuple
  base-lowering proof. `source_pure_expr_remainder` still accepts `Subscript`
  only with `TopLevelName bt id` and `supported_subscript_base tops id` (private
  slotted storage arrays or qualifying nontransient maps). Local `Name (TupleT
  ts) name` bases remain rejected for every index, even a checked literal.
  `supported_local_tuple_read_rejected` and the two remainder tests above make
  this distinction explicit. Source body transport does cover the fixed tuple
  bodies; it does not remove this backend restriction.
* **ABI #551:** `supported_type_builtin_form` is copied unchanged: encode only
  `(AbiEncode F (SOME mid),[a])`, `LENGTH mid = 4`, and
  `target = TupleT [t]` with `supported_tuple_type t`; decode only
  `(AbiDecode F,[a])`, `ty = target`, `supported_tuple_type ty`, and at least
  two tuple fields. Recursive argument restrictions also remain. Source flag/
  selector validation and interpreter ABI capture/staging transport do not prove
  general backend argument staging, wrapping/unwrapping or effect preservation.
* **Unrelated backend:** headers/names/dispatch, supported types/widths,
  memory/storage/calls, deployment/initialization/layout and other arithmetic
  obligations are retained, not new #543 source-semantics tasks.
  `source_module_checked_runtime_correct` explicitly retains
  `lower_vyper_runtime_unit ... = SOME unit`, `source_typing_ok`,
  `source_storage_ok`, `source_deployment_rel`, `valid_vyper_call`,
  `initial_venom_state_rel`, and `call_outcomes_ok`. It inherits
  `lower_vyper_runtime_unit_correct`'s admission; it is not a kernel-only
  whole-compiler theorem or a `compile_vyper` bytecode equality theorem.

### Relevant old lowering admission: Exp is now proved

The old admitted combined Exp/ExpMod `binop_frag_pow` statement is preserved
in a comment, **not exported**. Its Exp part is replaced by the proved
`exprSimBinopFrag.binop_frag_pow`: literal options **and evaluated operand
values come from the same checked AST**. The chain is
`powerCheckedProps.checked_power_run` → `powerFragProps.binop_frag_power_run`
→ `binop_frag_pow` → `exprSimOperators.compile_bop_word_with_frag_sim` /
`compile_power_case_sim`; `compile_bop_case_sim` dispatches Exp separately.
The scoped audits are clean. `binop_frag_expmod` remains admitted, and general
operator dispatch retains unrelated admissions. Do not require general
arithmetic or all #572 to close this Exp-only ledger item. Exact receipt:
[power-exp-integration-final](../.agent-files/power-exp-integration-final.md),
`.agent-files/receipts/power-scope-regression-final.log` (seven fresh build targets). Those seven
**build targets** are not the seven **parity fixtures** below.

### Source/runtime context and actual compiler-artifact audit

The former 19-body gap is closed: all **40 original bodies**, including both
constructors, have independent source derivations, structural code certificates
against actual retained declarations, and complete outcome/final-state equality.
Exact exports in `sourceMeaningLocationWitnessTest` for each `witness_function`
are `*_original_body`, `*_body_code`, `*_body_transport`, plus
`witness_constant_dependencies_meaning`, `witness_original_global_metadata`,
and `*_original_parameters`. The generic theorem is
`sourceMeaningLocationBody.source_location_body_code_evaluates`.
Its explicit condition is **`get_tenv cx = FEMPTY`** for these fixtures;
argument cells/module context/layouts are not synthesized by body entry.
No arbitrary module, callee, getter or deployment simulation is inferred.

There is no missing `compile_vyper` equality in the **nine certified finite
programs**: `sourceModuleParity.<name>_exact_checked_backend`,
`<name>_python_parity`, and `<name>_composition` retain it for the exact same
singleton `tops`. Both the location fixture helper and parity helper reuse
`sourceModuleFrontendLibTest.source_module_<name>_ast`, checking that its LHS
matches freshly decoded original syntax. Thus finite artifact composition is
ordinary substitution/conjunction of that phase, its `source_module_<name>_check`
checker equation, the body transport, and
`sourceModuleCompile.source_module_compile_equations`. It requires membership
of the selected `FunctionDecl` in **that** retained `tops`, not an assumed
meaning for every module. No new universal wrapper theorem is needed for this
ledger, and no new all-40 bytecode-simulation theorem is claimed.

For any of the **fixed 40** body certificates, the minimal conditional
composition is: successful `source_module_compile ... P ... = SM_Ok (R,art,bytes)`
with `retained_executable R = [(NONE,tops)]`, and membership of that certificate's
`FunctionDecl ... ss` in `tops`, retains `retained_source R = P`,
`check_contract T layouts address [(NONE,tops)] = SOME art`,
`compile_vyper finalizer policy tops = SOME bytes`, and
`!cx. get_tenv cx = FEMPTY ==> eval_stmts cx ss = source_location_runs cx ms`.
Here `P`, `ss`, `ms` and the original-source derivation are the fixed fixture's
certified terms, not arbitrary caller-supplied source semantics. This is a
logical conjunction of existing contracts, **not a newly exported theorem**.
Compiler success is an explicit premise; membership is in the same retained
program, not permission to substitute a different compiled body. A missing
successful backend artifact is not a missing source-context lemma.

For other retained programs the matrix records actual backend equations and
failures; do not postulate compiler success for all 36 accepted sources.
`sourceMeaningProgram.source_meaning_compile_entry` and
`sourceMeaningCompile.source_meaning_compile_program` remain the smaller
body-entry / independently derived call/default/constructor compositions, not
universal all-40 call/deployment coverage. `sourceMeaningPolicy` and
`sourceMeaningModules` cover their stated policy/imported-entry frontiers only.
The context hypotheses above and inherited type/import/layout claims remain
visible; they do not require expanding this task to full #135 semantics.

### Required passing set versus external failures

The required seven source-driven parity fixtures are `fold_add`,
`pow_folded_exp`, `fold_cmp`, `enc_mid_const`, `fold_powmod`, `fold_addmod`, and
`fold_abs`. All pass; adding `fold_not` and `boolop_and3` gives **9/9 exact
source-wrapper deploy/runtime certificates**. All **36 valid sources**
elaborate and pass `check_contract T`; `method_id_var` rejects. The recorded
both-output overflow tests give **4/4 REVERTs**. The full 37-row parity matrix
is nevertheless **32 matches / 4 failures / 1 expected rejection**, exit **1**:
`i12_immut_with_storage` and `p29_imm_multi` return backend NONE (#563);
`rc09_abi_encode_data` mismatches (#554/#551);
`rr03_abi` mismatches (#567/#551). These are externally owned failures,
not required-seven failures or successful parity. See
[SOURCE_MODULE_PARITY_RESULTS.md](SOURCE_MODULE_PARITY_RESULTS.md) for identities
and commands; this documentation audit does not refresh those receipts.

### Implemented ordinary bridge and final audit

The clean ordinary public names now route through the paired hybrid
`sourceOrdinaryProgramLib`, with recursive expression, statement and declaration
normalization (`sourceOrdinaryStmt` / `sourceOrdinaryDecl`). Annotated-only
compatibility is explicit `*_legacy`; no Source failure retries trusted metadata.
Residual runtime type/import/layout claims remain inherited, not independently
inferred. See [the bridge](../frontend/sourceOrdinaryBridge.md).

Pairing strips folds before decoding claims, retains original syntax and checks
source/claim shape and identities. Decimal/scientific serialization differences
require exact scaled-integer equality and valid precision, retaining the original
token; `Bytes[INF]` is confined to matched original `msg.data`. Imported flag
metadata uses canonical qualified identity. Regenerated pinned pairs match 26/26.

| Current ordinary gate | Recorded evidence |
|---|---|
| All 26 ordinary cases | Exact complete AST, independent checker artifact, delete/poison invariance and kernel-closed equations. `.agent-files/receipts/decimal-inventory-final25.log` is a successful cached inventory completion. |
| All 36 valid retained witnesses | `sourceOrdinaryProgramWitnessTestTheory` checks exact ordinary/Source modules and artifacts plus fold invariance. `.agent-files/issue543-ordinary-final-validation.log` records inventory and witness targets built; the combined command later timed out at parity. |
| Nine ordinary exact deploy/runtime certificates | Separate successful `sourceOrdinaryProgramParityTestTheory` build in `.agent-files/issue543-ordinary-parity-final.log`, 186.850s. |

The 36 exact AST equalities preserve the existing independent **40-body** meaning
scope, including its `get_tenv cx = FEMPTY` context premise; no new universal
call/deployment or bytecode-semantics theorem is implied.
`sourceOrdinaryProgramMeaningTest` now exports 40 kernel-linked ordinary-body
certificates and nine actual compile/body compositions. Final forced builds,
current combined regressions and scoped export audits pass; see implementation
status for receipts. No neighboring full #135 semantics, inference, nested-call/
getter, general arithmetic or backend completion is claimed. The wider matrix
remains 32 matches / 4 external failures / 1 expected rejection, not global green.

## Historical stage-1 status and evidence boundary

This is the stage-1 design/coverage table for `.agent-files/PLAN.md`, not an
implementation or a correctness certificate. Audited repository revision:
`2fb2f375f6a001b7a6ba3ccc8c8ba87538768512`.
`git -C /home/lukasz/vyper rev-parse HEAD` equals `VYPER_PIN`:
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`; that checkout's
`git status --short` was empty. Upstream paths below are relative to that
checkout. HOL paths are relative to this repository. No implementation files
were changed and no HOL build, new elaborator, parity run or EVM execution was
performed for this document.

Evidence is deliberately separated:

* **P (fresh Python acceptance):** all 37 retained sources were submitted to
  the pinned checkout's compiler, including annotated-AST generation and both
  bytecodes. 36 compiled; `method_id_var` raised `StructureException: Value must
  be a literal`. This is a source-language acceptance observation, **not HOL
  checker/parity success**. Python was 3.14.4, not the historical oracle's
  3.11.11. Immutable bare-name access produced deprecation warnings, not errors.
* **H (historical HOL evidence):** the local evidence archive was checked with
  `python3 lowering/defs/bytecode/verify_folded_evidence.py
  .agent-files/folded-value-evidence.tar.gz`. It returned
  `VERIFIED_HISTORICAL_EVIDENCE`: 737 files, source revision
  `ac6681fe013c4762158d1bc24e9ae206a19781e8`, 30 matches, four mismatches, two
  `COMPILE_NONE`, one expected rejection, four overflow-revert receipts, and
  28/33 attempted corpus targets passed. It also reported current source and
  proof-source drift (including the frontend, lowering, checker and manifest).
  These results are **not current validation**. Archive identity and recovery
  instructions: [evidence manifest](../lowering/defs/bytecode/folded-value-evidence.json)
  and [validation report](../lowering/defs/bytecode/folded-value-validation.md).
* **U (unknown):** every current HOL checker/parity/behavior result for the
  proposed source-driven path. That path is not yet implemented. Checked-in
  seven-fixture proofs and old folded-metadata regressions do not discharge it.

The stage-1 inventory is recorded here; the plan's *freeze gate is not claimed
closed*: the missing boundary regressions and semantic acceptance questions in
§5 must be addressed before evaluator definitions/theorem statements freeze.

### Reproduce P

From the repository root, using an environment with the pinned Vyper dependencies:

```sh
git -C /home/lukasz/vyper rev-parse HEAD
git -C /home/lukasz/vyper status --short
PYTHONPATH=/home/lukasz/vyper /home/lukasz/.local/share/uv/tools/vyper/bin/python - <<'PY'
import hashlib, sys, vyper
from pathlib import Path
from vyper.compiler.settings import Settings, OptimizationLevel
print(sys.version, vyper.__file__)
b = Path('lowering/defs/bytecode')
s = Settings(experimental_codegen=True, optimize=OptimizationLevel.NONE,
             evm_version='prague')
hashes = []
for name in (b / 'folded-value-witnesses.txt').read_text().split():
    p = b / 'folded-value-sources' / (name + '.vy')
    hashes.append(name + ' ' + hashlib.sha256(p.read_bytes()).hexdigest() + '\n')
    try:
        vyper.compile_code(p.read_text(), settings=s, no_bytecode_metadata=True,
            output_formats=['annotated_ast_dict', 'bytecode', 'bytecode_runtime'])
        print(name, 'ACCEPT')
    except Exception as e:
        print(name, type(e).__name__, str(e).splitlines()[0])
print(hashlib.sha256(''.join(hashes).encode()).hexdigest())
PY
```

Observed ordered `name SP source_sha256 LF` manifest digest:
`dba3a75ee707b51e2ba40991c12ca8adee4dac6731439b0ff93403636e665e36`.
The accepted sources' individual hashes also match the retained
`folded-value-oracle/provenance.json` entries. Use the historical pinned
Python/dependency environment and full settings in that provenance for oracle
regeneration; P did not regenerate/replace those fixtures. An initial probe
used the CLI format name `annotated_ast` with the Python API and failed with
`Unsupported format type`; those harness errors were not language rejections.
The successful run above used the API name `annotated_ast_dict`.

## 1. Pinned source semantics: folder is not acceptance

Evidence anchors:

* `vyper/semantics/analysis/constant_folding.py`: `ConstantFolder.run`,
  `_get_constants`, `visit`, and `visit_*` methods (entire file, 240 lines).
* `vyper/ast/nodes.py`: literals 797–945; operators 998–1281;
  `reduced`/`_set_folded_value` 418–435; `Decimal.to_dict` 846–849.
* `vyper/builtins/functions.py`: builtin rules below; signatures and acceptance
  also use `vyper/builtins/_signatures.py` (`_validate_arg_types`,
  `infer_kwarg_types`) and `vyper/semantics/analysis/local.py`
  (`ExprVisitor.visit`, `visit_Call`, approximately 868–871 and 1034–1061).
  The visitor checks original call arguments/keywords as well as folded values.
* Type acceptance is additionally controlled by
  `semantics/analysis/utils.py:validate_expected_type`,
  `semantics/types/primitives.py:validate_numeric_op`,
  `semantics/types/subscriptable.py:TupleT.validate_index_type`, and
  `semantics/analysis/local.py:_validate_range_call`.

| Syntax/rule | Pinned computation/result | Acceptance/error boundary and design requirement |
|---|---|---|
| Child visitation | `visit` visits children before the parent, even Boolean operands that runtime execution could skip; catches `UnfoldableNode`, not all exceptions | `False and (1 // 0 == 0)` must not hide constant division by zero. Preserve source child order; runtime short-circuit order remains distinct. |
| Declarations/names | `_get_constants` retries unresolved declarations until no progress; `Name` uses accumulated constants; `Attribute` follows namespace/module members | Earlier-declaration-only processing is insufficient. A stalled fold is not necessarily a cycle: struct/interface constants can remain valid but unfoldable. Validate duplicates, identities and dependencies separately. Immutables/locals/storage are not constant declarations. |
| Numeric binary forms | Same AST literal class, numeric operands; mathematical integer operations, not runtime-width wrapping; Decimal operations use Decimal/quantization | Result computation alone does not prove original operand legality or target-type fit. Keep intermediate source arithmetic separate from bounded runtime operations. |
| `/`, `//`, `%` | `/` folds decimals; multiplication and division quantize each result to 10 decimal places toward zero (`vyper/utils.py:454`, ROUND_DOWN default); `//` folds integers using `evm_div` (toward zero); remainder has dividend's sign; zero divisor raises `ZeroDivisionException` | Wrong numeric domain may be unfoldable at folder time and rejected by typing later. Do not reinterpret it as valid dynamic arithmetic. |
| `**` | Integers only, negative exponent error; bounded-size heuristic prevents compiler hangs; bases of magnitude ≤1 fast-path; returns Int | Do not formalize the floating-point heuristic as trusted mathematics. Specify explicit resource/error policy if needed. Original type/domain checks still apply. Raw runtime power is a separate #572 obligation. |
| Shifts/bitwise | `<<`/`>>` use unbounded integer shift, constant count restricted to 0…256; `~v = (2**256-1) xor v`; `&`, `|`, `^` use integer operations | Negative/count 257 rejects. Runtime-width truncation must not determine a source bound. Type restrictions (including 256-bit shift operand) are checked separately. Deprecated `shift()` has a different −256…256 count and wraps left shifts; do not conflate it with operators. |
| Unary/Boolean | `not` only NameConstant; minus numeric; invert Int; Boolean chains require all Boolean folded children, produce NameConstant | Do not turn Python truthiness into Vyper typing or use an n-ary AST as a binary operator. |
| Comparisons | Numeric ordering; same-literal-kind equality, Hex equality case-insensitive; membership folds against homogeneous literal lists | A folder result is not evidence of a valid original comparison domain. Runtime array/flag membership needs its own typing. |
| Aggregates/subscript | List/Tuple/Dict collect folded elements/values; subscript folder handles homogeneous literal **lists**, with Int index and bounds checks | This is not tuple-index acceptance. Tuple type validator uses `reduced()` and requires a nonnegative literal in bounds. Structured reification and nominal typing are separate obligations. |
| Literals | Int, Bool, Decimal, Str, Bytes/HexBytes, Hex are distinct source kinds | Validate numeric ranges at the actual source/type boundary, decimal precision (10 places), allowed ASCII string characters, hex shape/address typing and byte lengths. Do not erase bytes4 vs Bytes[4]. |

### Builtin folding inventory

`ConstantFolder.visit_Call` resolves a Name through the namespace, requires
`VarInfo`, then calls its type's `_try_fold`. Spelling alone is not identity.
`validate_call_args` and original type checking cannot be bypassed by reifying
a convenient final value.

| Builtin / pinned `functions.py` anchor | Fold/result and required validation | Scope |
|---|---|---|
| `len`, 466–493 | One folded Str/Bytes/HexBytes/Hex gives Int length; original `_inputs` and inferred argument type still matter (not arbitrary fixed bytes just because `_try_fold` can count them) | #543 witnesses |
| `keccak256`, 599–627 | Str encoded bytes, byte literals or Hex → Hex bytes32; original accepted argument types are String/Bytes/bytes32 | #543; use formal Keccak plus proved executable implementation, not compiler hash |
| `method_id`, 719–763 | Constant Str, no spaces, one argument; output_type only bytes4 or Bytes[4], default Bytes[4]; first four Keccak bytes → Hex or Bytes respectively | #543; runtime string rejects, no residual runtime MethodId |
| `min`/`max`, 1943–2011 | Same Int/Decimal node kind with common numeric type → same kind | #543 numeric domain, not arbitrary orderable values |
| `pow_mod256`, 1417–1438 | Two nonnegative Int operands → Int modular power, modulus 2**256; negative operands are unfoldable here, not valid uint256 inputs | #543 witnesses |
| `uint256_addmod`/`uint256_mulmod`, 1377–1414 | Three Int operands; zero modulus errors; unbounded sum/product then modulus → Int; original inputs must be uint256 | Addmod required by witness; shared rule should cover mulmod without introducing a second evaluator |
| `abs`, 1441–1474 | Fold Int → Int; original signed int256 domain and result bounds remain required, including minimum signed value overflow | #543 witness |
| `floor`/`ceil` 138–199; `sha256` 647–668; `as_wei_value` 922–980; deprecated `shift` 1326–1352; `uint2str` 2014–2041; `min_value`/`max_value`/`epsilon` 2462–2514 | Additional actual `_try_fold` rules: integer, hash, scaled integer, shift, string and type-derived numeric results respectively | Inventoried beyond 37 witnesses. No completeness claim from these witnesses. Any rule reached by #543 elaboration needs the same source/domain validation; unsupported must be explicit, never folded-metadata fallback. Broader independent typing remains #135. |
| `empty`, type-folded base classes 111–135 and 2116–2128 | Type-derived constant/modifiability is not synonymous with having a literal folder rule | Aggregate/type-driven elaboration must not be inferred from an Int-only evaluator |
| `abi_encode`/`abi_decode`, 2224–2443 | These are not general literal-folding rules. Literal-required kwargs and output type/size computation occur in builtin typing/codegen | #543 consumes source constant flags/selectors; broader ABI lowering is #551 |

### Concrete boundary observations (fresh pinned Python, not HOL tests)

Additional `compile_code` probes used the same settings as P, with
`enable_decimals=True`. The bodies below were placed in external pure
functions with the indicated types (the bound probe used an external array
parameter). These observations resolve immediate arithmetic/acceptance choices:

| Probe | Observed source outcome |
|---|---|
| `uint256[((1 << 256) >> 255) + 1]` parameter | Compiles; pinned source inspection and the retained strict-frontend fixture identify bound **3**, not wrapped 1. Existing strict HOL path rejects it. |
| `return 1 << 257` / `return 1 << -1` as uint256 | Both `InvalidLiteral: Shift bits must be between 0 and 256` |
| `return False and (1 // 0 == 0)` | `ZeroDivisionException: Division by zero` |
| `return -7 // 3` / `return -7 % 3` as int256 | Compile; serialized folded Int −2 / −1 respectively |
| `return -1.0 / 3.0` as decimal | Compiles; serialized folded Decimal value is **source text** `-1.0 / 3.0`, not a computed decimal token |
| `return x ** -1` / `return x ** y` (both operands runtime) | `InvalidOperation` for negative exponent / both base and exponent unknown |
| `abi_encode(x, method_id=b"abc")` / five-byte selector | `InvalidLiteral` exactly-four-byte requirement / `TypeMismatch` |
| `abi_encode(x, ensure_tuple=1)` | `TypeMismatch`, not truthy True or absent keyword |
| `A = B + 1; B = 2` constant declarations, return A | Compiles; folded return Int 3 |
| `A = B + 1; B = A + 1` constant declarations | Rejects with aggregate `VyperException`; no claim about a stable diagnostic subtype |

## 2. All 37 witness acceptance obligations

Inventory is exactly
[`folded-value-witnesses.txt`](../lowering/defs/bytecode/folded-value-witnesses.txt),
in that order; source files are
[`folded-value-sources/<name>.vy`](../lowering/defs/bytecode/folded-value-sources).
None of the 37 is a decimal witness. Decimal coverage must be added separately.

Notation:

* `u` = uint256, `i` = int256; `L_t(v)` is typed runtime Literal.
  `B_n` = Bytes[n], `b_n` = bytesN. Named constants retain declaration/provenance
  and get consistent source-computed executable initializers, not just body
  substitutions. AST entries are **required targets**, not observed output of
  a new elaborator.
* `Enc(e, ensure, mid)` abbreviates
  `TypeBuiltin B_n (AbiEncode ensure (SOME mid)) (TupleT [type(e)]) [e]`;
  n comes from source/type-validated ABI size bounds. `Dec(d,F)` is
  `TypeBuiltin (TupleT [u;bool]) (AbiDecode F) (TupleT [u;bool]) [d]`.
  In ABI rows, selector is a four-byte sequence, not a numeric endian guess.
* Checker column `+/H+` = required resolved-runtime checker success, and H
  records both deployment modes accepted the old translated AST.
  **Current result remains U for every row**. `—` = no runtime AST on expected
  source rejection, not permission for checker to accept residual MethodId.
* Parity column records **H only**: `=` both byte arrays equal; `≠` mismatch;
  `NONE` HOL compilation failure; `reject` Python rejection. `★` marks one of
  the seven retained parity fixtures. Fresh source-driven parity is U throughout.
* Verdict: **R** = required #543 success/regression; **W-P/M/A** = additionally
  blocks deletion of power / MethodId / ABI whitelist protection (with the
  named owner); **E** = external lowering result reported-only for this task,
  but frontend acceptance and correct elaboration/checking are still required.
  These classifications never authorize rejecting a valid witness.
* Final column specifies a **required behavior test**, not a test run. Only
  the two overflow rows have H execution receipts. Values in this table can
  supply test oracles, but are not HOL theorems.

Selector abbreviations: `D=deadbeef`, `Fsel=b3de648b` (f(uint256)),
`Esel=002ff067` (E(uint256)), `Foo=c2985578` (foo()),
`Transfer=a9059cbb`. `Khello` and `Kx` below denote Keccak of literal bytes.
These selectors/hashes were also computed via the pinned Python utility;
future HOL expectations must be obtained independently.

| # | Witness | Source expected / P | Required elaborated runtime subtree or declaration | Checker | Parity H | Verdict | Required behavior test (current U) |
|---|---|---|---|---|---|---|---|
| 1 | pow_folded_exp | accept / accept | `Exp(x,L_u(3))` | +/H+ | = ★ | R, W-P #572 | f(2)=8; f(2**90) reverts on both outputs (H: two receipts) |
| 2 | pow_negfold_base | accept / accept | `Exp(L_i(-2),y)` | +/H+ | = | R, W-P #572 | f(3)=−8; f(256) reverts on both outputs (H: two receipts); negative y check |
| 3 | fold_add | accept / accept | `Add(x,L_u(3))` | +/H+ | = ★ | R | f(4)=7; checked overflow at max uint256 |
| 4 | fold_pow_lit | accept / accept | `Mul(x,L_u(256))` | +/H+ | = | R | f(2)=512; overflow boundary |
| 5 | fold_cmp | accept / accept | `L_bool(T)` | +/H+ | = ★ | R | f()=True |
| 6 | fold_not | accept / accept | `x and L_bool(F)` with normal short-circuit AST | +/H+ | = | R | f(False)=False; f(True)=False |
| 7 | fold_shift | accept / accept | `And(x,L_u(16))` (bitwise) | +/H+ | = | R | f(31)=16; f(8)=0 |
| 8 | fold_minmax | accept / accept | `Add(x,L_u(3))` | +/H+ | = | R | f(4)=7 |
| 9 | fold_powmod | accept / accept | `L_u(1024)` | +/H+ | = ★ | R | f()=1024 |
| 10 | fold_addmod | accept / accept | `L_u(4)` | +/H+ | = ★ | R | f()=4 |
| 11 | fold_abs | accept / accept | `L_i(5)` | +/H+ | = ★ | R | f()=5 |
| 12 | keccak_literal | accept / accept | `L_b32(Khello)` | +/H+ | = | R | return `1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8` |
| 13 | len_string_lit | accept / accept | `L_u(4)` | +/H+ | = | R | f()=4, literal length not declaration capacity |
| 14 | method_id_b4 | accept / accept | `L_b4(Transfer)` | +/H+ | = | R, W-M | fixed bytes4 ABI return, correct prefix order |
| 15 | method_id_bytes | accept / accept | `L_B4(Transfer)` | +/H+ | = | R, W-M | dynamic Bytes[4] return length=4, correct bytes |
| 16 | method_id_const | accept / accept | SIG source string `"foo()"`; `L_b4(Foo)` return | +/H+ | = | R, W-M | return c2985578, not hash of constant name |
| 17 | method_id_storage | accept / accept | assignment `self.m := L_b4(Foo)` | +/H+ | = | R, W-M | call f(); inspect m storage = selector in bytes4 representation |
| 18 | method_id_var | **reject** / reject | explicit nonconstant-required-argument error, no runtime MethodId fallback | — | reject | R, W-M negative | reject runtime String[30]; hand-built residual MethodId fails checker |
| 19 | enc_mid_const | accept / accept | M=`L_b4(D)`; `Enc(a,F,D)` → B36 | +/H+ | = ★ | R, W-A #551 | f(7) returns D followed by 32-byte word 7 |
| 20 | enc_mid_methodid_call | accept / accept | `Enc(a,F,Foo)` → B36 (method_id default dynamic output converted to prefix bytes) | +/H+ | = | R, W-M/A #551 | prefix Foo, then word a |
| 21 | enc_mid_bytes4lit | accept / accept | v=(int128,bool); `Enc(v,F,D)` → B68; source selector is **bytes literal**, despite fixture name | +/H+ | = | R, W-A #551 | f(−1,True): D + signed word −1 + Boolean word 1 |
| 22 | enc_ensF_string_mid | accept / accept | `Enc(a,F,D)` → B132, String[40] | +/H+ | = | R, W-A #551 | encode "abc": no outer one-tuple offset; D + length/data; check actual vs max length |
| 23 | enc_ensF_uint_mid | accept / accept | `Enc(a,F,D)` → B36 | +/H+ | = | R, W-A #551 | prefix D + word a |
| 24 | enc_ensure_const | accept / accept | E=`L_bool(F)`; `Enc(a,F,D)` → B36 | +/H+ | = | R, W-A #551 | identical payload to row 23, no default-True substitution |
| 25 | dec_unwrap_const | accept / accept | U=`L_bool(F)`; `Dec(d,F)` | +/H+ | = | R, W-A #551 | decode canonical (7,True); malformed Boolean/length rejection |
| 26 | ctl03_abi_method_id | accept / accept | `Enc(x,T,Fsel)` → B36 (ensure absent defaults True) | +/H+ | **≠** | R frontend; E/W-A #551 | correct f selector and word x; require parity repair, not source rejection |
| 27 | enc_ensT_uint_mid | accept / accept | `Enc(a,T,D)` → B36, **address** operand despite fixture name | +/H+ | **≠** | R frontend; E/W-A #551 | address ABI word and D prefix |
| 28 | neg_lit | accept / accept | `Add(x,L_i(-5))` | +/H+ | = | R | f(10)=5; signed underflow boundary |
| 29 | pow_neglit_base | accept / accept | `Exp(L_i(-2),y)` (source already literal-negative form) | +/H+ | = | R, W-P #572 | f(3)=−8; compare row 2; negative exponent/overflow cases |
| 30 | lt_mixed_lit | accept / accept | runtime `Lt(a,L_u(5))` → bool | +/H+ | = | R | f(4)=True; f(5)=False; do not fold dynamic a |
| 31 | boolop_and3 | accept / accept | short-circuit `(a and b) or c` as nested IfExp | +/H+ | = | R | all eight Boolean combinations, preserve association/order |
| 32 | i12_immut_with_storage | accept / accept | N=`L_u(10)`; constructor X initializer `L_u(20)`; runtime X/storage reads retained | +/H+ | **NONE** | R frontend; E #563 | deploy X=20,s=1; f()=31; must not substitute immutable as source constant |
| 33 | p29_imm_multi | accept / accept | constructor C=`L_b32(Kx)`; A=a and B=msg.sender remain dynamic | +/H+ | **NONE** | R frontend; E #563 | deploy(a,sender); get=a, who=sender, h=`7521d1cadbcfa91eec65aa16715b94ffc1c9654ba57ea2ef1a2127bca1127a83` |
| 34 | c16_const_string_in_expr | accept / accept | S source String[5]="abc"; return `L_u(3)` | +/H+ | = | R | f()=3, not capacity 5 |
| 35 | c27_const_binop_fold | accept / accept | A=`L_u(3)`; return `L_u(21)` | +/H+ | = | R | f()=21 |
| 36 | rc09_abi_encode_data | accept / accept | raw_call(t,`Enc(x,T,Fsel)`), encode → B36 | +/H+ | **≠** | R frontend; E/W-A #554/#551 | observing callee receives f selector and x, effects/call failure policy |
| 37 | rr03_abi | accept / accept | conditional raw_revert(`Enc(x,T,Esel)`) → B36 | +/H+ | **≠** | R frontend; E/W-A #567/#551 | x=3 no revert; x=4 revert data Esel + word 4 |

All 36 valid witnesses must elaborate and remain checker-accepted even when an
external bytecode obligation is unresolved. The four mismatches and two NONEs
are not passing parity. Byte equality does not establish `supported_program`
or prove behavior; H's four execution receipts cover only the two named
power-overflow calls. No behavior result for other rows is asserted here.

## 3. Frontend source-sensitive consumer inventory

File abbreviations below: **D**=`frontend/jsonASTLib.sml`,
**E**=`frontend/jsonToVyperExprScript.sml`,
**T**=`frontend/jsonToVyperTypeScript.sml`,
**L**=`frontend/jsonToVyperTopLevelScript.sml`,
**M**=`frontend/jsonToVyperScript.sml`.

Scope: **543** = migrate in #543; **I** = integration prerequisite, even without
a dedicated witness; **D135** = broader independent frontend typing/import/layout
work may remain deferred, only behind an explicit no-fallback boundary.
“Retained” means in decoded `jsonAST`, not merely recoverable by rereading JSON.
Each boundary regression below is a required design/test obligation unless an
existing test is specifically named; **none of the proposed regressions was
implemented/run in this documentation-only task**.

| Consumer and exact entry point | Present data flow / original syntax status | Scope and required migration / boundary regression |
|---|---|---|
| Ordinary constant subexpressions: D `d_json_expr`, `with_folded` (670–889); E `translate_expr` (909–1075) | BinOp/Compare/BoolOp/UnaryOp/Call and Int/Bool-folded Names wrap `JE_Folded original folded`; E line 936 unconditionally selects folded branch. Original survives decoding but not runtime translation. Attributes do not have the same generic wrapper. | **543**: extract candidates from originals recursively in bodies, statements, initializers/defaults; validate builtin identity and source typing. Delete and replace folding with a *different well-formed literal*; compare source terms, elaboration, checking and bytes. Bad original + good metadata must not succeed. |
| Strings/bytes/static-array/dynamic-array annotation bounds: D `annotation_bound`, `d_ast_type` (484–566); T `elaborate_annotation`, `canonical_decl_type` | `JTA_String/Bytes/StaticArray/DynArray` contain **num**, not expressions. `annotation_bound` accepts literal Int or `folded_value.Int`; **bound original is discarded**. Nested arrays/tuples recurse through same decoder. | **I/543** for source bounds touched by integration: preserve expression-bearing source annotation; common evaluator, positive lengths and consumer limits. Test nested combinations and unbounded-intermediate bound 3. Do not add a separate bound evaluator. |
| Local/for annotations, parameters, returns, ordinary variables: D `d_json_stmt` (1150–1186), `json_arg` (1207–1220), `json_toplevel` (1361–1421); M `*_decl_types_valid` (552–645); L `translate_arg`, `translate_toplevel` | Source annotation skeleton sometimes retained; `orElse(field ... ast_type, JTA_None)` collapses **decode failure and absence**. `constant`, `immutable`, `public`, etc. annotation Calls are not recognized by `d_ast_type` (only indexed is unwrapped), so qualifiers/source types can be lost. T `canonical_decl_type` falls back to inferred `JT_*` for JTA_None. Validation compares against a bound already imported as num. | **I** fix failed-vs-missing decode and preserve qualifiers/bounds before trusting consistency. **D135** full expression type inference remains separate. Guard: malformed present bound + plausible inferred type/folded literal must error, not become JTA_None. |
| Struct fields, event fields (including indexed), interface argument/return annotations: D `json_event_arg`, StructDef/InterfaceDef decoders (1424 onward); L `translate_interface_func`, Event/Struct/Interface branches | Struct/interface args use `json_arg`; event fields explicitly unwrap indexed and preserve annotation; all use `d_ast_type` numeric bounds. L uses canonical declaration types or elaborated interface return annotations. **Original bound already lost**, even when inferred consistency succeeds. | **I** migrate nested source bounds everywhere, not just function args. **D135** wider nominal/interface inference. Guards: metadata poison nested field bounds; distinguish indexed qualifier from its bound syntax. |
| HashMap keys/values including nested HashMaps and arrays/strings/bytes: D `d_json_value_type` (1193–1204), HashMap VariableDecl (1388–1404); L `translate_value_type`, HashMap branch | Decoder reads **only target.type** key/value metadata into `JVT_Type/JVT_HashMap`; no source HashMap annotation in `JTL_HashMapDecl`. **Entire annotation is discarded**. L recursively `translate_type`s inferred values; M declaration validation catch-all does not reconstruct those annotations. | **I** retain HashMap source annotation and nested bound syntax for migrated elaboration. **D135** legacy full HashMap typing may remain, not as fallback after source failure. Guard: HashMap[address,DynArray[Bytes[N+1],M]] with deleted/poisoned bound/type metadata. |
| Explicit range `bound=`: D `json_iter_internal` (1045–1057); E `get_iter_bound`, `translate_iter`, `translate_stmt` | D turns keyword into num (prefers folded.value); **bound expression and keyword structure discarded**. E consumes num as iteration limit while runtime range args are separate. | **543** source compute positive bound; validate arity/keyword and pinned prohibition on explicit bound when both endpoints constant. Guard: invalid bound + valid folded 4 must reject; dynamic endpoint expressions/effects unchanged. |
| Inferred range limit: D range variant (1058–1065); E `json_expr_int_opt`, `range_bound_of_args`, `folded_bound_of_args`, `get_iter_bound` (1114–1169) | Endpoint originals retained as expressions (possibly JE_Folded), plus detached folded Int options. E tries a small integer syntax interpreter that itself selects folded values, then detached metadata fallback, then **0**. | **543** compute from original endpoints with common source evaluator, validate end>start; retain runtime operands. Guard: poison detached metadata while keeping endpoints, compare limit and runtime range. No zero-as-error convention. |
| Array iteration limit: D array iterator (1069–1070); E `get_iter_bound` | Original array expression retained, loop bound from inferred JT_StaticArray/JT_DynArray length; otherwise 0. | **I** use resolved source-derived declaration/expression type for migrated arrays. **D135** general expression-bound inference remains explicit legacy trust. Guard: nested bound change cannot be hidden by inferred iteration type. |
| Tuple subscript vs array/HashMap subscript: D subscript (771–792); E `translate_expr` Subscript, target subscripts | Tuple test relies on inferred base typeclass; D adds folded Int for tuple slice with fallback to slice type. Original index retained. Other indices are not specially literalized, though general subexpression folding still applies. E translates both index and base. | **543**, coordinated **#571**: source constant tuple indices → typed literals with bounds; dynamic array/map indices stay runtime expressions with effects. Guard poison tuple folded index; reject dynamic/out-of-range tuple; accept dynamic array/map. Do not ban all nonliteral source indices. |
| ABI `ensure_tuple`, `unwrap_tuple`, `method_id`: D `d_json_keyword` (948–958); E `kwarg_bool_opt`, `kwarg_method_id`, `make_builtin_call` | Method_id keyword explicitly wraps original and folded metadata; other flags pass through normal expr decoding. After translation, Boolean helpers distinguish absent/invalid; invalid ABI forms are encoded as malformed ASTs (`[]` args); invalid selector becomes `SOME []`. Validity currently still depends on trusted folded branch. | **543** evaluate original kwargs, validate Boolean or exactly four bytes, explicit errors (not malformed-AST sentinels); preserve default True vs invalid present. Selector order and bytes4/Bytes[4] tests. ABI multiargument effects/wrapping are **#551**, not fixed by constant flags. |
| Standalone `method_id`, including const strings/storage assignment | D generic Call folding; E `make_builtin_call` without fold emits Builtin MethodId, ignores output_type in that branch; runtime checker rejects all MethodId apps | **543** source-only call elaboration, source output_type retained/validated before erasure. Test runtime string, spaces, bad output_type, fixed/dynamic output, hash prefix order. Never weaken checker to accept unresolved MethodId. |
| Calldata `slice(msg.data,start,len)`: D special Call arguments (850–869); E `calldata_slice_length`/`calldata_slice_bound`/`translate_expr` | Original len wrapped, but E explicitly selects folded branch; fixed n becomes CalldataSlice n with only start as runtime operand. Invalid length maps to rejecting CalldataSlice 0 marker. `len(msg.data)` recognized syntactically, not ordinary bounded bytes. | **543/I** source-compute required positive length (<2**256), retain runtime start exactly once; explicit source errors. Guard: good folded len must not rescue dynamic/invalid original; poisoned folded len cannot change n. |
| Calldata raw_call flags/size: D `d_calldata_raw_call_keyword` (960–980); E `raw_call_flags_of_kwargs`, RawCallCalldata branch | Dedicated decoder adds folded max_outsize and flags; target/value remain runtime operands. Flags become record fields. Missing/invalid/nonliteral Boolean uses default; numeric negative/invalid uses default 0. | **I** migrate source required constants with no trusted-fold fallback. Guard well-formed poisoned Bool/Int, conflicting delegate/static flags, invalid max_outsize; compare target/value effects and defaults. Broader call lowering remains external. |
| Ordinary raw_call flags/size: E `make_builtin_call`, `kwarg_bool`/`kwarg_num` (207–233, 316–324) | Same flags helper, but no dedicated calldata keyword decoder. General wrappers may provide folds; flags/size erased into record, invalid values silently default. Runtime data,target,value retained; gas is not staged by this helper. | **D135** full call keyword/evaluation support; **I** no fallback when traversed by #543. Guard same as calldata plus a dynamic gas/effect-order test; do not claim gas support from constant folding. |
| Create flags: E `make_builtin_call` create_minimal_proxy_to/forwarder/copy/blueprint/raw_create (327–356) | `revert_on_failure` and blueprint `raw_args` via defaulting kwarg_bool. `value`, optional salt, blueprint code_offset remain expressions (code_offset default 3), not required source constants. Arg lists are reconstructed. | **D135** full create semantics/keyword sequencing; **I** migrated constant operands cannot call legacy defaulting on error. Guards invalid Bool + forged folded Bool, absent defaults, dynamic value/salt/code_offset evaluated once. Do not incorrectly require constant code_offset. |
| External/static call `skip_contract_check`: D ExtCall/StaticCall; E `json_keyword_bool` (827–832), ExtCall/StaticCall (1021–1059), `ext_call_kwargs` | Original kwargs retained, but skip check reads **raw JE_Bool only**, not JE_Folded; otherwise False. value/gas/default_return_value translated separately and preserved in source order; skip flag erased into ExtCall. | **D135** general calls, **I** source literal-required flag before erasure. Guard constant-True alias and forged folded opposite; invalid present must not become False; retain runtime keyword order/effects. |
| Denomination string: E `denomination_of_string`/`denomination_of_expr`, `make_builtin_call` as_wei_value (173–200, 358–365) | After translating expression, accepts StringL recognized denomination; unknown/nonliteral/missing silently becomes Wei. Original denomination expression is dropped from builtin args. | **D135** general as_wei_value source typing; **I** source-derived constants and explicit invalid denomination errors if reached by new path. Guard unknown literal/dynamic denomination + valid folded string cannot choose Wei; test aliases and source errors. |
| Result-type-derived builtin bounds and type parameters: E `make_builtin_call` concat/slice/uint2str, convert/empty/min_value/max_value/epsilon/extract32, ABI decode | Concat/Slice/Uint2Str n come from inferred return JT_String/JT_Bytes (else 0). Other type builtins use translated result ty, often drop type-expression arguments. JSON literal string/bytes lengths also come from inferred fields (D 695–718). Original call args retained until translation, but type-dependent meaning may already be numeric metadata. | **D135** independent general builtin typing; **I** derive/check sizes and output_type from source for migrated rules (especially method_id/ABI/bounds); reject inconsistent claims, never recompute meaning from forged return type. Guard concat/slice/uint2str return length poison, extract32/convert target poison, missing-vs-malformed type syntax. |
| Defaults (executable): D FunctionDef defaults (1368–1374); L `translate_toplevel` defaults | Original expressions retained, then translated through legacy folding; not restricted to a top-level Int literal. | **543** recursively elaborate constant subtrees; initializer/default evaluation must agree with rewritten modules. Guard default constant builtin/arithmetic with well-formed poison; preserve dynamic/default-call domain rather than assume all defaults constant. |
| Default override comparison: M `default_override_ok`, `canonical_default_aux` (762–862) | Structural equality after canonicalization. Explicitly strips JE_Folded using **original**; resolves module/constant identities and erases selected type metadata. | **I** finish structural comparison before rewriting, or retain separate provenance. `1+2` and `3` must not become interchangeable by fiat. Existing `vyperCheckContractFrontendLibTestScript.sml` 262–275 tests original-vs-folded defaults; not a new-path isolation regression. |
| Constants/declaration qualifiers: D non-HashMap VariableDecl; L `translate_var_mutability`, M `collect_consts_and_immutables` | `is_constant` controls initializer presence; immutable/transient/public flags trusted; source qualifiers may be lost as above. Constants and immutables both collected for top-level name lookup (not proof either is a source constant). L wraps translated initializer in Constant, variable initializer slot is NONE. | **543/I** preserve original initializer and qualifier syntax, distinguish constants from immutables; same reified value for references and deployment. Tests shadowing, immutables, declaration flag poison, duplicates, forward/imported names, aliases and cycles. |
| Exports/initializes/uses/dependency discovery: D declaration annotations as json_expr (1528–1538); M `resolve_module_expr`, export expansion, `initialized_alias`, `get_module_deps`, canonical identities; L drops declarations | Source expression shape retained until module translation. Dependency ordering currently based on import infos, not a general source-constant dependency graph. Rewriting to literals too early can break module paths/NamedExpr matching. | **I** run structural consumers against preserved originals/canonical declaration identities. **D135** full import/type/layout trust removal. Guard alias collision/imported constants and initializes named binding survive expression elaboration; do not identify source modules by unvalidated raw source_id alone. |

### Deferred legacy entry-point boundary (not implemented by this document)

The ordinary public path today is
`vyperCheckContractFrontendLib.check_contract_file` →
`jsonASTLib.annotated_ast` → `prepare_check_input` →
`translate_annotated_ast` → legacy E/L/M translation. That path **does reach**
the trusted folding and defaulting consumers above. Renaming it “source” would
not create independence.

The distinct existing opt-in path is
`check_constant_contract_file` → `jsonConstASTLib.annotated_ast` →
`translate_constant_module` → `vyperCheckContractLib.check_contract`.
Inspection of `frontend/vyperCheckContractFrontendLib.sml:170–185` shows explicit
failure on NONE and no retry of the ordinary translator. Its decoder accepts
only integer literals/names/binops, integer/static-array annotations,
non-public constants and external pure single-return functions. It rejects
imports, other statements/calls/unary/defaults. It processes constants in order
and rejects unbounded source intermediates. It cannot replace the ordinary path
for the 37 witnesses; see [constant-evaluation.md](../frontend/constant-evaluation.md).

For **each D135 row**, the future new ordinary elaboration API must have a
regression at that row's entry point:

1. Construct a valid original requiring that consumer; run with no fold and
   with two *different well-formed* folded literals. Require identical source
   syntax, elaboration, checker result and compiled bytes on supported rules.
2. Construct an unsupported/invalid original plus usable folded/type metadata.
   Require its explicit Unsupported/Invalid result, and show the wrapper does
   not retry `translate_annotated_ast`, `translate_expr` or another legacy
   helper. Any opt-in legacy API remains distinct and labelled.
3. For inferred type/bound consumers, delete/poison those claims too: derive
   the same meaning or reject inconsistency, never accept a different meaning.
   Preserve unchanged runtime operands and keyword order; compare source and
   resolved modules/artifacts actually checked and compiled.

Existing `frontend/jsonConstEvalWitnessScript.sml:18–34,98–103,141–149` compares
strict decoding with removed and **malformed string** metadata. It is useful
partial evidence, not the required well-formed poison and ordinary-path
isolation coverage. Existing folded tests in
`vyperCheckContractFrontendLibTestScript.sml:477–594` intentionally assert
legacy **consumption** (`folded_translation_boundary`, literal kinds and range
bounds), so must not be cited as independence tests. New boundary regressions
for all deferred rows remain **MISSING**. Documentation alone does not satisfy
the plan's requirement to add them.

## 4. Genuine source rejection vs masking lowering defects

| Boundary | Evidence and ownership | Condition before whitelist deletion |
|---|---|---|
| Power (#572) | Pinned `NumericT.validate_numeric_op` (`primitives.py:172–224`) checks reduced operands, including AugAssign: two dynamic operands reject; literal negative exponent rejects. HOL `well_typed_binop Exp` currently checks only integer type equality (`vyperTypeSystemScript.sml:104`); `compile_safe_pow` has a nonliteral/nonliteral fallback. | Frontend folds both exponent and base subtrees; checking/lowering for **raw runtime ASTs** establishes safe domain without assuming JSON normalization. Cover negative exponent, AugAssign and deployment, not only ordinary return expressions. Retain `supported_binop Exp` literal-base/nonnegative-literal-exponent premise until replaced by a named proved fact or correct general implementation. |
| Tuple index (#571) | Pinned TupleT validator accepts source-reduced literal index in range (`subscriptable.py:443–455`). Decoder's tuple-specific fold does not prove checker-admitted raw ASTs satisfy lowering's index shape. | Accept source-foldable indices; prove raw checker/lowering index contract. A blanket rejection of nonliteral original source masks missing elaboration. |
| MethodId | HOL runtime checker rejects MethodId (`vyperTypeSystemScript.sml:224`). Valid source standalone calls must disappear before checking; method_id_var remains a source rejection. | Prove source call acceptance/reification, and maintain residual runtime rejection. No reliance on compiler replacement Hex/Bytes value. |
| ABI (#551; callers #554/#567) | E carries flags/prefix/arg types; `exprLoweringScript.sml:2975–3004` lowers **HD args only** for AbiEncode and matches AbiDecode `_` (ignores unwrap). `supported_type_builtin_form` only admits a narrow tuple/prefix fragment (`supportedExprFormsScript.sml:133–147`). H has four actual mismatches. | Source keyword validation is necessary, not sufficient. Repair/prove all checker-admitted ABI argument staging, effects, tuple wrapping/unwrap and prefix behavior before removing restrictions. Add multiargument effect tests, not just single-argument fixtures. |
| Immutables (#563) | Valid P programs; H checker accepts but compile returns NONE for rows 32–33. | Keep frontend constants in constructor bodies correct; report lowering failure separately. No rejection or claiming byte parity as a workaround. |
| Raw compiler/proof composition | `compile_vyper` receives runtime toplevels directly, does not run JSON elaboration/checking. Existing constant lemmas concern bounded runtime evaluation and actual module-code/immutable environments. | Elaborate, check, interpret and compile the **same** resolved modules with translation/checker/compile equations. Rewriting source changes module code; discharge transport hypotheses. This document removes no supported_program premise or admission. |

Unrelated arithmetic, storage, calls, memory, deployment, dispatch/name uniqueness
and complete #135 typing/import/layout obligations remain outside #543. Existing
three top-level lowering admissions in the validation report are not certified
away by this matrix or by historical fixture parity.

## 5. Decisions to carry into implementation; remaining freeze blockers

**Settled design constraints from the audit:** retain originals until the last
structural/source-sensitive consumer; use one source-constant syntax/evaluator
for bodies, defaults, bounds and keywords; source integer arithmetic is not
bounded runtime arithmetic; eager compile-time child visitation; original
builtin signature/domain/type validation before erasure; exact fixed/dynamic
byte kinds and explicit missing/invalid/unsupported/nonconstant outcomes;
required constants accept only Computed. Invalid constant arithmetic must not
become runtime arithmetic or trigger metadata fallback. Annotation datatypes
currently precede json_expr: use an independent source-constant datatype rather
than introduce a circular dependency. Preserve provenance separately from the
initializer actually executed at deployment.

**Do not freeze theorems claiming coverage beyond the evidence above.** Remaining
work/questions, with the required resolution evidence:

* The strict evaluator's bounded-intermediate rejection is not the general
  source semantics. Specify precisely which original intermediates are
  validated (vs final requested type), including zero/negative bounds and
  huge powers. The bound-3 probe forbids blanket runtime wrapping or blanket
  early overflow rejection. Probe more cases at pinned typing/codegen, not
  just `_try_fold` outputs; no host floats in HOL arithmetic.
* Formalize scaled decimal per-operation truncation, precision and signed
  division/remainder from the pinned rules above, with executable examples near
  minimum precision and overflow. The 37 witnesses supply **no decimal acceptance coverage**; a
  folded Decimal containing source text must never be parsed as its computed
  value. Preserve original decimal tokens.
* Complete acceptance tests for additional builtin rules and negative original
  operand domains that can yield an innocuous final constant (e.g. hash input
  type, abs minimum signed value, modular arithmetic uint operands). Decide
  aggregate reification scope explicitly; List/Tuple/Dict folding alone does
  not justify nominal struct/interface constants or sparse-array lengths.
* Resolve imported/forward constant dependency behavior, canonical module and
  declaration identities, alias collisions, shadowing, cycles and duplicates.
  Local forward reference acceptance is established by P; full imported and
  aggregate cases remain **UNKNOWN**, not proven by folder retry termination.
* Add the per-consumer no-fallback regressions in §3 before claiming any D135
  legacy consumer safely deferred from the new ordinary path. No such new
  path or regressions have been supplied here.
* Re-run all 37 through source elaboration/checking and record actual resolved
  AST equations; then regenerate the seven oracle fixtures independently at
  exact pinned settings and re-run current parity, corpus, both-output power
  executions and theorem/tag audit. H source drift prevents reusing its
  receipts as the final acceptance run. Report owner-specific failures as
  failures/unknowns, not passes.

Historical stage-1 conclusion: until those obligations had current evidence,
the evaluation/proof readiness and #543 whitelist-deletion gates were
**UNKNOWN / NOT DISCHARGED**. For the current, narrower discharged gates,
implemented ordinary bridge and retained backend boundaries, use the scoped
ledger above.
