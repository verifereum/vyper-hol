# Source annotation resolution

This layer resolves retained source annotations for source elaboration and
ordinary normalization, independently of compiler-computed bounds. See [sourceSyntax.md](sourceSyntax.md),
[sourceResolve.md](sourceResolve.md) and
[constant-evaluation.md](constant-evaluation.md) for syntax, identity and trust
boundaries.

## API and inputs

* `sourceTypeDefs`: resolved identities, errors and required-constant bounds.
* `sourceTypeResolve`: `source_type_resolve tenv names constants annotation`
  consumes `source_const_annotation`, returning
  `ST_Ok (SourceTypeResolution vtype qualifiers bounds)` or an explicit error.
* `sourceTypeProps`: runtime wellformedness and bound-value provenance.
* `sourceTypeProvenance`: recorded bounds are exactly all original annotation
  bounds, in structural left-to-right/postorder, not replacements.
* `sourceTypeFrontendLib.resolve`: kernel-certified equation, wellformedness,
  bound-value and original-bound theorems. `check_claim` additionally checks an
  inferred `value_type` for equality; it cannot choose the resolution.

`tenv` is the independently elaborated nominal environment; `names` maps resolved
paths to `source_type_identity`; `constants` is the common `source_const_eval`
environment (e.g. successful `source_const_resolve` output). There is no
spelling-based primitive fallback. Aliases may share identities; shadowed names
need not. Integer identities carry source width/signedness, fixed-byte identities
the source byte width.

Dedicated annotation tags for `String`, `Bytes`, `DynArray`, `HashMap` and
qualifiers do not establish builtin identity: the canonical path must resolve to
the matching `STI_Constructor`. A `Bytes` spelling bound to `STI_Bool` rejects.
The common syntax cannot represent aliases of parameterized builtin
constructors; resolution does not invent missing identity information.

Frontend callers supply original annotations and independently resolved
environments. The library computes HOL terms using proved rules, never source
arithmetic in ML, and fails closed on errors/nonclosed/noncomputable inputs. It
does not decode JSON or reify syntax.

## Validation and errors

Integer widths are multiples of eight in `[8,256]`; fixed bytes are `[1,32]`.
Original bounds use common `source_const_eval`. Only `SC_Value (SCV_Int i)` with
`0 < i < 2^256` is accepted; naturals are constructed afterward, never by unsigned
wrapping. Booleans/scaled decimals are not integer bounds.

| Common outcome | Annotation error |
|---|---|
| `SC_NotConstant` | `STE_RequiredConstant` |
| `SC_Invalid e` | `STE_ConstantInvalid e` |
| `SC_Unsupported u` | `STE_ConstantUnsupported u` |
| noninteger `SC_Value` | `STE_IntegerBound` |
| nonpositive/too-large integer | `STE_BoundRange` |

Constructed types also pass `well_formed_vtype`, including aggregate slot-size
overflow and nominal declaration validity. HashMaps retain `HashMapT key value`,
separate from ordinary `Type ty`, and may nest as values; they never become
`NoneT`. Keys satisfy `hashmap_key_type`. Arrays/tuples require ordinary runtime
element types and reject nested qualifiers. Empty tuples, duplicate qualifiers
and mutually exclusive constant/immutable/transient qualifiers reject. Root
qualifiers remain explicit. Resolution reports the first failing structural
child; each constant expression retains the common eager error algebra.

## Theorem and trust boundary

`source_type_resolve_well_formed` establishes output `value_type` wellformedness;
`source_type_resolve_runtime_well_formed` specializes it to ordinary `Type ty`.
`source_type_resolve_bound_provenance` gives exact common evaluation and a
positive source-range-checked natural for every bound.
`source_type_resolve_original_bounds` excludes omitted, inserted or substituted
bound expressions. `source_type_claim_is_only_a_check` characterizes inferred
claim success as independent resolution success plus equality.

These are not whole-program acceptance, import provenance, nominal cycle
checking, qualifier **placement** checking (e.g. indexed only on event fields),
storage-layout correctness or compiler equivalence. These obligations remain
with callers. Environments must not be copied from unchecked inferred metadata.

## Reproduction

```sh
holbuild build sourceTypeTestTheory sourceTypeProvenanceTheory \
  sourceTypeFrontendLibTestTheory
```

Tests exercise primitives/source widths, arithmetic/name bounds, nested arrays
and HashMaps, tuples/qualifiers, distinct common outcomes, slot overflow,
no wrapping, constructor shadowing and inferred-claim rejection. Frontend
certificates are saved as HOL theorems in `sourceTypeFrontendLibTest`.
