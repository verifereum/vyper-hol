# C1.7.1: local-memory RHS representation qualification

## Scope and result

This is a checked interface report for C1.7, **not** a proof of
`bodyFullAssign.body_assign_local_memory_full` or of its execution suffix.
No exported helper, semantic definition, frozen header, shared root, or foreign
supplier was changed. The temporary local-only probe theory was removed after
checking; the statements and tactics below record its relevant results.

The frozen representation alternatives suffice for nonempty classification,
post-type normalization, and lowered-buffer destination capacity. Existing
`memoryLocalRhsProps` exports already give successful-read typing, runtime
footprint, and empty-default facts. None of these facts asserts full static
source-region ownership or source/destination disjointness.

## Checked implications of the frozen assumptions

The following four local probes built successfully in
`bodyFullAssignRepresentationProbeTheory`, with ancestors
`memoryLocalRhsProps loweringPosts vyperTypeSystem vyperAST finite_map
exprSimHypsDefs valueTypingMemoryProps` and library `monadsyntax`.
These are report snippets, not additional proposed exported interfaces.

### Nonempty classification

```sml
Theorem nonempty_classification[local]:
  !cenv e ty.
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    expr_type e = ty \/ is_bytestring_type ty
Proof
  metis_tac[]
QED
```

The second representation alternative is essential: when the lowered type is
the destination but differs from the annotation, it identifies bytestrings.
This is not an assertion that lowered and annotation types always coincide.

### Physical post type

```sml
Theorem post_type_normalization[local]:
  !cenv e.
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    post_value_type cenv e = expr_type e
Proof
  metis_tac[post_value_type_lowered, post_value_type_bytestring]
QED
```

Existing signatures in `loweringPostsScript.sml`:

- `post_value_type_lowered`:
  `!cenv e. lowered_value_type cenv e = expr_type e ==>
  post_value_type cenv e = expr_type e`.
- `post_value_type_bytestring`:
  `!cenv e. is_bytestring_type (expr_type e) ==>
  post_value_type cenv e = expr_type e`.

`post_value_type_def` uses the lowered type for non-word, non-bytestring
internal calls, and otherwise uses the annotation. The checked normalization
therefore does not equate the annotation with `lowered_value_type` in the
bytestring alternative. In particular it is not permission to rewrite the
second slot of a physical `vv_store_bound` contract.

### Assignment typing

```sml
Theorem assignment_typing[local]:
  !env ret_ty id e env' ty.
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    FLOOKUP env.var_types id = SOME ty ==>
    well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty
Proof
  rpt strip_tac >>
  gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
  rename1 `FLOOKUP env.var_assignable id = SOME asg` >> Cases_on `asg` >> gvs[]
QED
```

### Lowered buffer versus destination capacity

```sml
Theorem nonempty_destination_sizes[local]:
  !cenv e env ty tenv.
    well_typed_expr env e /\ type_widens_to tenv (expr_type e) ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ty
Proof
  metis_tac[nonempty_classification, memory_rhs_destination_bound]
QED
```

The exact existing `memory_rhs_destination_bound` antecedent is
`well_typed_expr env e /\ type_widens_to tenv (expr_type e) ty /\
(expr_type e = ty \/ is_bytestring_type ty) /\
0 < type_memory_bytes cenv ty`, together with the frozen second representation
disjunction. Its conclusion is exactly the last probe's size conjunction.
A kernel-checked goal search also matched that existing theorem directly.

## Successful forced-RHS read: existing interface

`memoryLocalRhsProps.memory_rhs_read_destination_footprint` already proves the
following goal as stated (kernel-checked `MATCH_ACCEPT_TAC`):

```sml
!cenv cx env e es tops ty tyv v es1.
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  type_widens_to env.type_defs (expr_type e) ty /\
  (expr_type e = ty \/ is_bytestring_type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tyv /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
  value_has_type tyv v /\
  val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
```

Thus, on **this same successful run**, runtime footprint is bounded by lowered
buffer capacity, which the nonempty size result bounds by destination capacity.
There is no separate choice of source or execution endpoint in this reasoning.
The full root must still derive `expr_body_pre`, supported-program/compiler
metadata, and destination type evaluation from its own invariants.

Other existing interfaces explain the division of responsibilities:

- `memory_rhs_read_destination_typed`: `expr_body_pre` plus
  `type_widens_to env.type_defs (expr_type e) ty` and that successful forced read
  imply `value_runtime_typed env ty v`.
- `memory_rhs_read_lowered_typed`: `expr_body_pre`, `supported_expr tops e`,
  return-type metadata, supported-program/module-code facts, and that same read
  imply `value_runtime_typed env (lowered_value_type cenv e) v`.
- `memory_rhs_runtime_layout`: `expr_sim_inv cenv cx env es /\
  value_runtime_typed env ty v ==> ?tv.
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes cenv ty = type_memory_size tv`.
- `memory_rhs_read_local_type`: `expr_body_pre`,
  `FLOOKUP env.var_types id = SOME ty`, destination type evaluation, the same
  forced read, and `lookup_scopes id es1.scopes = SOME entry` imply
  `entry.type = tyv`.
- `value_has_type_memory_wf` supplies `val_wf` from runtime value typing;
  the footprint theorem itself uses this existing fact. Neither `val_wf` nor
  `value_has_type` is an ownership predicate for memory padding.

## Empty length-bearing branch

`memory_rhs_empty_read_destination` exactly matches the checked goal:

```sml
!cx env e es ty tyv.
  env.type_defs = get_tenv cx /\ well_typed_expr env e /\
  is_empty_value_expr e /\ has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ty /\
  evaluate_type (get_tenv cx) ty = SOME tyv ==>
  (do r <- eval_expr cx e; read_result cx r od) es =
  (INL (default_value tyv), es)
```

`type_widens_to_has_length_word` exactly matches
`!t u tenv. has_length_word t /\ type_widens_to tenv t u ==>
 has_length_word u`.
Together with the checked assignment typing implication, these validate the
source-side default and destination length-word classification. They do not
identify or execute the compiler's special empty-assignment suffix. That is
C1.7.2's execution-qualification boundary, not a zero-size instance of the
nonempty argument.

## Exact unestablished execution antecedents

The current `bodyFullAssignMemoryValue.body_full_assign_local_memory_value_path`
requires, among its other antecedents:

```sml
ptr_covers G tn xs s (type_memory_size stv) /\
ptr_covers G tn p s (type_memory_size dtv) /\
w2n sw + type_memory_size stv < dimword (:256) /\
(type_memory_size stv = 0 \/
 w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
(w2n sw + type_memory_size stv <= w2n dw \/
 w2n dw + type_memory_size dtv <= w2n sw)
```

Full static source coverage and the final disjointness disjunction have **not**
been discharged by the representation results above. This matters in both the
direct and staged cases: the theorem requires those facts before its case split
on `loc = SOME LocMemory`.

`loweringPosts.expr_val_at_def` establishes `val_wf` and operand placement with
bounds involving `val_footprint tv v`. It expressly permits a `local_region`
alternative, with `local_val_at`, as well as an own-allocation alternative and
the zero-footprint alternative. It does not itself assert that the RHS local is
different from the assigned local. Runtime bounds alone therefore supply
neither the full `type_memory_size stv` coverage above nor destination alias
freedom. For bytestrings, runtime length/footprint need not fill the declared
capacity. This report makes no claim that the frozen root is false: execution
qualification must decide whether a different existing suffix interface or an
approved interface adjustment is needed. No strengthened header is proposed or
silently installed here.

## Verification and publication audit

- Four local probes passed originally in
  `TO_assignment_cases-L0043-20261116T143053696141Z_m0015_t001`; their final
  ancestor-complete version passed again in
  `TO_assignment_cases-L0043-20261116T143053696141Z_m0022_t004`.
- Exact existing theorem matches: destination capacity
  `TO_assignment_cases-L0043-20261116T141248082485Z_m0009_t001`; runtime footprint,
  empty destination, and length-word propagation respectively
  `TO_assignment_cases-L0043-20261116T143053696141Z_m0012_t001`,
  `TO_assignment_cases-L0043-20261116T143053696141Z_m0012_t002`, and
  `TO_assignment_cases-L0043-20261116T143053696141Z_m0012_t003`.
- Required supporting targets `memoryLocalRhsPropsTheory` and
  `loweringPostsTheory` passed the current support build in
  `TO_assignment_cases-L0043-20261116T143053696141Z_m0021_t001`.
- Publication contains only this diagnostic report. No HOL source is added or
  modified; temporary probes are removed. No proof or completion credit is
  claimed for inherited admissions, foreign stand-ins, independent siblings,
  the memory-value execution theorem's applicability, or the frozen root.
