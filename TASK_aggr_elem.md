# TASK: prove body_struct_lit_widened_call_elem and body_make_array_widened_call_elem

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statements (FROZEN)

lowering/bodySimExprCasesScript.sml:

```sml
Theorem body_struct_lit_widened_call_elem:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ok cx (MAP SND kes)) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
      (?e. MEM e (MAP SND kes) /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
      expr_vv_sim ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es

Theorem body_make_array_widened_call_elem:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_ok cx es) ==>
    !tops ctx func cenv env ty' st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
      (?e. MEM e es /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
      expr_vv_sim ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st
```

Both are one job because both go through the same child-store helpers
(lowering/exprSimAggregateChildrenScript.sml, exprSimAggregateLoops,
exprSimAggregates); generalise those once.

## Route

The lowering stores each element with
`compile_store_memory cenv v dst elem_ty (lowered_value_type cenv e)`
(lowering/defs/exprLoweringScript.sml:2180, 2199, 2356). The current case
lemmas (`compile_struct_lit_vv_case`, `compile_make_array_vv_case`,
`compile_struct_lit_case`, `compile_make_array_case` in
lowering/exprSimAggregatesScript.sml) restrict elements to
`int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e`. Generalise
the child store step so an element whose lowered type differs is stored by
`compile_store_memory_typed_run` (non-word, non-bytestring) or the
bytestring store, reading the element's value at `post_value_type cenv e`
from its `vv_post`/`expr_post`. Then drop the restriction from the case
lemmas and prove the two targets from them, the way `body_structlit_case` and
`body_make_array_case` use them.

Internal lemmas you may weaken: the four case lemmas above and the child
store/loop helpers they use.

## Build targets

`holbuild -j4 build bodySimExprCasesTheory exprSimAggregatesTheory exprSimAggregateChildrenTheory exprSimAggregateLoopsTheory`
plus every theory you edit and every theory that uses a lemma whose
statement you change (`git grep` its name under `lowering/`).

## Completion Criteria

1. `holbuild -j4 build <targets>` (targets below) passes at the default
   tactic timeout with proof steps on.
2. The target theorem(s) above are proved (no `cheat` left in them). No other
   theorem gains a `cheat`; the theorems cheated at the start (`git grep -n
   cheat lowering/` at the task's first commit) stay as they are.
3. No new axioms, no `TRY`/`ORELSE` around `metis_tac` or other search, no
   timeout overrides, no changes under `lowering/defs/` or `semantics/`.

## Allowed statement changes

- The target theorem's statement is FROZEN.
- Internal case lemmas the target needs (named below) may be generalised by
  WEAKENING their premises (e.g. dropping or widening the
  `int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e`
  restriction on elements/arms), never by adding premises. Repair their
  consumers. List every changed statement in LEARNINGS.
- New helper lemmas are allowed. Search for an existing one first (`git grep`);
  don't duplicate a theorem that exists elsewhere, even as `[local]`: export or
  move it instead.
- If a statement looks false, record the statement and a concrete
  counterexample in LEARNINGS and stop on it; don't weaken the target.

## Background

An internal call's result buffer is laid out at the callee's declared return
type (`lowered_value_type cenv e`), which a widening call site annotates with
a wider type (`expr_type e`), e.g. `DynArray[uint256, 2]` used as
`DynArray[uint256, 3]`, or a struct/tuple whose members widen. The
postconditions (`expr_post`/`vv_post`, lowering/loweringPostsScript.sml) describe
the value at `post_value_type cenv e`, which is `lowered_value_type cenv e`
for a non-word, non-bytestring internal call and `expr_type e` otherwise.
Where an element/arm type differs from the destination type, the lowering
stores it with `compile_store_memory cenv src dst dst_ty src_ty`
(lowering/defs/contextScript.sml:835), which for `dst_ty <> src_ty`
(non-word, non-bytestring) is `compile_store_memory_typed`: a recursive
typed copy that re-lays the value out at `dst_ty`. Its correctness theorem
is `compile_store_memory_typed_run` (lowering/typedMemoryCopyScript.sml:3531):
from `type_widens_to tenv sty dty`, both types evaluating, the value at
`sty` in memory at `src`, disjoint in-range regions and the struct-metadata
facts, it ends with the value at `dty` at `dst` and a frame.

Facts available from `expr_body_pre`/`expr_sim_inv` (lowering/exprSimHypsScript.sml):
`post_value_type_widens` (type_widens_to (post_value_type cenv e) (expr_type e)),
`post_type_evaluates`, `ifexp_body_pre_intcall_physical`,
`expr_sim_inv_memory_size` (compiler size = semantic size for every evaluated
type), and the struct-metadata conjuncts of `expr_sim_inv_def`
(`sfields_tenv_consistent`, field sizes; check for `acyclic_struct_metadata`).
The bytestring sources are covered separately by `compile_store_bytestring`
proofs already used for same-type stores.

The element/arm's own simulation (`expr_sim`/`expr_vv_sim` of an internal
call) comes from the target's `body_expr_ok` premises; that those rest on the
inherited cheat `body_intcall_case` is fine.

## Domain Constraints

- Change proofs only; keep each step under the 2.5 s tactic timeout.
- Read AGENTS.md for proof style.
- Never `holbuild run`/`repl`; probe with a scratch lemma in a theory you
  build, and delete probe theories before finishing.
