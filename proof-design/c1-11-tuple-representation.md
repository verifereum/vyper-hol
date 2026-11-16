# C1.11.1 — widened tuple representation boundary

## Result and scope

Diagnostic complete on source HEAD `a9dc90977bdc7d641b58171917e7041ec3f901cc`.
Five temporary HOL implication/application tests pass. They establish physical
tuple representation, clean-operand coverage, and component-layout applicability
**under the exact premises printed below**. They do not prove the frozen
`body_assign_tuple_widened_full`, select all compiler branches from that root's
hypotheses, or supply its joint sequential continuation. No production theorem,
semantic definition, frozen header or foreign source was changed.

The temporary theory is reproduced in full below for reproducibility, then
removed from `lowering/`; this report is the deliverable, not a helper export.

## Checked evidence

- Initial four tests: `TO_assignment_cases-L0057-20261116T190236992849Z_m0032_t001`.
- This session rechecked that source: `TO_assignment_cases-L0057-20261116T190236992849Z_m0042_t001`.
- Exact layout-provider signature: `TO_assignment_cases-L0057-20261116T190236992849Z_m0042_t002`; full unchanged provider source: `TO_assignment_cases-L0057-20261116T190236992849Z_m0043_t001`.
- Final build of `c111TupleBoundaryProbeTheory`, `typedCopyCompatibilityPtrTheory`
  and `bodyPtrDefsTheory` passes:
  `TO_assignment_cases-L0057-20261116T190236992849Z_m0047_t001`.
- Exact final temporary source:
  `TO_assignment_cases-L0057-20261116T190236992849Z_m0048_t001`.
- Admission-mechanism scan of that source has no matches:
  `TO_assignment_cases-L0057-20261116T190236992849Z_m0048_t002`.

These builds qualify the tests and used providers, not the unbuilt full tuple
continuation tower. Existing frozen tuple roots remain admitted and assigned to
their production components; none receives completion credit here.

## Actual compiler cut (source inspection, not root application proof)

`tuplePlaceCodeParts.tuple_place_compile_parts` exposes this compiler call after
expression lowering/unwrapping:

```sml
compile_tuple_unpack cenv (lowered_value_type cenv e)
  (is_memory_view e /\ vv_location vv = SOME LocMemory) gs op su = ((),sf)
```

See `lowering/tuplePlaceCodePartsScript.sml:7-21`, read in
`TO_assignment_cases-L0057-20261116T190236992849Z_m0043_t002`.
This theorem's complete provider tower was **not** qualified here.

`lowering/defs/stmtLoweringScript.sml:532-542,574-632` shows that the unpacker
loads all operands at the **lowered element types**, then stores them. A word
component is loaded by value; a complex component remains an address at the
physical prefix-sum offset. There is no preliminary whole-tuple conversion to
logical `expr_type e` in this code. Optional staging copies the physical layout.
The first checked test below fixes the stage flag to `F`; it does **not** derive
that flag from the widened root. The stage/INVALID branches remain to be selected
from the actual root/compiler hypotheses, not assumed away.

For a BaseTarget component `compile_tuple_store_all` obtains `dst_ty` from the
target (falling back to `src_ty`), then dispatches:

- word source + word destination: `compile_store_at_loc`;
- word source + complex destination: INVALID;
- complex source: `compile_assign_value cenv dst_op dst_loc val_op is_prim
  NONE dst_ty src_ty mem_sz`.

In particular the actual last call passes `NONE`, not `SOME LocMemory`, in its
source-location slot. The nearby prose comment is not the executable equation.
Keep `src_ty` (lowered element), logical RHS element type and target `dst_ty`
distinct when applying conversion/store providers. Compiler equation evidence:
`TO_assignment_cases-L0057-20261116T190236992849Z_m0044_t001` and
`TO_assignment_cases-L0057-20261116T190236992849Z_m0048_t004`.

## Complete checked temporary theory

```sml
Theory c111TupleBoundaryProbe
Ancestors bodyPtrDefs loweringPosts stmtLowering exprLowering compileEnv vyperAST
  valueEncodingDefs vyperTyping venomExecSemantics venomState ptrDiscipline
  typedCopyCompatibilityPtr
Libs monadsyntax

Theorem no_stage_probe:
  compile_tuple_unpack cenv (TupleT ltys) F targets op =
    do vals <- compile_tuple_load_all cenv op ltys 0;
       compile_tuple_store_all cenv ltys targets vals od
Proof
  simp[compile_tuple_unpack_def, comp_return_def, comp_bind_def, FUN_EQ_THM]
QED

Theorem tuple_post_type_probe:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys ==>
  post_value_type cenv e = TupleT ltys
Proof
  rpt strip_tac >> Cases_on `e` >>
  gvs[vyperASTTheory.expr_type_def, lowered_value_type_def, post_value_type_def]
  >- (Cases_on `b` >> gvs[lowered_value_type_def, concat_buffer_type_def, expr_type_def])
  >- (Cases_on `t0` >> gvs[lowered_value_type_def, expr_type_def]) >>
  rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
  gvs[lowered_value_type_def, post_value_type_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem tuple_post_representation_probe:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  expr_post H ctx func cenv cx e es sa sb s0 ee (ArrayV (TupleV vs)) op s ==>
  stmt_state_rel H ctx func cenv cx ee s /\
  expr_val_at cenv cx (TupleT ltys) sa sb ee (ArrayV (TupleV vs)) op s /\
  ?w. eval_operand op s = SOME w /\
      tuple_in_memory vs ltvs (w2n w) s.vs_memory /\ tuple_val_wf vs ltvs
Proof
  strip_tac >>
  `post_value_type cenv e = TupleT ltys` by metis_tac[tuple_post_type_probe] >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
      is_word_type_def, val_in_memory_def, val_wf_def] >>
  metis_tac[]
QED

Theorem tuple_buffer_coverage_probe:
  ptr_buf_ok cenv e op G s /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
  eval_operand op s = SOME w /\
  type_memory_bytes cenv (lowered_value_type cenv e) <> 0 ==>
  ?p. op = Var p /\ lookup_var p s = SOME w /\
      ptr_covers G tn p s (type_memory_bytes cenv (lowered_value_type cenv e))
Proof
  strip_tac >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  simp[ptr_buf_ok_def] >> strip_tac >>
  gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]
QED

Theorem tuple_component_layout_application_probe:
  arg_type_fits (TupleT ltys) (TupleT tys) /\
  evaluate_type tenv (TupleT ltys) = SOME (TupleTV ltvs) /\
  evaluate_type tenv (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH ltys ==>
  LENGTH ltys = LENGTH tys /\
  arg_type_fits (EL i ltys) (EL i tys) /\
  evaluate_type tenv (EL i ltys) = SOME (EL i ltvs) /\
  evaluate_type tenv (EL i tys) = SOME (EL i tvs)
Proof
  strip_tac >> drule_all arg_type_fits_tuple_layouts >>
  strip_tac >> gvs[]
QED
```

The fifth test directly applies the existing exported theorem; it does not
install a duplicate component-layout lemma. It verifies lowered-to-logical
layout fit at each index, **not** lowered-to-destination value encoding.

## Precise remaining application premises

To apply these checked implications to the frozen root, the production proof
must still obtain, at the chosen actual RHS endpoint:

1. `expr_type e = TupleT tys`, `lowered_value_type cenv e = TupleT ltys`,
   evaluated physical/logical layouts and the tuple-shaped source value;
2. the canonical `expr_post H ...` plus `ptr_buf_ok` and `ptr_val_ok` facts
   for this same operand and endpoint, and nonzero physical capacity for the
   coverage implication (or handle zero capacity separately);
3. `arg_type_fits (TupleT ltys) (TupleT tys)` from the frozen typing/support
   context, rather than adding it to the root;
4. the actual stage flag/branch, target-list lengths, target destination types
   and per-target typing compatibility. The fifth implication supplies only
   physical-RHS-to-logical-RHS fit/evaluations once its premises hold. It does
   not supply `arg_type_fits (EL i ltys) dst_ty` or memory encoding at `dst_ty`;
5. an ordinary load/store execution with one endpoint and ghosts chosen before
   all valid-horizon observations, including pointer coverage/taint, physical
   component representations, remaining-component frame preservation, actual
   FMP/no-wrap, exceptional callback and source-target evaluation obligations.

No one of these unperformed applications is asserted false. The tests establish
neither a missing-contract counterexample nor an external-precondition stop.
In particular the fit theorem assumes both successful evaluations; it does not
manufacture them from layout syntax. Existing source
`exprSimIfExpCompat.ifexp_compat_body_pre_lowered_type` has an additional
`int_calls_expr e = [] \/ same_memory_layout ...` guard (source-only inspection,
`TO_assignment_cases-L0057-20261116T190236992849Z_m0048_t005`), so simply naming
that theorem is not a checked discharge of the frozen root's application.

## Why the existing sequential pointer theorem does not close the full cut

`lowering/assignTuplePtrSequentialScript.sml:94-163`, exact read
`TO_assignment_cases-L0057-20261116T190236992849Z_m0044_t003`, exports
`tuple_store_sequential_path_ptr`. It assumes a singleton-store callback that
already proves execution, state/ghost relation and preservation of untouched
memory; it does not construct that callback. Its premises include
`~ctx_has_dalloca ctx` (both callback and outer theorem), `stmt_state_rel H ...`
and `ghost_inv H ...`, with `H` free at this theorem's level. Its conclusion
chooses `?t G' tn'` and proves `gas_path_ptr ... (OK t)` for that H.

This is not the required full interface `?t G' tn'. ... /\ !H. valid_horizon ...
==> ...` with one ordinary execution endpoint preceding H. Moving its existential
witnesses out through H would be unjustified. Nor does its normal-only pointer
conclusion provide the full normal/exceptional callback. The approved resource
ports do not themselves prove this quantifier/preservation bridge.

Accordingly the next mathematical planning boundary is a uniform sequential
continuation over the actual physical component loads and per-target stores,
not a whole-tuple conversion fiction or another layout-only lemma. No new
production helper signature is proposed or authorized by this report. Root
assembly and its production helper ownership remain with the strategist/lead.

## Publication integrity

The temporary script was removed with `restore_file`
(`TO_assignment_cases-L0057-20261116T190236992849Z_m0050_t001`). Final pre-stage
`git diff --stat` was empty and `git status --short` listed only this new report
(`TO_assignment_cases-L0057-20261116T190236992849Z_m0050_t003`,
`TO_assignment_cases-L0057-20261116T190236992849Z_m0050_t004`). The report's
embedded SML also passed the admission-mechanism text scan
(`TO_assignment_cases-L0057-20261116T190236992849Z_m0050_t002`). Thus this
publication introduces no production SML changes or admissions; existing root
proof debt and foreign provider qualifications are not concealed or discharged.
