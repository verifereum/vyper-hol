# C1.12 endpoint-sealed specialization: NO-GO at fixed full frame

## Decisive obstruction

`stmt_state_rel ctx func cenv cx es s0` includes `alloca_room ctx func s0`
(exprLoweringPropsScript.sml:412-415). `alloca_room_def` at :245-248 requires

```sml
lookup_function func.fn_name ctx.ctx_functions = SOME func
```

If the proposed endpoint-sealed function `sealed` retains `func.fn_name`,
then keeping the same ctx and requiring its new stmt_state_rel would imply
`SOME sealed = SOME func`, hence `sealed = func`. A genuinely truncated
function is not equal to the original containing function. For the concrete
closed interval function the operand join is @exit_2 index0 whereas the
original exit block contains SUB through STOP (E0018 instruction computation),
so replacing it by an empty block is a genuine change. This is an exact
contract conflict, not an unverified conjecture about path confinement.

## Instantiation antecedents

- body_exprs_ptr_ok yields body_expr_ptr_ok for the head (bodyPtrPreds:61-67).
  The latter universally quantifies ctx and func (:20-25).
- body_inv tops ctx cenv cx: unchanged when replacing func alone, since it
  has no func argument (bodySim:61-88). But ctx is tied to an actually lowered
  unit by :64-68; replacing ctx to accommodate sealed is not free.
- expr_body_pre cenv cx env operand es: independent of func and ctx
  (exprSimHypsDefs:148-160); operand extraction still needs its existing
  builtin-argument lemma, not a stronger hypothesis.
- lower_value equation: unchanged, compiler independent of containing func.
- fn_has_code sa sb sealed: plausible for prefix truncation if emitted blocks
  are retained and final prefix is kept; would require construction proof.
- fn_inst_ids_distinct sealed: deletion preserves IDs in a properly
  constructed truncation; requires proof but not the decisive problem.
- local_ptrs_reserved, ~ctx_has_dalloca, ~cenv.ce_is_ctor, return-buffer/PC
  not_fresh_at, gas_admissible, ghost_inv, not-halted and start PCs: unchanged
  for same ctx/cenv/source/runtime/ghost (bodyPtrDefs:218-231).
- stmt_state_rel: NOT transferable to a different sealed function with same
  name and ctx, by the exact alloca_room lookup equality above. Its other
  clauses (local_ptrs_rel via state_rel, fmp_room and recorded ALLOCA sizes)
  also depend on func and cannot be dismissed as syntactic prefix facts.

Classification: fixed-ctx nontrivial specialization is ruled out by equality.
Changing ctx is unresolved and would require re-proving actual-module
body_inv, call/evaluation frame and context-dependent execution. No such
replacement is authorized or justified by this audit.

## Forward transport still required if another route changes this barrier

One would need equality of every fetched instruction on a witness; congruent
step_inst including INVOKE/context lookups; ptr_safe_step for original fn;
entry_prov and entry_taint_vars for ALL terminator entry alternatives; full
source/gas synchronization; and transfer of expr_post, ghost_inv, ptr_val_ok,
ptr_buf_ok, ghost_kept and exception posts at the unchanged witness endpoint.
entry_prov/entry_taint_vars inspect target block PHI prefixes (ptrDiscipline
:212-225 for provenance), so fetched-instruction equality alone is insufficient.
A final prefix of length0 can hide nonempty original PHIs, making entry
transport an additional real obligation, not a consequence of fn_has_code.
No claim of congruence of pointer checks under arbitrary function truncation
is made here; the frame obstruction prevents instantiating the judgment first.

## Verdict

Stop this fixed-ctx endpoint-sealing route before constructing a new function
or proving confinement. Per C1.12's approach, the exact frame equality blocks
specialization immediately; therefore its conditional no-instruction barrier
proof is not needed in this episode. This is NOT a counterexample to the
frozen target. Positive finite certificate E0018 remains valid. The prior
arbitrary-function audit must now be read together with this stronger frame
restriction: although fn_has_code alone leaves suffixes free, the actual full
frame forces func to be ctx's function. A strategy exploiting the actual
lowered module could therefore differ from a theorem using fn_has_code alone;
no compiler-wide proof is authorized or attempted here.
