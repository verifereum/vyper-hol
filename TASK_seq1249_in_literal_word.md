# TASK: prove compile_bop_in_literal_word_case (in / not in on an array literal of words)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimBopInLiteralWordScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

In `lowering/exprSimBopInLiteralWordScript.sml`:

```sml
Theorem compile_bop_in_literal_word_case:
  !nocalls ctx func cenv cx ann bop e1 a t n elems.
    is_word_type (expr_type e1) /\ (bop = In \/ bop = NotIn) /\
    exprs_case nocalls ctx func cenv cx (e1::elems) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) /\
    expr_vv_case nocalls ctx func cenv cx
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
```

`compile_bop_in_literal_word_sim` (the same case at `expr_ok`, nocalls = T)
is already derived from it in the same file; keep that derivation and its
statement unchanged.

Supporting definitions (do not change them): `expr_sim_case_def`,
`expr_vv_case_def`, `exprs_case_def`, `expr_body_pre_def`, `expr_ok_def`, `expr_sim_ok_def`,
`expr_vv_ok_def`, `expr_sim_pre_def`, `expr_sim_below_def` in
`lowering/exprSimHypsDefsScript.sml`; `expr_sim_def`, `expr_post_def`,
`expr_vv_sim_def` in `lowering/exprSimDefsScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build exprSimBopInLiteralWordTheory` passes at the default
   tactic timeout, and `compile_bop_in_literal_word_case`,
   `compile_bop_in_literal_word_sim` and every helper you add are proved
   without `cheat`.
2. All new helpers live in `lowering/exprSimBopInLiteralWordScript.sml` or in
   new leaf theories next to it under `lowering/` (named
   `exprSimBopInLiteralWord*Script.sml`). No duplicate of a theorem that
   already exists in an ancestor: reuse it.
3. The theorem statement above, and `compile_bop_in_literal_word_sim`'s, are
   byte-for-byte unchanged.

**If the theorem is false as stated:** produce the counterexample (concrete
source expression and state), state the tightest fix, and stop. Do NOT weaken
the statement.

## Build

```
holbuild -j4 build exprSimBopInLiteralWordTheory
```

(from this directory, the one with `holproject.toml`)

## Background

vyper-hol proves the Vyper→Venom lowering correct expression by expression.
`expr_sim_case nocalls ctx func cenv cx e` / `expr_vv_case ...` say the
lowering of `e` simulates its source evaluation from any state satisfying
`expr_body_pre` (with `nocalls`, also `int_calls_expr e = []`; with
`nocalls = F`, internal calls in operands are allowed). `exprs_case` gives
those judgments for each operand at the states where the operands before it
evaluated (as `evaluate_ind` gives them). The lowering of `e` simulates its source evaluation
both as a word-valued operand (`expr_sim`, through `lower_value`) and as a
value/pointer (`expr_vv_sim`, through `compile_expr`), under the gas-counted
simulation `gas_outcome`. This theorem is the case `x in [a, b, ...]` /
`x not in [...]` where the right operand is an array literal and the needle
has a word type. The lowering unrolls the literal (Vyper's
`_lower_list_literal_membership`): see `compile_builtin_dispatch_body` (Bop,
`is_ArrayT rhs_ty`, `Builtin _ (MakeArray _ _) elems` arm) and
`compile_list_membership_in_def` / `compile_list_membership_notin_def` in
`lowering/defs/exprLoweringScript.sml` (around lines 700-735 and 3030-3060).

The source side: `evaluate_builtin_def` (Bop and MakeArray arms) in
`semantics/vyperContextScript.sml`; `evaluate_binop_def` (In, NotIn via
`binop_negate`) and `evaluate_in_array_def` in
`semantics/vyperValueOperationScript.sml`; `make_array_value_def` and
`enumerate_static_array` in `semantics/vyperValueScript.sml`; typing
`well_typed_binop_def` and `well_typed_builtin_app_def` (MakeArray) in
`semantics/type/vyperTypeSystemScript.sml`.

## Domain Constraints

- Edit only `lowering/exprSimBopInLiteralWordScript.sml` and new leaf
  theories next to it. Do not edit any other file: not semantics, not
  `lowering/defs/`, not shared ancestors (`exprSimWordArgs`, `exprSimHyps`,
  `exprSimDefs`, ...). If something in an ancestor is wrong or missing, put
  the helper in your leaf.
- Several ancestor theories in this worktree have their proofs replaced by
  `cheat` locally (an uncommitted overlay: the base cut doesn't build them
  yet). Their statements are the real ones; use them freely. Never edit,
  stage or commit those files, and don't try to repair their proofs. The
  `holbuild check` cheat findings inherited from them are expected; only
  cheats in your own files count.
- Do not prove this through `compile_expr_sim`, `body_sim_mutual` or any
  theorem whose ancestry includes this theorem (that is circular). The
  needle's and elements' judgments come from the `exprs_case` hypothesis.
- The lemma must hold for both `nocalls = T` and `nocalls = F`; the body
  simulation uses it at `F`.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with
  `>~`, `>-`, `>|`. Never raise the tactic timeout; split slow steps.
- No `let` in theorem statements; no new axioms; no new definitions unless
  essential (prefer existing ones).
- Don't use `holbuild run` or `holbuild repl`; probe with scratch theorems in
  the build.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target theory | `lowering/exprSimBopInLiteralWordScript.sml` | statement + intuition comment |
| Consumer | `lowering/exprSimOperatorsScript.sml` (`compile_bop_in_literal_sim`) | how the theorem is used |
| Word-argument engine (base, gas-counted) | `lowering/exprSimWordArgsScript.sml`; real proofs in `alan-ref/exprSimWordArgsScript.unoverlaid.sml.txt` | `lower_word_args`, `wb_args_ready`, `lower_word_args_sim`, `word_builtin_frag`, `word_builtin_frag_success`, `eval_expr_builtin_action`, `eval_exprs_cons_cases`, `compile_word_builtin_sim` (normal/exit/exempt) |
| Word builtins using the engine | `lowering/exprSimWordBuiltinsScript.sml`; real proofs in `alan-ref/exprSimWordBuiltinsScript.unoverlaid.sml.txt` | `compile_*_run` (run_inst_seq of emitted ops), `compile_*_word_frag`, `compile_typed_word_builtin_sim` (how a consumer builds `wb_args_ready` from smaller judgments) |
| Judgment definitions | `lowering/exprSimHypsDefsScript.sml`, `lowering/exprSimDefsScript.sml`, `lowering/exprSimHypsScript.sml`, `lowering/exprSimSourceScript.sml` | `expr_ok_stack` (vv part from sim part), `expr_body_pre_*` / `expr_sim_pre_*` facts, `int_calls_exprs_mem` |
| Older proof of the same case (guide only) | `alan-ref/harvest/*.txt` | astra's proof of `compile_bop_in_literal_sim` on an older tree whose `expr_sim` was NOT gas-counted and whose membership semantics (`evaluate_membership`) and lowering (`emit_membership_eqs`, `fold_membership_or`) differ from this base. Source-side lemmas (`enumerate_static_array_membership`, `eval_expr_literal_membership`, `expr_body_pre_literal_membership`, `expr_body_pre_eval_exprs_success`, `typed_val_to_w256_prim_MEM`) in `harvest/exprSimHypsScript.sml.txt` and `harvest/exprSimCompareScript.sml.txt`; membership-chain correctness in `harvest/exprSimOpsScript.sml.txt` (~line 700-900); its top proof in `harvest/exprSimOperatorsScript.sml.txt` (`compile_bop_in_literal_sim`) |
| Equality operand encoding | `lowering/exprSimCompareScript.sml` | `typed_val_to_w256_bytes_11` and the compare proofs for word equality |
| Lowering defs | `lowering/defs/exprLoweringScript.sml`, `lowering/defs/exprCallBoundsScript.sml` (`expr_list_member_bound`, `expr_child_callback`), `compile_multi_exprs_callback_cong` | |
| Encoding | `lowering/defs/valueEncodingScript.sml` | `val_to_w256`, `typed_val_to_w256` |

## Notes

- `alan-ref/` is untracked reference material; don't commit it.
