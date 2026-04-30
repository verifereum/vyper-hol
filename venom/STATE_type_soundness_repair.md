# STATE: Type Soundness Repair

## Session 31: Fix gen tactic bug + prove Append incrementally

## PRIORITY 1: Fix close_inr_err_tac / apply_eval_ih

`apply_eval_ih` (line 795) returns a gentactic, which cannot compose with `>>`
in Resume blocks. This breaks `close_inr_err_tac` (line 868) and
`close_inr_err_tac_for` (line 854). Affects: Assign, AugAssign, and any block
using `TRY close_inr_err_tac` or `reverse (Cases_on q) >> simp_tac >> TRY close_inr_err_tac`.

**Fix**: Replace `apply_eval_ih` with explicit IH application:
```sml
(* Instead of: *)
reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
TRY close_inr_err_tac >>
(* Use: *)
Cases_on `q` >> simp_tac (srw_ss()) [] >-
(* INR case - explicit IH *)
(first_x_assum drule >> strip_tac >>
 rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
 rpt strip_tac >> not_type_error_tac) >>
(* INL case continues... *)
```

Consider rewriting `close_inr_err_tac_for` to be a proper tactic:
```sml
fun close_inr_err_tac_for st_term =
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> not_type_error_tac
```

## PRIORITY 2: Prove Append incrementally

CRITICAL: Build ONE tactic at a time, verify with hol_state_at after EACH.

```sml
Resume eval_preserves_swt[Append]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_stmt _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [wts_Append]) >>
  (* VERIFY: check assumptions have well_typed_target env bt (ArrayT (expr_type e) bd) *)
  qpat_assum `well_typed_target env bt _`
    (fn th => ASSUME_TAC (Q.EXISTS (`?ty'. well_typed_target env bt ty'`,
                                    `ArrayT (expr_type e) bd`) th)) >>
  (* VERIFY: check witness added *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  rewrite_tac[ev_Append] >>
  simp_tac std_ss [bind_apply, BETA_THM, UNCURRY, ignore_bind_apply] >>
  (* VERIFY: check goal has case expr *)
  Cases_on `eval_base_target cx bt st` >> rename1 `(res_bt, st_bt)` >>
  (* VERIFY: check goal + assumptions *)
  Cases_on `res_bt` >> simp_tac (srw_ss()) [] >-
  (* INR case for eval_base_target - TERMINAL, safe to use gvs *)
  (strip_tac >> gvs[] >>
   first_x_assum drule >> strip_tac >>
   rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
   rpt strip_tac >> not_type_error_tac) >>
  (* VERIFY INR solved, check INL state *)
  rename1 `eval_base_target cx bt st = (INL tgt_v, st_bt)` >>
  (* APPLY P5 IH - verify which assumption matches *)
  first_x_assum drule_all >> strip_tac >>
  (* VERIFY: P5 conclusions added *)
  (* Discharge guarded P7 IH *)
  qpat_x_assum `!s'' gv t. eval_base_target _ _ _ = _ ==> _`
    (qspecl_then [`st`, `tgt_v`, `st_bt`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* VERIFY: P7 conclusions added, check variable names *)
  Cases_on `eval_expr cx e st_bt` >> rename1 `(res_e, st_e)` >>
  Cases_on `res_e` >> simp_tac (srw_ss()) [] >-
  (* INR case for eval_expr - TERMINAL *)
  (strip_tac >> gvs[] >>
   first_x_assum drule >> strip_tac >>
   rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
   rpt strip_tac >> not_type_error_tac) >>
  (* VERIFY INR solved, check INL state *)
  rename1 `eval_expr cx e st_bt = (INL tv, st_e)` >>
  (* Apply P7 IH: use the unguarded IH already in assumptions from guarded IH discharge *)
  (* IMPORTANT: after guarded P7 IH discharge, the eval_expr IH is a plain
     assumption like: !env st res st'. well_typed_expr env e /\ ... ==>
     ... Not a forall with eval_base_target guard. *)
  (* VERIFY: check exact assumption pattern before writing qspecl_then *)
  (* Then Cases_on materialise, assign_target, etc. step by step *)
  ...
```

NOTE: After guarded P7 IH discharge + strip_tac, the eval_expr IH assumption
has variables renamed (env' → env, etc). Use hol_state_at to see the EXACT
pattern before writing qspecl_then.

## PRIORITY 3: holmake to test untested blocks

After fixing Append and Assign (the known-broken ones), run holmake to see
which of the 28 untested blocks pass. Many may already work. Then fix only
the ones that fail.

## PRIORITY 4: Prove cheated helpers

| Theorem | What | Priority |
|---------|------|----------|
| assign_target_well_typed | Assignment preserves typing | HIGH - blocks Assign, AugAssign, Append |
| env_consistent_pop_scope | Pop scope preserves env_consistent | MEDIUM - For, IntCall |
| bind_arguments_env_consistent | Call arg binding preserves env | MEDIUM - IntCall, ExtCall |
| set_immutable_well_typed | set_immutable preserves typing | MEDIUM - IntCall |
| env_consistent_preserves_tv | Eval preserves tv+env_consistent | LOW - already have partial lemmas |
| eval_expr_not_HashMapRef | Well-typed eval not HashMapRef | LOW - existing lemmas may cover this |

## BLOCK STATUS (55 total, from holmake output with Append cheated)

### PASSING (27): Pass, Continue, Break, ReturnNone, ReturnSome, Raise1, Raise2,
Raise3, Assert1, Assert2, Expr, Log, stmts_nil, stmts_cons, BaseTarget,
TupleTarget, targets_nil, targets_cons, NameTarget, BareGlobalNameTarget,
TopLevelNameTarget, AttributeTarget, for_nil, Name, Literal, exprs_nil

### CHEATED (2): Assert3, Append
NOTE: Append_atwt suspend is orphaned (Append cheated past the suspend call).
Need to also cheat or remove the Append_atwt Resume block.

### KNOWN BROKEN by gen tactic: Assign, AugAssign (use close_inr_err_tac)

### UNTESTED (26): AnnAssign, Array, Attribute, BareGlobalName, Builtin,
CreateTarget, ExtCall, FlagMember, For, If, IfExp, IntCall, Pop, Range,
RawCallTarget, RawLog, RawRevert, SelfDestructTarget, Send, StructLit,
Subscript, SubscriptTarget, TopLevelName, TypeBuiltin, exprs_cons, for_cons

## QPAT_X_ASSUM RULES
- NO wildcards `_` in patterns → Q_TAC0 parse error
- NO Unicode (∃∧⇒∀) → Q_TAC0 parse error, use ASCII (? /\ ==> !)
- Parenthesize existentials: `(?ty. P ty) /\ _` not `?ty. P ty /\ _`

## gvs[] USAGE RULES
- SAFE: terminal cases (after `>-`), final cleanup
- UNSAFE: after case splits when later steps need forall-quantified IHs
- Use `simp_tac (srw_ss()) []` instead for non-terminal case splits
- After gvs[], NEVER use `first_x_assum drule_all` (IH may be consumed)

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~3930 LOC)
  - close_inr_err_tac definition: line 854-868
  - apply_eval_ih definition: line 795
  - tp_materialise_conclusion_tac: line 339
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml (~7307 LOC)
- Workdir: semantics/prop/

## WHAT NOT TO TRY
- Writing 5+ tactic lines without verifying with hol_state_at (FAILED 6x in S29)
- gvs[] after case splits when later steps need IHs
- close_inr_err_tac / apply_eval_ih in Resume blocks (gentactic bug)
- qpat_x_assum with _ wildcards (Q_TAC0)
- first_x_assum drule_all after gvs[] (IH already consumed)
- apply_guarded_ih (uses drule_all internally, may consume wrong IH)
