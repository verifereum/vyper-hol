# STATE: Type Soundness Repair

## Session 40 → 41 Plan

## TOP PRIORITY: Fix Assign_tgt_inl (build blocker)

### Root diagnosis: WRONG DECOMPOSITION
The current proof has 4 levels of case splits (eval_target → eval_expr → materialise → assign_target)
with fragile variable naming in `by` blocks. When HOL generates `r''` but the by-block
targets `r'`, the proof silently proves the wrong thing and then fails at ACCEPT_TAC.

### THE FIX: Replace by-block with inline IH application + combined finish pattern

Instead of:
```
Cases_on `assign_target cx x (Replace x'') r` >>
`state_well_typed r' /\ env_consistent env cx r'` by suspend "Assign_atwt" >>
reverse (Cases_on `q`) >> ...
```

Use (following AugAssign lines 1377-1387):
```
Cases_on `assign_target cx x (Replace x'') r` >>
`state_well_typed r' /\ env_consistent env cx r'` by
  (drule (cj 1 assign_target_well_typed) >>
   disch_then drule >> disch_then drule >>
   strip_tac >> first_x_assum match_mp_tac >>
   rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
   qpat_assum `evaluate_type _ _ = SOME _`
     (fn th => qpat_assum `value_has_type _ _`
       (fn th2 => EXISTS_TAC (th |> concl |> rhs |> rand) >>
                  CONJ_TAC >| [ACCEPT_TAC th, ACCEPT_TAC th2]))
   >> TRY not_type_error_tac) >>
reverse (Cases_on `q`) >> simp_tac (srw_ss()) [return_def] >>
strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
rpt strip_tac >> gvs[] >>
imp_res_tac (cj 1 assign_target_no_return) >>
first_x_assum (qspec_then `v` mp_tac) >> simp_tac (srw_ss()) []
```

Key changes:
1. INLINE the Assign_atwt proof (no suspend, no variable naming fragility)
2. Use the EXACT same finish pattern as AugAssign (which works!)

### Alternative if variable names still clash:
Add `rename1 `assign_target cx x (Replace x'') r = (ao_res, st_at)`` right after
Cases_on, then use `st_at` consistently.

### IMPORTANT: Don't handle materialise INR separately!
Use the AugAssign combined pattern where `reverse (Cases_on `q`) >> simp >> strip >>
rpt CONJ_TAC >> TRY ACCEPT` handles BOTH INR and INL of the final case split.
For materialise INR, the `>- suspend "Assign_tgt_mat_err"` with the separate Resume
block works — keep that structure.

### ALSO: The `by` block variable name MUST match what Cases_on produces.
After `Cases_on `assign_target cx x (Replace x'') r``, the result pair is named
based on all variables in scope. With the IH applied, `r` and `r'` are taken,
so the result state is likely `r''`. But this is fragile — use inline proof
or rename1 to be safe.

## PRIORITY 2: Prove Assert3 (line 1184, currently cheat)

### What Assert3 does:
```
eval_stmt cx (Assert e (AssertReason se)) = do
  tv <- eval_expr cx e;
  switch_BoolV tv
    (return ())
    (do stv <- eval_expr cx se;
        sv <- get_Value stv;
        s <- lift_option_type (dest_StringV sv) "not StringV";
        raise $ AssertException s od)
od
```
### well_typed_stmt gives: well_typed_expr env e (BoolT), well_typed_expr env se (StringT)
### Proof: Try tp_stmt_no_return_tac first. Manual: case split eval_expr, switch_BoolV.
### Key risk: LOW

## PRIORITY 3: Prove Append (line 1193, currently cheat)

### Same monadic bind chain as Assign/AugAssign. Use AugAssign INR pattern.
### Key risk: LOW

## PRIORITY 4: Prove AnnAssign (line 1189, currently just suspended)

### Extra evaluate_type/lift_option_type prefix step.
### Key risk: MEDIUM

## PRIORITY 5: holmake and fix any other failures

## BLOCK PASSING STATUS
### PASSING: Pass, Continue, Break, ReturnNone, ReturnSome, Raise1, Raise2, Raise3,
  Assert1, Assert2, Expr, Log, stmts_nil, stmts_cons, BaseTarget, TupleTarget,
  targets_nil, targets_cons, NameTarget, BareGlobalNameTarget, TopLevelNameTarget,
  AttributeTarget, SubscriptTarget, for_nil, Name, Literal, exprs_nil,
  Assign_inr, Assign_atwt, AugAssign, Assign_tgt_inr (likely, untested with final fix)
### BROKEN (1): Assign_tgt_inl (variable naming + case explosion)
### UNTESTED: Assign_tgt_mat_err (structure looks right)
### CHEATED (3): Assert3, Append, AnnAssign

## WHAT NOT TO TRY
- `>-` (THEN1) inside Resume blocks with parenthesized tactic bodies — gentactic error
  (works with `suspend` but not general tactics)
- `qpat_x_assum` with `_` wildcards on unguarded IH patterns with common variable names — Q_TAC0
  (Works with primed names like `env'`, `st0`, `res0`, `st0'`)
- `by suspend` with hardcoded variable names that may not match Cases_on output
- TRY+NO_TAC inside multi-subgoal contexts (creates case explosion)
- `gvs[definition_def]` in consumer proofs (wrong abstraction level — §3)
- Any approach requiring >3 nested case splits — factor instead

## CORRECT PATTERNS (verified in AugAssign)
- `>-` + `suspend "name"` for separating subgoals in Resume blocks
- `qpat_x_assum `!env' st0 res0 st0'. well_typed_expr _ _ /\ _ ==> _`` for P7 IH
- `qpat_x_assum `!s'' gv t. eval_target _ _ s'' = (INL gv,t) ==> _`` for guarded IH
- `impl_tac >- (rpt CONJ_TAC >> first_assum ACCEPT_TAC)` for IH antecedent discharge
- `reverse (Cases_on `q`) >> simp >> strip >> VAR_EQ >> CONJ >> TRY ACCEPT >> strip >> gvs >>
  imp_res_tac assign_target_no_return >> qspec_then >> simp` for assign_target finish
- INLINE assign_target_well_typed proof (not by-block with hardcoded names)
- `rename1` after Cases_on to lock variable names

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~3959 LOC)
  - AugAssign WORKING REFERENCE: lines 1340-1400
  - Assign_tgt parent: lines 1262-1270
  - Assign_tgt_inr: lines 1272-1286
  - Assign_tgt_inl: lines 1288-1316 (BROKEN — fix decomposition)
  - Assign_tgt_mat_err: lines 1318-1324
  - Assert3 cheat: line 1185
  - Append cheat: line 1193
  - AnnAssign: line 1189 (suspended)
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml
- Workdir: semantics/prop/

## PROOF DECOMPOSITION LESSON (Session 40)
The AugAssign proof works because it has only ONE level of case split at the end
(assign_target INL/INR) and handles BOTH cases uniformly with `>>`. It doesn't
separately handle intermediate monadic step INR cases.

For Assign_tgt, the monadic chain is:
  eval_target → eval_expr → materialise → assign_target

The WRONG decomposition splits EACH step's INL/INR into separate Resume blocks,
creating 4 levels of nested cases and variable naming chaos.

The RIGHT decomposition:
1. Apply ALL IHs upfront (P3 for eval_target, guarded+unguarded P7 for eval_expr)
2. Split ONLY the materialise step (needed because materialise INR requires
   separate handling for type-error analysis)
3. After materialise INL: apply assign_target_well_typed INLINE (not by-block)
4. Split assign_target INL/INR, handle both uniformly like AugAssign

## ABSTRACTION/CLEANUP TASKS
- [ ] Inline Assign_atwt proof (remove fragile by-block with suspend)
- [ ] Create close_p0_inr_err_tac: reusable tactic for P0 INR error cases
- [ ] Remove orphaned Append_atwt comment when Append is proved
- [ ] Consider extracting tp_assign_chain_tac for common eval_expr→materialise→assign_target
