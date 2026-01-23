# Proof Plan: assign_target_spec_preserves_name_targets

## Goal

Prove that assigning to any target preserves the existence of name targets:

```sml
Theorem assign_target_spec_preserves_name_targets:
  ∀P cx st av ao n.
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
```

## Key Definitions

### lookup_name_target
```sml
lookup_name_target cx st n = lookup_base_target cx st (NameTarget n)
```

### lookup_base_target
```sml
lookup_base_target cx st tgt =
  case eval_base_target cx tgt st of
  | (INL (loc, sbs), _) => SOME (BaseTargetV loc sbs)
  | (INR _, _) => NONE
```

### eval_base_target (NameTarget n)
```sml
eval_base_target cx (NameTarget id) = do
  sc <- get_scopes;
  n <<- string_to_num id;
  svo <<- if IS_SOME (lookup_scopes n sc) then SOME $ ScopedVar id else NONE;
  ivo <- if cx.txn.is_creation
         then do imms <- get_immutables cx; return $ immutable_target imms id n od
         else return NONE;
  v <- lift_sum $ exactly_one_option svo ivo;
  return $ (v, [])
od
```

### assign_target cases
1. `ScopedVar id` - updates scopes via `find_containing_scope` + `|+`
2. `TopLevelVar src_id_opt id` - updates `st.globals`
3. `ImmutableVar id` - updates immutables map
4. `TupleTargetV gvs` - recursive on components

## Core Insight

`eval_base_target (NameTarget n)` returns success iff exactly one of:
- `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` (produces `ScopedVar`)
- `IS_SOME (FLOOKUP imms (string_to_num n))` (produces `ImmutableVar`, only during creation)

The result is `(location, [])` where location is `ScopedVar n` or `ImmutableVar n`.

**Key property:** `assign_target` preserves *existence* of variables (not their values):
- For scopes: updates an existing entry with `|+`, preserves domain
- For immutables: updates an existing entry with `|+`, preserves domain

## Proof Dependencies

### Prerequisite Theorems (currently cheated)

#### 1. assign_target_preserves_scopes (line 132-141)
```sml
(∀cx av ao st res st'.
   assign_target cx av ao st = (INL res, st') ⇒
   (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes))) ∧
(∀cx gvs vs st res st'.
   assign_targets cx gvs vs st = (INL res, st') ⇒
   (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes)))
```

**Proof sketch:**
- Induct on `assign_target`/`assign_targets`
- **ScopedVar case:** `set_scopes $ pre ++ env |+ (ni, a') :: rest`
  - Use `find_containing_scope_structure`: `sc = pre ++ env :: rest`
  - Use `lookup_scopes_update_preserves`: updating preserves IS_SOME
- **TopLevelVar case:** Only modifies `st.globals`, not `st.scopes`
- **ImmutableVar case:** Only modifies `st.globals`, not `st.scopes`
- **TupleTargetV case:** Induction hypothesis

#### 2. assign_target_preserves_immutables (line 146-163)
```sml
(∀cx av ao st res st'.
   assign_target cx av ao st = (INL res, st') ⇒
   ∀n gbs gbs'.
     ALOOKUP st.globals cx.txn.target = SOME gbs ∧
     ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
     IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
     IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n)) ∧
(∀cx gvs vs st res st'.
   assign_targets cx gvs vs st = (INL res, st') ⇒ ... same ...)
```

**Proof sketch:**
- **ScopedVar case:** `set_scopes` only modifies `st.scopes`, globals unchanged
- **TopLevelVar case:** `set_global` updates `mg.mutables`, not `mg.immutables`
- **ImmutableVar case:** `set_immutable` updates immutables with `|+`, preserves IS_SOME for existing keys
- **TupleTargetV case:** Induction hypothesis

## Main Proof Strategy

### Step 1: Unfold definitions
```sml
simp[assign_target_spec_def, lookup_name_target_def, lookup_base_target_def]
```

### Step 2: Case split on assign_target result
```sml
Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[]
```

### Step 3: Analyze eval_base_target (NameTarget n)
The hypothesis `lookup_name_target cx st n = SOME av'` implies:
```sml
eval_base_target cx (NameTarget n) st = (INL (loc, []), _)
```
where `loc` is either `ScopedVar n` or `ImmutableVar n`.

### Step 4: Show eval_base_target succeeds in st' too

Two sub-cases based on how the name was resolved:

#### Case A: ScopedVar (from lookup_scopes)
- Hypothesis: `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` and
  `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n) = NONE` (or not during creation)
- By `assign_target_preserves_scopes`: 
  `IS_SOME (lookup_scopes (string_to_num n) st'.scopes)`
- By `assign_target_preserves_immutables`: immutables check still fails (if was NONE) or passes (if was checking)
- Need to also show immutables remain NONE to maintain `exactly_one_option` invariant

#### Case B: ImmutableVar (from immutables, during creation only)
- Hypothesis: `cx.txn.is_creation`, `FLOOKUP imms (string_to_num n) = SOME _`, 
  and `lookup_scopes (string_to_num n) st.scopes = NONE`
- By `assign_target_preserves_immutables`: 
  `IS_SOME (FLOOKUP imms' (string_to_num n))`
- By `assign_target_preserves_scopes`: scopes still have NONE (if was NONE)

### Step 5: Conclude the result is the same
Since both preconditions for `exactly_one_option` are preserved, the same `location` is returned.

## Helper Lemmas Needed

### 1. assign_target_preserves_globals_target
```sml
∀cx av ao st res st'.
  assign_target cx av ao st = (INL res, st') ⇒
  IS_SOME (ALOOKUP st.globals cx.txn.target) ⇒
  IS_SOME (ALOOKUP st'.globals cx.txn.target)
```
Actually, we need the stronger property that the globals for `cx.txn.target` exist both before and after (and the assign modifies appropriately).

### 2. eval_base_target_NameTarget_success_characterization
```sml
∀cx st n loc.
  eval_base_target cx (NameTarget n) st = (INL (loc, []), st) ⇒
  (loc = ScopedVar n ∧ IS_SOME (lookup_scopes (string_to_num n) st.scopes) ∧
   (cx.txn.is_creation ⇒ FLOOKUP imms (string_to_num n) = NONE)) ∨
  (loc = ImmutableVar n ∧ cx.txn.is_creation ∧ 
   IS_SOME (FLOOKUP imms (string_to_num n)) ∧
   ¬IS_SOME (lookup_scopes (string_to_num n) st.scopes))
```

### 3. exactly_one_option_preserved
```sml
∀svo ivo svo' ivo'.
  IS_SOME svo = IS_SOME svo' ∧
  IS_SOME ivo = IS_SOME ivo' ⇒
  (IS_SOME (exactly_one_option svo ivo) ⇔ IS_SOME (exactly_one_option svo' ivo'))
```

## Detailed Proof Steps

```sml
Theorem assign_target_spec_preserves_name_targets:
  ∀P cx st av ao n.
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
Proof
  simp[assign_target_spec_def, lookup_name_target_def, lookup_base_target_def] >>
  rpt strip_tac >>
  (* Case split on assign_target result *)
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  (* Now need to show: eval_base_target cx (NameTarget n) r = (INL (loc, sbs), _) 
     where (loc, sbs) matches av' *)
  
  (* Analyze the original eval_base_target success *)
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  
  (* Case on is_creation *)
  Cases_on `cx.txn.is_creation` >> gvs[] >- (
    (* Creation case: both scopes and immutables are checked *)
    simp[get_immutables_def, get_immutables_module_def, bind_def,
         get_current_globals_def, lift_option_def, return_def, lift_sum_def] >>
    Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[] >>
    Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
    Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >>
    gvs[exactly_one_option_def, return_def, raise_def, immutable_target_def] >>
    (* ... case analysis ... *)
    strip_tac >> gvs[] >>
    
    (* Use preservation lemmas *)
    `IS_SOME (lookup_scopes (string_to_num n) r.scopes) = 
     IS_SOME (lookup_scopes (string_to_num n) st.scopes)`
      by metis_tac[assign_target_preserves_scopes] >>
    (* ... similar for immutables ... *)
    
    (* Reconstruct eval_base_target in new state *)
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def, ...]
  ) >>
  
  (* Non-creation case: only scopes checked *)
  simp[lift_sum_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[exactly_one_option_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  
  (* Use scope preservation *)
  `IS_SOME (lookup_scopes (string_to_num n) r.scopes)`
    by metis_tac[assign_target_preserves_scopes] >>
  
  (* Reconstruct *)
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def, lift_sum_def,
       exactly_one_option_def]
QED
```

## Task Order

1. **First:** Prove `assign_target_preserves_scopes`
   - This is the foundational lemma
   - Uses mutual induction on assign_target/assign_targets
   - Key helper: `lookup_scopes_update_preserves`

2. **Second:** Prove `assign_target_preserves_immutables`
   - Similar structure to (1)
   - Key insight: only ImmutableVar case touches immutables, and it uses `|+`

3. **Third:** Prove `assign_target_spec_preserves_name_targets`
   - Uses both (1) and (2)
   - Main work is case analysis on eval_base_target

## Complexity Estimate

- `assign_target_preserves_scopes`: ~50-80 lines
- `assign_target_preserves_immutables`: ~40-60 lines  
- `assign_target_spec_preserves_name_targets`: ~60-100 lines

Total: ~150-240 lines of proof

## Potential Issues

1. **globals existence:** Need to track that `ALOOKUP st.globals cx.txn.target` remains SOME. This should be preserved by all assign_target cases.

2. **exactly_one_option invariant:** The delicate part is that we need to preserve both:
   - The existence check (IS_SOME)
   - The mutual exclusion (exactly one of svo/ivo is SOME)

3. **State threading:** `eval_base_target` is pure for `NameTarget` (returns same state), but we need to verify this is preserved across the transformation.

## Existing Helper Theorems to Leverage

From `vyperAssignTargetSpecScript.sml`:
- `lookup_scopes_find_containing` (line 68)
- `find_containing_scope_pre_none` (line 82)
- `lookup_scopes_update` (line 94)
- `find_containing_scope_structure` (line 104)
- `lookup_scopes_update_preserves` (line 117)
- `assign_target_preserves_scopes` (line 132) - PROVEN

These are already proven and provide the core facts about scope manipulation.

## Current Progress (Session 4) - Batch/Interactive Discrepancy

### Status
The `assign_target_preserves_globals_and_immutables` theorem is currently **cheated** due to a discrepancy between interactive and batch mode proofs.

### The Problem
The ScopedVar case proof works interactively but fails in batch mode. The issue is with pattern matching on auto-generated state variable names:

1. **Interactive mode:** After processing the ScopedVar case, we get an assumption like:
   `s'³' with scopes := x0 ⧺ x1 |+ (string_to_num id,a')::x3 = st'`
   
   We can use `qpat_x_assum \`_ with scopes := _ = st'\` (SUBST1_TAC o SYM)` to substitute
   and get `s'³'.globals = (s'³' with scopes := ...).globals` which simplifies to T.

2. **Batch mode:** The pattern `_ with scopes := _ = st'` doesn't match because:
   - The auto-generated name `s'³'` is different in batch mode
   - Or the assumption structure is slightly different

### Attempted Solutions
1. Using `fs` instead of `gvs` to preserve the original variable name `st'` - didn't help
2. Using `sg` with explicit `>-` subgoals - the subgoal tactic still fails to find the pattern
3. Using Cases_on to trace through the state chain - works interactively but the final SUBST1_TAC fails in batch

### Root Cause Analysis
The fundamental issue is that HOL4's batch processing generates different temporary variable names than interactive mode. The proof relies on matching a specific pattern in the assumptions, but the pattern involves auto-generated names that differ between modes.

### Potential Fixes to Try
1. **Use `first_x_assum` with a predicate** instead of `qpat_x_assum` - more robust matching
2. **Use `rename1` early** to give the state a stable name before processing
3. **Restructure the proof** to not depend on the record update pattern at all
4. **Use `CONV_TAC` or `ONCE_REWRITE_TAC`** to handle the record update differently

### Files Changed
- `vyperAssignTargetSpecScript.sml`: Lines 231-341 contain the cheated proof with the original commented out

### Build Status
The file builds with CHEATED warnings. The derived theorems (`assign_target_preserves_immutables` and `assign_target_preserves_globals`) use `metis_tac` on the cheated combined theorem, so they also require the cheat.

## Current Progress (Session 3) - Combined Theorem Proven

### Key Achievement
The circular dependency has been resolved by proving both `assign_target_preserves_globals` and `assign_target_preserves_immutables` simultaneously in a single mutual induction proof.

The combined theorem `assign_target_preserves_globals_and_immutables` proves:
1. For any `tgt`, `IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)`
2. Immutables preservation (as before)

The proof was developed interactively and works. The full proof script is below.

### Remaining Steps
1. Convert the interactive proof to batch (the >~ syntax doesn't work, need positional tactics)
2. Remove cheats from the derived theorems (they should follow from the combined theorem)
3. Prove the main theorem

## Full Proof Script for assign_target_preserves_globals_and_immutables

```sml
ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >-
(* ScopedVar case *)
(simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
      lift_option_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
      ignore_bind_def, set_scopes_def] >>
 strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, bind_def, set_scopes_def] >>
 `st.globals = st'.globals` by (
   Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
   PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
   Cases_on `assign_subscripts x2 (REVERSE is) ao` >> gvs[return_def, raise_def]) >>
 gvs[] >> rw[] >> gvs[]) >-
(* TopLevelVar case *)
(strip_tac >> gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
                  lookup_global_def, bind_def, get_current_globals_def, lift_option_def,
                  LET_THM, set_global_def, set_current_globals_def] >>
 `st.globals = s'³'.globals ∧ ALOOKUP st.globals cx.txn.target = SOME gbs`
   by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
 `s'³'.globals = s''.globals`
   by (Cases_on `FLOOKUP (get_module_globals src_id_opt gbs).mutables (string_to_num id)` >>
       gvs[return_def, raise_def]) >>
 `s''.globals = s'⁴'.globals` by (Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]) >>
 Cases_on `assign_toplevel (type_env ts) tv (REVERSE is) ao` >-
 (gvs[lift_sum_def, return_def] >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_def, get_current_globals_def, AllCaseEqs(), return_def, raise_def,
       set_current_globals_def, ignore_bind_def, LET_THM] >>
  strip_tac >> gvs[bind_def, ignore_bind_def, get_current_globals_def,
                   set_current_globals_def, return_def, LET_THM, AllCaseEqs(),
                   lift_option_def] >>
  conj_tac >- (Cases_on `cx.txn.target = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `src_id_opt` >> simp[get_module_globals_def, set_module_globals_def,
                                alistTheory.ALOOKUP_ADELKEY]) >-
 gvs[lift_sum_def, raise_def]) >-
(* ImmutableVar case *)
(strip_tac >> gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
                  bind_def, get_current_globals_def, lift_option_def, LET_THM,
                  set_immutable_def, set_current_globals_def, get_immutables_def,
                  get_immutables_module_def] >>
 `st.globals = s''.globals ∧ ALOOKUP st.globals cx.txn.target = SOME gbs`
   by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
 `s''.globals = s'⁴'.globals`
   by (Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num id)` >>
       gvs[return_def, raise_def]) >>
 Cases_on `assign_subscripts a (REVERSE is) ao` >> gvs[return_def, raise_def] >-
 (gvs[lift_sum_def, return_def] >> conj_tac >-
  (rpt strip_tac >> qpat_x_assum `do _ od _ = _` mp_tac >>
   simp[bind_def, ignore_bind_def, get_current_globals_def, set_current_globals_def,
        return_def, LET_THM, AllCaseEqs(), lift_option_def] >>
   strip_tac >> gvs[] >>
   Cases_on `cx.txn.target = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]) >>
  rpt strip_tac >> qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def, get_current_globals_def, set_current_globals_def,
       return_def, LET_THM, AllCaseEqs(), lift_option_def] >>
  strip_tac >> gvs[] >>
  simp[get_module_globals_def, set_module_globals_def, alistTheory.ALOOKUP_ADELKEY,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `string_to_num id = n` >> simp[] >>
  gvs[get_module_globals_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP (case ALOOKUP gbs NONE of NONE => empty_module_globals
                     | SOME mg => mg).immutables (string_to_num id)` >>
  gvs[return_def, raise_def]) >-
 gvs[lift_sum_def, raise_def]) >-
(* TupleTargetV with TupleV *)
(strip_tac >> rpt gen_tac >> strip_tac >>
 gvs[Once assign_target_def, check_def, AllCaseEqs(), return_def, raise_def] >>
 Cases_on `LENGTH gvs = LENGTH vs` >> gvs[] >-
 (fs[bind_def, assert_def, return_def] >>
  Cases_on `assign_targets cx gvs vs st` >> Cases_on `q` >-
  (gvs[return_def] >> first_x_assum drule >> simp[]) >-
  gvs[]) >-
 fs[assert_def, raise_def]) >-
(* Other TupleTargetV cases: all vacuously true *)
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
simp[Once assign_target_def, raise_def] >-
(* assign_targets [] [] *)
(simp[Once assign_target_def, return_def] >> strip_tac >> gvs[] >> rw[] >> gvs[]) >-
(* assign_targets cons case - the key case that needs both IHs *)
(strip_tac >> rpt gen_tac >> strip_tac >>
 gvs[Once assign_target_def, bind_def, get_Value_def, AllCaseEqs(), return_def, raise_def] >>
 `s'' = s'³'` by (Cases_on `tw` >> gvs[get_Value_def, return_def, raise_def]) >> gvs[] >>
 last_x_assum (qspec_then `st` (drule_then assume_tac)) >>
 first_x_assum (qspec_then `s''` (drule_then assume_tac)) >>
 conj_tac >- metis_tac[] >>
 rpt strip_tac >>
 `IS_SOME (ALOOKUP s''.globals cx.txn.target)` by (gvs[] >> first_x_assum irule >> simp[]) >>
 Cases_on `ALOOKUP s''.globals cx.txn.target` >> gvs[]) >-
(* assign_targets [] (v::vs) - vacuous *)
simp[Once assign_target_def, raise_def] >-
(* assign_targets (v::vs) [] - vacuous *)
simp[Once assign_target_def, raise_def]
```

## Current Progress (Session 2)

### Completed
- **assign_target_preserves_scopes**: Fully proven (lines 132-194)
- **assign_target_spec_preserves_name_targets proof sketch**: The main theorem proof has been developed interactively and works, but depends on the cheated helper lemmas

### In Progress: assign_target_preserves_immutables

The proof for `assign_target_preserves_immutables` is nearly complete. All cases are proven except the **assign_targets cons case** which has a circular dependency issue.

**Proven cases:**
1. **ScopedVar**: `set_scopes` preserves globals, so immutables unchanged ✓
2. **TopLevelVar (src_id_opt ≠ NONE)**: `ADELKEY` with different key preserves NONE lookup ✓
3. **ImmutableVar**: `|+` on immutables preserves IS_SOME for existing keys ✓
4. **TupleTargetV**: Uses assign_targets IH ✓
5. **assign_targets base case (nil)**: Trivial, state unchanged ✓

**Blocked case:**
6. **assign_targets cons case**: Needs `assign_target_preserves_globals` to show that `ALOOKUP s''.globals cx.txn.target` is SOME (where `s''` is the intermediate state after `assign_target` but before `assign_targets`)

### Circular Dependency Issue

The cons case of `assign_target_preserves_immutables` needs `assign_target_preserves_globals` to work. But both theorems are of the same structure and need to be proven together.

**Solution options:**
1. **Prove `assign_target_preserves_globals` first** - This theorem is simpler (just needs to show IS_SOME is preserved)
2. **Combine into single mutual induction** - Prove both properties simultaneously
3. **Add an additional precondition** - Require `IS_SOME (ALOOKUP st.globals cx.txn.target)` in the theorem statement (which is what we did for the main theorem)

### Next Steps

1. Prove `assign_target_preserves_globals` using same induction pattern
2. Complete `assign_target_preserves_immutables` using the globals theorem
3. The main theorem proof should then work as already developed

### Partial Proof Script for assign_target_preserves_immutables

```sml
ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >>
simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
     lift_option_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
     ignore_bind_def, set_scopes_def] >-
(* ScopedVar case *)
(simp[AllCaseEqs(), return_def, raise_def, bind_def, set_scopes_def] >>
 strip_tac >> gvs[] >> rpt gen_tac >> strip_tac >>
 PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
 Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
 Cases_on `assign_subscripts x2 (REVERSE is) ao` >> gvs[return_def, raise_def]) >-
(* TopLevelVar case *)
(... state tracking shows gbs = gbs', then case on src_id_opt ...) >-
(* ImmutableVar case *)
(... state tracking, then use FLOOKUP_UPDATE ...) >-
(* TupleTargetV case *)
(... use IH with check/assert preserving state ...) >-
(* assign_targets nil case *)
(strip_tac >> gvs[] >> rw[] >> gvs[]) >-
(* assign_targets cons case - BLOCKED on assign_target_preserves_globals *)
(...)
```
