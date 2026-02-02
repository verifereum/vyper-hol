# Plan: Update semprop/ and hoare/ for evaluation_state Changes

## Progress Summary - CHEATS REMAINING

### All Phases Complete ✓

- **Phase 1**: Understanding the new model ✓
- **Phase 2**: vyperLookupScript.sml ✓ (builds successfully)
- **Phase 3**: vyperScopePreservationLemmasScript.sml ✓ (builds successfully)
- **Phase 4**: vyperAssignTargetLemmasScript.sml ✓ (builds successfully)
- **Phase 5**: vyperScopePreservingExprScript.sml ✓ (builds successfully)
- **Phase 6**: vyperEvalExprPreservesScopesDomScript.sml ✓ (builds successfully)
- **Phase 7**: hoare/vyperHoareScript.sml ✓ (builds with cheats)
- **Phase 7**: hoare/vyperAssignTargetSpecScript.sml ✓ (builds, NO cheats)
- **Phase 8**: hoare/examples/ ✓ (builds successfully)
- **Phase 9**: Remove cheats in vyperAssignTargetSpecScript.sml ✓ (COMPLETED)
- **Phase 10**: Helper Lemmas for ImmutableVar Cases ✓ (COMPLETED)
- **Phase 11**: Remove cheats in vyperHoareScript.sml

### Build Status

**semprop/**: ✅ Builds with NO cheats
**hoare/**: ✅ Builds with 2 cheats (vyperHoareScript.sml only)
**hoare/examples/**: ✅ Builds (1 cheat in example2)

### Cheats Remaining

| File | Line | Reason |
|------|------|--------|
| vyperHoareScript.sml:291 | expr_spec_toplevelname | Major rewrite needed - TopLevelName now reads from EVM storage via lookup_global |
| vyperHoareScript.sml:304 | expr_spec_subscript | evaluate_subscript signature changed (no type_env, new return type) |
| vyperHoareExample2Script.sml:78 | Example proof | Pre-existing cheat |

### Key Changes Made

1. **eval_expr_Name_preserves_state**: Updated for `get_address_immutables` + `get_source_immutables` API
2. **eval_base_target_NameTarget_preserves_state**: Updated for new immutables access pattern
3. **expr_spec_toplevelname**: Cheated - needs major rewrite for storage-based TopLevelName access
4. **expr_spec_subscript**: Cheated - evaluate_subscript signature changed

### Phase 10 Additions (ImmutableVar Helper Lemmas)

**Added to semprop/vyperLookupScript.sml:**
- `lookup_immutable_after_set_immutable`: After `set_immutable`, `lookup_immutable` returns the new value

**Added to semprop/vyperAssignTargetLemmasScript.sml:**
- `assign_target_immutable_replace_gives_lookup`: For ImmutableVar Replace, `lookup_immutable` returns the new value
- `assign_target_immutable_update_gives_lookup`: For ImmutableVar Update, `lookup_immutable` returns the computed value

**Fixed in hoare/vyperAssignTargetSpecScript.sml:**
- `assign_target_spec_lookup`: ImmutableVar case now proven (was cheated)
- `assign_target_spec_update`: ImmutableVar case now proven (was cheated)

---

## Summary of Change

The `evaluation_state` record has been modified:
- **Removed**: `globals` field (type: `(address, module_globals_bundle) alist`)
- **Added**: `tStorage` field (type: `transient_storage`)

The new `evaluation_state` definition (from `semantics/vyperInterpreterScript.sml:1451-1458`):
```sml
evaluation_state = <|
  immutables: (address, module_immutables) alist
; logs: log list
; scopes: scope list
; accounts: evm_accounts
; tStorage: transient_storage
|>
```

---

## Phase 1 Findings: Understanding the New Model

### Key Architecture Change

The old `globals` field has been replaced with a more realistic EVM-based storage model:

1. **Storage Variables (mutables)**: Now stored in `accounts.storage` (EVM storage slots)
2. **Transient Storage**: Now stored in `tStorage` (EIP-1153)
3. **Immutables**: Now stored in `st.immutables` field (per-address, per-source-id)

### New Accessor Functions

#### For Immutables (in evaluation_state.immutables)

```sml
(* Get immutables for current address *)
get_address_immutables cx st =
  lift_option (ALOOKUP st.immutables cx.txn.target) "get_address_immutables" st

(* Get immutables for a specific source module *)
get_immutables cx src_id_opt = do
  imms <- get_address_immutables cx;
  return (get_source_immutables src_id_opt imms)
od

(* Set immutables for a source module *)
set_immutable cx src_id_opt n v = do
  imms <- get_address_immutables cx;
  let imm = get_source_immutables src_id_opt imms in
  set_address_immutables cx $ set_source_immutables src_id_opt (imm |+ (n, v)) imms
od
```

#### For Storage Variables (in accounts.storage)

```sml
(* Get storage backend - either accounts.storage or tStorage *)
get_storage_backend cx is_transient =
  if is_transient then
    do tStore <- get_transient_storage;
       return $ lookup_transient_storage cx.txn.target tStore od
  else
    do accts <- get_accounts;
       return $ (lookup_account cx.txn.target accts).storage od

(* Read from storage slot *)
read_storage_slot cx is_transient slot tv = do
  storage <- get_storage_backend cx is_transient;
  lift_option (decode_value storage (w2n slot) tv) "read_storage_slot decode"
od

(* Write to storage slot *)
write_storage_slot cx is_transient slot tv v = do
  storage <- get_storage_backend cx is_transient;
  writes <- lift_option (encode_value tv v) "write_storage_slot encode";
  set_storage_backend cx is_transient (apply_writes writes storage)
od

(* High-level lookup - determines slot from layout *)
lookup_global cx src_id_opt n = do
  ts <- lift_option (get_module_code cx src_id_opt) ...;
  case find_var_decl_by_num n ts of
  | StorageVarDecl is_transient typ => do
      var_slot <- lookup_var_slot_from_layout cx is_transient n;
      v <- read_storage_slot cx is_transient (n2w var_slot) tv;
      return (Value v) od
  | HashMapVarDecl is_transient kt vt =>
      return (HashMapRef is_transient (n2w var_slot) kt vt)
od

(* High-level set - determines slot from layout *)
set_global cx src_id_opt n v = do
  ts <- lift_option (get_module_code cx src_id_opt) ...;
  case find_var_decl_by_num n ts of
  | StorageVarDecl is_transient typ =>
      write_storage_slot cx is_transient (n2w var_slot) tv v
  | HashMapVarDecl _ _ _ =>
      raise "cannot set hashmap directly"
od
```

### Name Expression Evaluation (eval_expr cx (Name id))

```sml
eval_expr cx (Name id) = do
  env <- get_scopes;
  imms <- get_immutables cx NONE;  (* Uses st.immutables, not st.globals *)
  n <<- string_to_num id;
  v <- lift_sum $ exactly_one_option
         (lookup_scopes n env) (FLOOKUP imms n);
  return $ Value v
od
```

**Key insight**: Name lookup now uses `st.immutables` (via `get_immutables`) instead of the old `st.globals`.

### NameTarget Evaluation (eval_base_target cx (NameTarget id))

```sml
eval_base_target cx (NameTarget id) = do
  sc <- get_scopes;
  n <<- string_to_num id;
  svo <<- if IS_SOME (lookup_scopes n sc) then SOME (ScopedVar id) else NONE;
  ivo <- if cx.txn.is_creation
         then do imms <- get_immutables cx NONE;
                 return $ immutable_target imms id n od
         else return NONE;
  v <- lift_sum $ exactly_one_option svo ivo;
  return $ (v, [])
od
```

### assign_target Changes

```sml
(* ScopedVar - unchanged, uses scopes *)
assign_target cx (BaseTargetV (ScopedVar id) is) ao = do
  sc <- get_scopes;
  (pre, env, a, rest) <- lift_option (find_containing_scope ni sc) ...;
  a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
  set_scopes $ pre ++ env |+ (ni, a') :: rest;
  return $ Value a
od

(* TopLevelVar - now uses read_storage_slot/write_storage_slot *)
assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao = do
  tv <- lookup_global cx src_id_opt ni;
  case tv of
  | Value v => do
      v' <- lift_sum $ assign_subscripts v (REVERSE is) ao;
      set_global cx src_id_opt ni v';  (* writes to accounts.storage *)
      return tv od
  | HashMapRef is_transient base_slot kt vt => do
      (* computes slot and uses read_storage_slot/write_storage_slot *)
      ... od
od

(* ImmutableVar - now uses st.immutables *)
assign_target cx (BaseTargetV (ImmutableVar id) is) ao = do
  imms <- get_immutables cx NONE;  (* reads from st.immutables *)
  a <- lift_option (FLOOKUP imms ni) ...;
  a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
  set_immutable cx NONE ni a';     (* writes to st.immutables *)
  return $ Value a
od
```

### Implications for semprop/ and hoare/

#### 1. `valid_lookups` Definition Must Change

**Old concept**: Ensured no ambiguity between scoped vars and `st.globals` immutables
**New concept**: Must ensure no ambiguity between scoped vars and `st.immutables`

**New definition should be:**
```sml
valid_lookups cx st ⇔
  ∃imms. ALOOKUP st.immutables cx.txn.target = SOME imms ∧
         ∀n. var_in_scope st n ⇒
             FLOOKUP (get_source_immutables NONE imms) (string_to_num n) = NONE
```

#### 2. `lookup_immutable` Definition Must Change

**Old**: Used `ALOOKUP st.globals cx.txn.target` then `FLOOKUP gbs.immutables`
**New**: Use `ALOOKUP st.immutables cx.txn.target` then `FLOOKUP (get_source_immutables NONE imms)`

```sml
lookup_immutable cx st n =
  case ALOOKUP st.immutables cx.txn.target of
  | SOME imms => FLOOKUP (get_source_immutables NONE imms) (string_to_num n)
  | NONE => NONE
```

#### 3. Scope Preservation Lemmas Need Simplification

**Removed functions** (no longer exist):
- `get_current_globals` - REMOVED
- `set_current_globals` - REMOVED

**New functions to add lemmas for**:
- `get_address_immutables_scopes` - reads st.immutables, preserves scopes
- `set_address_immutables_scopes` - writes st.immutables, preserves scopes
- `get_immutables_scopes` - uses get_address_immutables
- `set_immutable_scopes` - uses set_address_immutables
- `lookup_global_scopes` - reads accounts.storage, preserves scopes
- `set_global_scopes` - writes accounts.storage, preserves scopes

#### 4. Assign Target Preservation Theorems

**Old**: Tracked `st.globals` preservation
**New**: Must track:
- `st.immutables` domain preservation (for ImmutableVar case)
- `st.accounts` changes (for TopLevelVar case) - but this is outside scope for name lookups

**Key simplification**: Storage variables don't affect name lookups (they use different namespace via TopLevelName, not Name). Only immutables affect Name lookups.

#### 5. State Preservation Theorems

**Old proofs** referenced `ALOOKUP st.globals cx.txn.target`
**New proofs** should reference `ALOOKUP st.immutables cx.txn.target`

---

## Impact Analysis

### Files Affected

#### semprop/ (6 files)

1. **vyperLookupScript.sml** (446 lines) - HIGH IMPACT
   - `lookup_immutable_def` uses `st.globals`
   - `valid_lookups_def` uses `st.globals`
   - `globals_preserved_after_update` theorem references `st.globals`
   - Many theorems about lookup behavior depend on globals

2. **vyperScopePreservationLemmasScript.sml** (321 lines) - MEDIUM IMPACT
   - `get_current_globals_scopes` - references globals in proof
   - `set_current_globals_scopes` - references globals
   - `get_immutables_scopes` - uses ALOOKUP st.globals
   - `lookup_global_scopes` - uses ALOOKUP st.globals
   - `set_global_scopes` - uses ALOOKUP st.globals
   - `set_immutable_scopes` - uses ALOOKUP st.globals

3. **vyperEvalExprPreservesScopesDomScript.sml** (420 lines) - MEDIUM IMPACT
   - `case_NameTarget_dom` - uses ALOOKUP st.globals
   - Proofs that reference globals for is_creation case

4. **vyperAssignTargetLemmasScript.sml** (236 lines) - HIGH IMPACT
   - Multiple theorems about preserving globals/immutables domain
   - `assign_target_preserves_globals_and_immutables_dom` - core theorem
   - All references to `st.globals` and `st'.globals`

5. **vyperEvalPreservesScopesScript.sml** (659 lines) - LOW IMPACT
   - May have indirect dependencies through other lemmas

6. **vyperScopePreservingExprScript.sml** (424 lines) - LOW IMPACT
   - Focuses on scopes, minimal globals references

#### hoare/ (5 files)

1. **vyperHoareScript.sml** (740 lines) - MEDIUM IMPACT
   - `eval_expr_Name_preserves_state` - uses ALOOKUP st.globals
   - `eval_base_target_NameTarget_preserves_state` - uses ALOOKUP st.globals
   - Theorem proofs that reference globals for creation case

2. **vyperAssignTargetSpecScript.sml** (412 lines) - HIGH IMPACT
   - `assign_target_spec_preserves_name_targets` - uses globals extensively
   - `assign_target_spec_lookup` - uses globals
   - `assign_target_spec_update` - uses globals
   - `assign_target_spec_preserves_valid_lookups` - uses globals

3. **hoare/examples/*.sml** (3 files) - LOW IMPACT
   - May need minor updates if valid_lookups changes

---

## Detailed Update Plan

### Phase 1: Understand the New Model ✓ COMPLETED

See "Phase 1 Findings" section above for detailed analysis.

### Phase 2: Update Core Lookup Definitions (semprop/vyperLookupScript.sml)

**Task 2.1**: Update `lookup_immutable_def`
```sml
(* OLD *)
lookup_immutable cx st n =
  case ALOOKUP st.globals cx.txn.target of
  | SOME gbs => FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n)
  | NONE => NONE

(* NEW *)
lookup_immutable cx st n =
  case ALOOKUP st.immutables cx.txn.target of
  | SOME imms => FLOOKUP (get_source_immutables NONE imms) (string_to_num n)
  | NONE => NONE
```

**Task 2.2**: Update `valid_lookups_def`
```sml
(* OLD *)
valid_lookups cx st ⇔
  ∃gbs. ALOOKUP st.globals cx.txn.target = SOME gbs ∧
        ∀n. var_in_scope st n ⇒ 
            FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n) = NONE

(* NEW *)
valid_lookups cx st ⇔
  ∃imms. ALOOKUP st.immutables cx.txn.target = SOME imms ∧
         ∀n. var_in_scope st n ⇒ 
             FLOOKUP (get_source_immutables NONE imms) (string_to_num n) = NONE
```

**Task 2.3**: Rename `globals_preserved_after_update` to `immutables_preserved_after_update`
```sml
(* OLD *)
globals_preserved_after_update:
  ∀st n v. (update_scoped_var st n v).globals = st.globals

(* NEW *)
immutables_preserved_after_update:
  ∀st n v. (update_scoped_var st n v).immutables = st.immutables
```

**Task 2.4**: Update all proofs that reference `st.globals` → `st.immutables`

| Theorem | Change Required |
|---------|-----------------|
| `lookup_scopes_to_lookup_name` | Replace `st.globals` with `st.immutables`, `get_module_globals NONE gbs` with `get_source_immutables NONE imms` |
| `var_in_scope_implies_name_target` | Same pattern |
| `lookup_name_target_implies_var_in_scope` | Same pattern |
| `lookup_immutable_implies_lookup_name` | Same pattern |
| `lookup_name_preserved_after_update` | Use `immutables_preserved_after_update` |
| `valid_lookups_preserved_after_update` | Same pattern |

### Phase 3: Update Scope Preservation Lemmas (semprop/vyperScopePreservationLemmasScript.sml)

**Task 3.1**: Remove obsolete lemmas
- DELETE `get_current_globals_scopes` - function no longer exists
- DELETE `set_current_globals_scopes` - function no longer exists

**Task 3.2**: Update existing lemmas for new function signatures

```sml
(* OLD get_immutables_scopes - referenced get_current_globals *)
(* NEW get_immutables_scopes - uses get_address_immutables *)
get_immutables_scopes:
  ∀cx st res st'. get_immutables cx src st = (res, st') ⇒ st'.scopes = st.scopes
Proof
  rw[get_immutables_def, bind_def, return_def, 
     get_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

(* OLD lookup_global_scopes - referenced get_current_globals *)
(* NEW lookup_global_scopes - uses get_storage_backend/read_storage_slot *)
lookup_global_scopes:
  ∀cx src n st res st'. lookup_global cx src n st = (res, st') ⇒ st'.scopes = st.scopes
Proof
  (* Proof follows from read_storage_slot preserving scopes *)
QED

(* OLD set_global_scopes - referenced set_current_globals *)
(* NEW set_global_scopes - uses write_storage_slot *)
set_global_scopes:
  ∀cx src n v st res st'. set_global cx src n v st = (res, st') ⇒ st'.scopes = st.scopes
Proof
  (* Proof follows from write_storage_slot preserving scopes *)
QED

(* OLD set_immutable_scopes - referenced set_current_globals *)
(* NEW set_immutable_scopes - uses set_address_immutables *)
set_immutable_scopes:
  ∀cx src n v st res st'. set_immutable cx src n v st = (res, st') ⇒ st'.scopes = st.scopes
Proof
  rw[set_immutable_def, bind_def, return_def,
     get_address_immutables_def, set_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[raise_def, return_def]
QED
```

**Task 3.3**: Add new helper lemmas for storage operations

```sml
(* NEW: Storage backend operations preserve scopes *)
get_storage_backend_scopes:
  ∀cx is_trans st res st'. get_storage_backend cx is_trans st = (res, st') ⇒ 
    st'.scopes = st.scopes

set_storage_backend_scopes:
  ∀cx is_trans storage st res st'. set_storage_backend cx is_trans storage st = (res, st') ⇒ 
    st'.scopes = st.scopes

read_storage_slot_scopes:
  ∀cx is_trans slot tv st res st'. read_storage_slot cx is_trans slot tv st = (res, st') ⇒ 
    st'.scopes = st.scopes

write_storage_slot_scopes:
  ∀cx is_trans slot tv v st res st'. write_storage_slot cx is_trans slot tv v st = (res, st') ⇒ 
    st'.scopes = st.scopes

get_address_immutables_scopes:
  ∀cx st res st'. get_address_immutables cx st = (res, st') ⇒ st'.scopes = st.scopes

set_address_immutables_scopes:
  ∀cx imms st res st'. set_address_immutables cx imms st = (res, st') ⇒ st'.scopes = st.scopes
```

**Task 3.4**: Verify `assign_target_preserves_scopes_dom` still holds
- ScopedVar case: unchanged (uses set_scopes)
- TopLevelVar case: now uses `write_storage_slot` which preserves scopes
- ImmutableVar case: now uses `set_address_immutables` which preserves scopes
- Proofs should be simpler as storage ops clearly preserve scopes

### Phase 4: Update Assign Target Lemmas (semprop/vyperAssignTargetLemmasScript.sml)

**Task 4.1**: Simplify theorem scope

**Key insight**: The old theorems tracked `globals` domain to ensure `valid_lookups` was preserved.
Now we need to track `immutables` domain instead.

**What matters for `valid_lookups`**:
- `st.immutables` domain (keys in the per-address immutables alist)
- Specifically: `FLOOKUP (get_source_immutables NONE imms) n`

**What doesn't matter**:
- `accounts.storage` - used for TopLevelName, not Name lookups
- `tStorage` - used for transient storage, not Name lookups

**Task 4.2**: Rename and simplify the main theorem

```sml
(* OLD: assign_target_preserves_globals_and_immutables_dom *)
(* NEW: assign_target_preserves_immutables_dom *)

(* The theorem is simpler now because:
   - ScopedVar: only touches scopes, not immutables
   - TopLevelVar: only touches accounts.storage, not immutables
   - ImmutableVar: touches st.immutables - need to track this *)

assign_target_preserves_immutables_dom:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     (* Immutables domain preserved (may add keys but not remove) *)
     (∀addr. IS_SOME (ALOOKUP st.immutables addr) ⇒ 
             IS_SOME (ALOOKUP st'.immutables addr)) ∧
     (* For current target: source immutables keys preserved *)
     (∀n imms imms'.
        ALOOKUP st.immutables cx.txn.target = SOME imms ∧
        ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
        IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) =
        IS_SOME (FLOOKUP (get_source_immutables NONE imms') n)))
```

**Task 4.3**: Update exported theorems

| Old Theorem | New Theorem | Notes |
|-------------|-------------|-------|
| `assign_target_preserves_globals_dom` | DELETE | No longer relevant |
| `assign_targets_preserves_globals_dom` | DELETE | No longer relevant |
| `assign_target_preserves_immutables_dom` | KEEP/UPDATE | Change from `globals` to `immutables` |
| `assign_targets_preserves_immutables_dom` | KEEP/UPDATE | Change from `globals` to `immutables` |

**Task 4.4**: Simplify helper lemmas
- `ALOOKUP_set_module_globals_preserves` - may no longer be needed
- The mutual induction may be simpler as TopLevelVar doesn't affect immutables

### Phase 5: Update Expression Evaluation (semprop/vyperEvalExprPreservesScopesDomScript.sml)

**Task 5.1**: Update `case_NameTarget_dom`

```sml
(* OLD: referenced ALOOKUP st.globals *)
Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]

(* NEW: reference ALOOKUP st.immutables *)
Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]
```

The proof structure should be similar, just using `get_address_immutables` instead of `get_current_globals`.

**Task 5.2**: Review other cases for globals references
- `case_NameTarget_dom` (line ~34-49): Uses immutables for is_creation case
- Most other cases don't touch globals/immutables directly
- May have cascading changes from updated lemmas in Phase 3

### Phase 6: Update Hoare Logic (hoare/vyperHoareScript.sml)

**Task 6.1**: Update state preservation theorems

```sml
(* eval_expr_Name_preserves_state *)
(* OLD: Cases_on `ALOOKUP st.globals cx.txn.target` *)
(* NEW: Cases_on `ALOOKUP st.immutables cx.txn.target` *)

(* eval_base_target_NameTarget_preserves_state *)
(* Similar change - references get_immutables which uses st.immutables *)
```

**Task 6.2**: Update specification rules

| Rule | Change Required |
|------|-----------------|
| `expr_spec_name` | No change (uses lookup_name which we update) |
| `expr_spec_scoped_var` | Uses `valid_lookups` which we update in Phase 2 |
| `expr_spec_toplevelname` | MAJOR CHANGE needed - see below |
| `target_spec_scoped_var` | Uses `valid_lookups` which we update |

**Task 6.3**: Rewrite `expr_spec_toplevelname`

```sml
(* OLD - referenced st.globals and module_globals *)
expr_spec_toplevelname:
  ∀P cx src_id_opt id gbs mg tv.
    ⟦cx⟧
      ⦃λst. P st ∧
            ALOOKUP st.globals cx.txn.target = SOME gbs ∧
            get_module_globals src_id_opt gbs = mg ∧
            FLOOKUP mg.mutables (string_to_num id) = SOME tv⦄
      (TopLevelName (src_id_opt, id)) ⇓ tv
      ⦃P⦄

(* NEW - TopLevelName now reads from accounts.storage via lookup_global *)
(* This is more complex as it involves storage slots and decoding *)
expr_spec_toplevelname:
  ∀P cx src_id_opt id.
    ⟦cx⟧
      ⦃λst. P st ∧ 
            (* Precondition: lookup_global will succeed and return tv *)
            ∃v. lookup_global_result cx src_id_opt (string_to_num id) st = SOME v ∧
                v = tv⦄
      (TopLevelName (src_id_opt, id)) ⇓ tv
      ⦃P⦄

(* Alternative: may need a helper definition for expected storage value *)
```

**Note**: The toplevelname spec is significantly more complex now because it involves:
1. Looking up the variable declaration from source code
2. Getting the storage slot from layout
3. Reading and decoding from accounts.storage

Consider whether a simpler specification is possible or if we need to expose more of the storage model.

### Phase 7: Update Assign Target Specs (hoare/vyperAssignTargetSpecScript.sml)

**Task 7.1**: Update name target preservation theorems

```sml
(* assign_target_spec_preserves_name_targets *)
(* OLD: IS_SOME (ALOOKUP st.globals cx.txn.target) *)
(* NEW: For ScopedVar targets, only scopes matter, not immutables *)
(* For ImmutableVar targets during creation, uses st.immutables *)

(* Key insight: This theorem shows that name targets are preserved.
   - ScopedVar targets: preserved via scopes domain preservation
   - ImmutableVar targets: preserved via immutables domain preservation
   - TopLevelVar targets: trivially preserved (always succeed) *)
```

**Task 7.2**: Update lookup/update theorems

```sml
(* assign_target_spec_lookup - uses valid_lookups and tracks name lookup result *)
(* Changes needed: *)
(* - Replace st.globals with st.immutables *)
(* - Replace get_module_globals with get_source_immutables *)

(* assign_target_spec_update - similar changes *)
```

**Task 7.3**: Update valid_lookups preservation

```sml
(* assign_target_spec_preserves_valid_lookups *)
(* OLD *)
valid_lookups cx st ∧ assign_target_spec cx st av ao P ⇒
assign_target_spec cx st av ao (λst'. P st' ∧ valid_lookups cx st')

(* Proof needs to show:
   1. st'.immutables has target address (preserved)
   2. No new overlaps between scopes and immutables created *)

(* Key insight: assign_target can only ADD to immutables domain (ImmutableVar case),
   never remove. And it preserves scopes domain. So valid_lookups is preserved. *)
```

**Task 7.4**: Simplify where possible

The new model may actually simplify some theorems:
- Storage operations (TopLevelVar) don't affect name lookups at all
- Only ImmutableVar and ScopedVar affect the Name namespace
- Transient storage is completely separate from name lookups

### Phase 8: Update Examples (hoare/examples/)

**Task 8.1**: Update example proofs
- May need adjustment if valid_lookups definition changed
- Most examples use scoped variables, minimal globals impact

---

## Execution Strategy

### Recommended Order

1. **First**: Understand the new model (Phase 1)
   - This determines all subsequent changes

2. **Second**: Update vyperLookupScript.sml (Phase 2)
   - Core definitions that everything depends on
   - Must be done before other files

3. **Third**: Update vyperScopePreservationLemmasScript.sml (Phase 3)
   - Basic lemmas used throughout

4. **Fourth**: Update vyperAssignTargetLemmasScript.sml (Phase 4)
   - Complex mutual induction
   - Blocks hoare/ updates

5. **Fifth**: Update vyperEvalExprPreservesScopesDomScript.sml (Phase 5)
   - Depends on scope preservation lemmas

6. **Sixth**: Update hoare/ files (Phases 6-8)
   - Depends on all semprop/ updates

### Build Verification

After each phase, run:
```bash
cd semprop && Holmake --qof
cd hoare && Holmake --qof
```

---

## Key Questions - RESOLVED

1. **Where did globals functionality move?** ✓ RESOLVED
   - Storage variables (mutables): `accounts.storage` via `read_storage_slot`/`write_storage_slot`
   - Transient storage: `tStorage` via same functions with `is_transient=T`
   - Immutables: `st.immutables` field directly

2. **How do immutables work now?** ✓ RESOLVED
   - `st.immutables : (address, module_immutables) alist`
   - `module_immutables = (num option, (num, value) fmap) alist` (per source_id)
   - Access via `get_address_immutables` → `get_source_immutables`
   - Write via `set_immutable` → `set_address_immutables`

3. **Is `valid_lookups` concept still needed?** ✓ RESOLVED - YES
   - Still needed to prevent ambiguity between scoped vars and immutables
   - Definition changes from `st.globals` to `st.immutables`
   - Same concept, different field

4. **What about module_globals (mutables)?** ✓ RESOLVED
   - No longer stored in state directly
   - Read/written via EVM storage slots in `accounts.storage`
   - Accessed via `lookup_global`/`set_global` which use storage slots

---

## Updated Risk Assessment

- **MEDIUM RISK**: vyperAssignTargetLemmasScript.sml - actually simpler now (TopLevelVar doesn't affect name lookups)
- **MEDIUM RISK**: vyperAssignTargetSpecScript.sml - simpler for ScopedVar, complex for TopLevelName
- **MEDIUM RISK**: vyperLookupScript.sml - straightforward field rename
- **LOW RISK**: vyperScopePreservingExprScript.sml - focuses on scopes, minimal changes
- **HIGH COMPLEXITY**: expr_spec_toplevelname in vyperHoareScript.sml - storage model is more complex

---

## Summary of Changes by File

### semprop/vyperLookupScript.sml
- `lookup_immutable_def`: `st.globals` → `st.immutables`, `get_module_globals` → `get_source_immutables`
- `valid_lookups_def`: Same pattern
- `globals_preserved_after_update` → `immutables_preserved_after_update`
- All proofs: Replace globals references with immutables

### semprop/vyperScopePreservationLemmasScript.sml
- DELETE: `get_current_globals_scopes`, `set_current_globals_scopes`
- UPDATE: `get_immutables_scopes`, `set_immutable_scopes`, `lookup_global_scopes`, `set_global_scopes`
- ADD: `get_storage_backend_scopes`, `read_storage_slot_scopes`, `write_storage_slot_scopes`, etc.

### semprop/vyperAssignTargetLemmasScript.sml
- SIMPLIFY: TopLevelVar case doesn't affect immutables
- RENAME: `assign_target_preserves_globals_and_immutables_dom` → `assign_target_preserves_immutables_dom`
- DELETE: `assign_target_preserves_globals_dom`, `assign_targets_preserves_globals_dom`

### semprop/vyperEvalExprPreservesScopesDomScript.sml
- `case_NameTarget_dom`: `st.globals` → `st.immutables`

### hoare/vyperHoareScript.sml
- State preservation theorems: `st.globals` → `st.immutables`
- `expr_spec_toplevelname`: Major rewrite needed for storage-based access

### hoare/vyperAssignTargetSpecScript.sml
- All globals references → immutables references
- Preservation theorems: simpler for storage operations

### hoare/examples/
- Minimal changes if any (mostly use scoped variables)

---

## Phase 9: Remove Cheats in vyperAssignTargetSpecScript.sml

### Status: IN PROGRESS

**Completed:**
- `assign_target_spec_preserves_name_targets` ✅ DONE (no cheat)
- `assign_target_spec_preserves_valid_lookups` ✅ DONE (no cheat)

**Partially Complete:**
- `assign_target_spec_lookup` - ScopedVar case proven, ImmutableVar case cheated
- `assign_target_spec_update` - Statement updated to require `valid_lookups cx st`, proof structure written but has cheats for extracting `lookup_scoped_var` from `lookup_name` and ImmutableVar case

**Remaining Issues:**
1. **ImmutableVar case** for both lookup and update - needs helper lemmas for `set_immutable`/`lookup_immutable` interaction
2. **lookup_name to lookup_scoped_var extraction** - the `lookup_name` definition evaluates through `eval_expr` which has complex case structure; need a simpler lemma to extract the scoped var value

**Next Steps:**
1. Add helper lemma in semprop/vyperLookupScript.sml:
   ```sml
   Theorem lookup_name_to_lookup_scoped_var:
     ∀cx st n v.
       valid_lookups cx st ∧
       IS_SOME (lookup_scopes (string_to_num n) st.scopes) ∧
       lookup_name cx st n = SOME v ⇒
       lookup_scoped_var st n = SOME v
   ```
2. Add helper lemmas for ImmutableVar case (see Appendix below)
3. Complete proofs

### Overview

There are 4 cheated theorems in `vyperAssignTargetSpecScript.sml`:

| Line | Theorem | Purpose |
|------|---------|---------|
| 115 | `assign_target_spec_preserves_name_targets` | Show that `lookup_name_target` is preserved after assign_target |
| 126 | `assign_target_spec_lookup` | Show that after assign, `lookup_name` returns the new value |
| 138 | `assign_target_spec_update` | Show that after aug-assign, `lookup_name` returns the computed value |
| 148 | `assign_target_spec_preserves_valid_lookups` | Show that `valid_lookups` is preserved after assign_target |

### Dependency Analysis

The theorems form a dependency chain:

```
assign_target_preserves_scopes_dom (semprop - DONE) 
assign_target_preserves_immutables_dom (semprop - DONE)
    │
    ├── assign_target_spec_preserves_name_targets
    │       └── needs: scopes domain preserved, immutables domain preserved
    │
    ├── assign_target_spec_preserves_valid_lookups  
    │       └── needs: scopes domain preserved, immutables domain preserved
    │
    ├── assign_target_spec_lookup
    │       └── needs: assign_target_scoped_var_replace, lookup_after_update
    │
    └── assign_target_spec_update
            └── needs: assign_target_scoped_var_update, lookup_after_update
```

### Key Insight: Name vs TopLevelName Distinction

The theorems deal with `lookup_name_target` and `lookup_name`, which are about the **Name** expression, NOT **TopLevelName**:

- **Name**: Looks up in scopes OR immutables (during creation)
- **TopLevelName**: Looks up in storage (new model)

Since the cheated theorems are about Name (not TopLevelName), they should be relatively straightforward because:
1. `assign_target` for `ScopedVar` only touches scopes
2. `assign_target` for `TopLevelVar` only touches storage (NOT immutables)
3. `assign_target` for `ImmutableVar` touches immutables (but only during creation)

### Theorem 1: assign_target_spec_preserves_name_targets

**Statement:**
```sml
Theorem assign_target_spec_preserves_name_targets:
  ∀P cx st av ao n.
    IS_SOME (ALOOKUP st.immutables cx.txn.target) ∧
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
```

**What we need to prove:**
- `lookup_name_target` (which calls `eval_base_target (NameTarget n)`) returns the same result before and after `assign_target`

**Key observations about `eval_base_target (NameTarget id)`:**
```sml
eval_base_target cx (NameTarget id) = do
  sc <- get_scopes;
  n <<- string_to_num id;
  svo <<- if IS_SOME (lookup_scopes n sc) then SOME (ScopedVar id) else NONE;
  ivo <- if cx.txn.is_creation
         then do imms <- get_immutables cx NONE;
                 return $ immutable_target imms id n od
         else return NONE;
  v <- lift_sum $ exactly_one_option svo ivo;
  return $ (v, [])
od
```

The result depends on:
1. `IS_SOME (lookup_scopes n sc)` - scopes domain
2. If `is_creation`: `immutable_target imms id n` - immutables domain

**Strategy:**
1. Use `assign_target_preserves_scopes_dom_lookup` to show scopes domain preserved
2. Use `assign_target_preserves_immutables_dom` to show immutables domain preserved
3. Case split on whether lookup was via scopes or immutables
4. Show that the result is preserved in both cases

**Helper lemma needed (may already exist):**
```sml
(* immutable_target is preserved when immutables domain is preserved *)
Theorem immutable_target_preserved_by_dom:
  ∀imms imms' id n.
    IS_SOME (FLOOKUP imms n) = IS_SOME (FLOOKUP imms' n) ⇒
    immutable_target imms id n = immutable_target imms' id n
```

Actually, looking at `immutable_target`:
```sml
immutable_target imms id n = 
  if IS_SOME (FLOOKUP imms n) then SOME (ImmutableVar id) else NONE
```

So preserving the domain of `imms` (at position `n`) preserves `immutable_target`.

**Proof outline:**
```sml
Proof
  simp[assign_target_spec_def, lookup_name_target_def, lookup_base_target_def] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  (* Show lookup_name_target is preserved *)
  `MAP FDOM st'.scopes = MAP FDOM st.scopes` 
    by metis_tac[assign_target_preserves_scopes_dom] >>
  `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` 
    by metis_tac[assign_target_preserves_immutables_addr_dom] >>
  (* Now case on how lookup_name_target computed its result *)
  qpat_x_assum `lookup_name_target _ _ _ = SOME _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  (* ... unfold the definition and show equivalence ... *)
QED
```

### Theorem 2: assign_target_spec_preserves_valid_lookups

**Statement:**
```sml
Theorem assign_target_spec_preserves_valid_lookups:
  ∀cx st n v.
    valid_lookups cx st ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ valid_lookups cx st')
```

**What `valid_lookups` means:**
```sml
valid_lookups cx st ⇔
  ∃imms. ALOOKUP st.immutables cx.txn.target = SOME imms ∧
         ∀n. var_in_scope st n ⇒ 
             FLOOKUP (get_source_immutables NONE imms) (string_to_num n) = NONE
```

**What we need to prove:**
1. `ALOOKUP st'.immutables cx.txn.target = SOME imms'` for some `imms'`
2. For all `n`, if `var_in_scope st' n` then `FLOOKUP (get_source_immutables NONE imms') (string_to_num n) = NONE`

**Key facts:**
- `assign_target_preserves_immutables_addr_dom`: immutables address exists in st' if in st
- `assign_target_preserves_immutables_dom`: for same address, immutables keys are preserved
- `assign_target_preserves_scopes_dom_lookup`: scopes domain preserved

**Proof outline:**
```sml
Proof
  rw[valid_lookups_def, assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  (* 1. Show immutables address still exists *)
  `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` 
    by metis_tac[assign_target_preserves_immutables_addr_dom] >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >> gvs[] >>
  qexists_tac `x` >> conj_tac >- simp[] >>
  (* 2. Show no overlap between scopes and immutables *)
  rpt strip_tac >>
  (* var_in_scope st' n' → was in scope in st (by domain preservation) *)
  `var_in_scope st n'` by 
    (fs[var_in_scope_def, lookup_scoped_var_def] >>
     metis_tac[CONJUNCT1 assign_target_preserves_scopes_dom_lookup]) >>
  (* Therefore FLOOKUP imms (string_to_num n') = NONE *)
  first_x_assum drule >> strip_tac >>
  (* Show FLOOKUP imms' (string_to_num n') = NONE by domain preservation *)
  drule assign_target_preserves_immutables_dom >>
  disch_then (qspecl_then [`string_to_num n'`, `imms`, `x`] mp_tac) >>
  simp[]
QED
```

### Theorem 3: assign_target_spec_lookup

**Statement:**
```sml
Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    valid_lookups cx st ∧
    lookup_name_target cx st n = SOME av ⇒
    assign_target_spec cx st av (Replace v) P ⇒
    assign_target_spec cx st av (Replace v) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
```

**This theorem is more complex** because it needs to show that after assigning `v` to target `av`, looking up name `n` returns `v`.

**Key insight:** The precondition `lookup_name_target cx st n = SOME av` tells us what kind of target `av` is:
- If `av = BaseTargetV (ScopedVar n) []`: variable is in scopes
- If `av = BaseTargetV (ImmutableVar n) []`: variable is in immutables (creation only)

**Case 1: ScopedVar**
- Use existing `assign_target_spec_scoped_var_replace_elim` to get `Q (update_scoped_var st n v)`
- Use `lookup_after_update` to show `lookup_scoped_var (update_scoped_var st n v) n = SOME v`
- Use `lookup_scoped_var_implies_lookup_name` to show `lookup_name cx st' n = SOME v`

**Case 2: ImmutableVar** (only during creation)
- Need: `lookup_immutable cx st' n = SOME v` after assigning
- This requires a new lemma about immutable assignment

**Helper lemmas needed:**

```sml
(* Immutable assignment analog of lookup_after_update *)
Theorem lookup_immutable_after_set_immutable:
  ∀cx st n v st'.
    set_immutable cx NONE n v st = (INL (), st') ⇒
    lookup_immutable cx st' n = SOME v

(* Immutable lookup implies lookup_name *)
Theorem lookup_immutable_implies_lookup_name:
  (* Already exists in vyperLookupScript.sml *)
  ∀cx st n v.
    valid_lookups cx st ∧
    lookup_immutable cx st n = SOME v ⇒
    lookup_name cx st n = SOME v
```

**Actually, looking more carefully at the theorem:**
- It says `lookup_name_target cx st n = SOME av`
- If this returns `ScopedVar n`, then `av = BaseTargetV (ScopedVar n) []`
- The precondition of `assign_target_spec` already uses `av`, so the proof needs to match `av` with the lookup result

This is getting complex. Let me reconsider...

**Simpler approach:** The existing proof for `assign_target_spec_preserves_var_in_scope` (line 151) actually works and isn't cheated. Looking at its structure:

```sml
Theorem assign_target_spec_preserves_var_in_scope:
  ∀cx st n v.
    var_in_scope st n ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ var_in_scope st' n)
Proof
  rpt strip_tac >>
  simp[assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >-
  (conj_tac >- fs[assign_target_spec_def] >>
   fs[var_in_scope_def, lookup_scoped_var_def] >>
   metis_tac[CONJUNCT1 assign_target_preserves_scopes_dom_lookup]) >>
  fs[assign_target_spec_def]
QED
```

So the pattern works for `var_in_scope`. For `lookup_name`, we need to additionally track the actual value, not just domain.

**The issue:** `assign_target_spec_lookup` is about assigning TO the same variable we're looking up. We need to show the assigned value is what we read back.

For ScopedVar case, we can use:
- `assign_target_scoped_var_replace` → gives us exact post-state 
- `lookup_after_update` → shows lookup returns the value

For ImmutableVar case (during creation), we need similar lemmas.

### Theorem 4: assign_target_spec_update

Similar to Theorem 3, but for aug-assignment (Update bop v2) instead of Replace.

Uses `assign_target_scoped_var_update` instead of `assign_target_scoped_var_replace`.

---

### Implementation Plan

#### Step 1: Verify existing helper lemmas are sufficient (1-2 hours)

Check that these lemmas exist and are proven in `semprop/`:
- [x] `assign_target_preserves_scopes_dom` (vyperScopePreservationLemmasScript.sml:296)
- [x] `assign_target_preserves_scopes_dom_lookup` (vyperScopePreservationLemmasScript.sml:377)  
- [x] `assign_target_preserves_immutables_dom` (vyperAssignTargetLemmasScript.sml:188)
- [x] `assign_target_preserves_immutables_addr_dom` (vyperAssignTargetLemmasScript.sml:212)
- [x] `assign_target_scoped_var_replace` (vyperLookupScript.sml:269)
- [x] `assign_target_scoped_var_update` (vyperLookupScript.sml:286)
- [x] `lookup_after_update` (vyperLookupScript.sml:338)
- [x] `lookup_scoped_var_implies_lookup_name` (vyperLookupScript.sml:219)
- [x] `lookup_immutable_implies_lookup_name` (vyperLookupScript.sml:230)

#### Step 2: Add helper lemma for immutable_target preservation (30 min)

In `semprop/vyperLookupScript.sml` or `hoare/vyperAssignTargetSpecScript.sml`:

```sml
Theorem immutable_target_dom_eq:
  ∀imms imms' id n.
    IS_SOME (FLOOKUP imms n) = IS_SOME (FLOOKUP imms' n) ⇒
    immutable_target imms id n = immutable_target imms' id n
Proof
  rw[immutable_target_def]
QED
```

#### Step 3: Prove assign_target_spec_preserves_name_targets (2-3 hours)

**Approach:**
1. Unfold definitions
2. Case split on `assign_target` result
3. Show scopes domain preserved
4. Show immutables domain preserved  
5. Re-evaluate `lookup_name_target` in new state
6. Show result unchanged

#### Step 4: Prove assign_target_spec_preserves_valid_lookups (1-2 hours)

**Approach:**
1. Unfold `valid_lookups` and `assign_target_spec`
2. Show immutables address preserved
3. Show for any `n` in new scopes, it was in old scopes (domain preserved)
4. Therefore no overlap (by original valid_lookups)

#### Step 5: Prove assign_target_spec_lookup (3-4 hours)

**Approach:**
1. Case split on what `av` is (from `lookup_name_target` result)
2. For ScopedVar: use `assign_target_scoped_var_replace` + `lookup_after_update`
3. For ImmutableVar: need analogous lemmas for immutables
4. In both cases, use `lookup_*_implies_lookup_name` to conclude

**May need new lemmas for ImmutableVar case:**
```sml
Theorem assign_target_immutable_replace:
  ∀cx st id v.
    IS_SOME (lookup_immutable cx st id) ⇒
    ∃old_v.
      assign_target cx (BaseTargetV (ImmutableVar id) []) (Replace v) st =
      (INL (Value old_v), st')
    ∧ lookup_immutable cx st' id = SOME v

Theorem lookup_immutable_after_assign_immutable:
  ∀cx st id v st'.
    assign_target cx (BaseTargetV (ImmutableVar id) []) (Replace v) st = (INL _, st') ⇒
    lookup_immutable cx st' id = SOME v
```

#### Step 6: Prove assign_target_spec_update (2-3 hours)

Similar to Step 5, using `Update` instead of `Replace`.

---

### Estimated Timeline

| Step | Task | Estimated Time |
|------|------|----------------|
| 1 | Verify helper lemmas | 1-2 hours |
| 2 | Add immutable_target helper | 30 min |
| 3 | Prove preserves_name_targets | 2-3 hours |
| 4 | Prove preserves_valid_lookups | 1-2 hours |
| 5 | Prove spec_lookup | 3-4 hours |
| 6 | Prove spec_update | 2-3 hours |
| **Total** | | **10-14 hours** |

### Risk Assessment

- **LOW RISK**: `assign_target_spec_preserves_valid_lookups` - straightforward domain preservation
- **MEDIUM RISK**: `assign_target_spec_preserves_name_targets` - need careful case analysis
- **MEDIUM-HIGH RISK**: `assign_target_spec_lookup` and `assign_target_spec_update` - may need new helper lemmas for ImmutableVar case

### Potential Blockers

1. **ImmutableVar assignment lemmas**: May need to add new lemmas about how `set_immutable` affects `lookup_immutable`
2. **get_source_immutables complexity**: The nesting of `get_source_immutables NONE` may require careful handling
3. **eval_base_target unfolding**: The monad structure may be tedious to work with

### Success Criteria

- All 4 theorems proven without `cheat`
- `Holmake` in `hoare/` succeeds with no CHEAT warnings for these theorems
- All downstream proofs (examples) still build

---

## Appendix: Helper Lemmas Needed for ImmutableVar Case

For `assign_target_spec_lookup` and `assign_target_spec_update` to handle the ImmutableVar case, we need lemmas relating `set_immutable` to `lookup_immutable`.

### Understanding the Definitions

```sml
(* lookup_immutable - reads from st.immutables *)
lookup_immutable cx st n =
  case ALOOKUP st.immutables cx.txn.target of
  | SOME imms => FLOOKUP (get_source_immutables NONE imms) (string_to_num n)
  | NONE => NONE

(* set_immutable - writes to st.immutables *)
set_immutable cx src_id_opt n v = do
  imms <- get_address_immutables cx;   (* reads ALOOKUP st.immutables cx.txn.target *)
  let imm = get_source_immutables src_id_opt imms in
  set_address_immutables cx $ set_source_immutables src_id_opt (imm |+ (n, v)) imms
od

(* get_source_immutables - extracts per-source immutables *)
get_source_immutables src_id_opt imms =
  case ALOOKUP imms src_id_opt of
    NONE => FEMPTY
  | SOME imm => imm

(* set_source_immutables - updates per-source immutables *)
set_source_immutables src_id_opt imm imms =
  (src_id_opt, imm) :: ADELKEY src_id_opt imms

(* set_address_immutables - updates st.immutables for current address *)
set_address_immutables cx imms' st =
  return () $ st with immutables := (cx.txn.target, imms') :: ADELKEY cx.txn.target st.immutables
```

### Lemma 1: get_source_immutables_set_source_immutables

```sml
Theorem get_source_immutables_set_source_immutables:
  ∀src_id imm imms.
    get_source_immutables src_id (set_source_immutables src_id imm imms) = imm
Proof
  rw[get_source_immutables_def, set_source_immutables_def, 
     alistTheory.ALOOKUP_ADELKEY]
QED
```

### Lemma 2: get_source_immutables_set_source_immutables_other

```sml
Theorem get_source_immutables_set_source_immutables_other:
  ∀src_id1 src_id2 imm imms.
    src_id1 ≠ src_id2 ⇒
    get_source_immutables src_id1 (set_source_immutables src_id2 imm imms) =
    get_source_immutables src_id1 imms
Proof
  rw[get_source_immutables_def, set_source_immutables_def, 
     alistTheory.ALOOKUP_ADELKEY]
QED
```

### Lemma 3: ALOOKUP_after_set_address_immutables

```sml
Theorem ALOOKUP_after_set_address_immutables:
  ∀cx imms' st st'.
    set_address_immutables cx imms' st = (INL (), st') ⇒
    ALOOKUP st'.immutables cx.txn.target = SOME imms'
Proof
  rw[set_address_immutables_def, return_def] >>
  simp[alistTheory.ALOOKUP_ADELKEY]
QED
```

### Lemma 4: lookup_immutable_after_set_immutable

```sml
(* The key lemma: after set_immutable, lookup_immutable returns the set value *)
Theorem lookup_immutable_after_set_immutable:
  ∀cx st n v st'.
    set_immutable cx NONE (string_to_num n) v st = (INL (), st') ⇒
    lookup_immutable cx st' n = SOME v
Proof
  rw[set_immutable_def, lookup_immutable_def, 
     bind_def, LET_THM, get_address_immutables_def,
     set_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  simp[alistTheory.ALOOKUP_ADELKEY,
       get_source_immutables_set_source_immutables,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
```

### Lemma 5: lookup_immutable_after_set_immutable_other

```sml
(* Lookup of different variable is preserved *)
Theorem lookup_immutable_after_set_immutable_other:
  ∀cx st n1 n2 v st'.
    n1 ≠ n2 ∧
    set_immutable cx NONE (string_to_num n1) v st = (INL (), st') ⇒
    lookup_immutable cx st' n2 = lookup_immutable cx st n2
Proof
  rw[set_immutable_def, lookup_immutable_def, 
     bind_def, LET_THM, get_address_immutables_def,
     set_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  simp[alistTheory.ALOOKUP_ADELKEY,
       get_source_immutables_set_source_immutables,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  `string_to_num n1 ≠ string_to_num n2` 
    by metis_tac[vyperMiscTheory.string_to_num_inj]
  (* ... rest of proof ... *)
QED
```

### Lemma 6: assign_target_immutable_gives_lookup

```sml
(* For ImmutableVar assignment, show lookup returns the new value *)
Theorem assign_target_immutable_gives_lookup:
  ∀cx st id v res st'.
    assign_target cx (BaseTargetV (ImmutableVar id) []) (Replace v) st = (INL res, st') ⇒
    lookup_immutable cx st' id = SOME v
Proof
  rw[Once assign_target_def, bind_def, get_immutables_def,
     get_address_immutables_def, lift_option_def, 
     lift_sum_def, assign_subscripts_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  Cases_on `FLOOKUP (get_source_immutables NONE x) (string_to_num id)` >> 
  gvs[return_def, raise_def] >>
  gvs[ignore_bind_def, bind_def] >>
  irule lookup_immutable_after_set_immutable >>
  (* ... finish the proof ... *)
QED
```

### Where to Add These Lemmas

1. **Lemmas 1-2** (get_source_immutables properties): Add to `semprop/vyperLookupScript.sml`
2. **Lemma 3** (ALOOKUP_after_set_address_immutables): Add to `semprop/vyperScopePreservationLemmasScript.sml`
3. **Lemmas 4-5** (lookup_immutable after set_immutable): Add to `semprop/vyperLookupScript.sml`
4. **Lemma 6** (assign_target_immutable_gives_lookup): Add to `hoare/vyperAssignTargetSpecScript.sml` or `semprop/vyperAssignTargetLemmasScript.sml`

### Alternative: Restrict to ScopedVar Only

Looking at the theorem statements more carefully:

```sml
Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    valid_lookups cx st ∧
    lookup_name_target cx st n = SOME av ⇒
    assign_target_spec cx st av (Replace v) P ⇒
    assign_target_spec cx st av (Replace v) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
```

The precondition `lookup_name_target cx st n = SOME av` means:
- If `cx.txn.is_creation = F`: only ScopedVar is possible (ImmutableVar not checked)
- If `cx.txn.is_creation = T`: could be ScopedVar OR ImmutableVar

But wait - during creation (`is_creation = T`), can you actually **assign** to an ImmutableVar through `lookup_name_target`? Let's check `eval_base_target (NameTarget id)`:

```sml
eval_base_target cx (NameTarget id) = do
  sc <- get_scopes;
  n <<- string_to_num id;
  svo <<- if IS_SOME (lookup_scopes n sc) then SOME (ScopedVar id) else NONE;
  ivo <- if cx.txn.is_creation
         then do imms <- get_immutables cx NONE;
                 return $ immutable_target imms id n od
         else return NONE;
  v <- lift_sum $ exactly_one_option svo ivo;
  return $ (v, [])
od
```

So yes, during creation, if a variable is in immutables but not scopes, `lookup_name_target` returns `ImmutableVar`.

The theorems need to handle both cases. However, practically:
- **ScopedVar**: Most common case, already has helper lemmas
- **ImmutableVar**: Only during creation, needs new helper lemmas

If the ImmutableVar case is complex to prove, we could:
1. Add a precondition `¬cx.txn.is_creation` to simplify (but this limits generality)
2. Or prove the full version with both cases

**Recommendation**: Prove the full version to maintain generality. The helper lemmas above should make it tractable.

---

## Phase 10: Helper Lemmas for ImmutableVar Cases

### Overview

The two remaining cheated cases in `vyperAssignTargetSpecScript.sml` are:
1. **Line 267** (`assign_target_spec_lookup`): ImmutableVar Replace case
2. **Line 360** (`assign_target_spec_update`): ImmutableVar Update case

Both cases occur when:
- `cx.txn.is_creation = T` (contract creation mode)
- `lookup_scoped_var st n = NONE` (n not in scopes)
- `immutable_target (get_source_immutables NONE imms) n (string_to_num n) = SOME (ImmutableVar n)` (n is in immutables)

### Case Helper Lemma 1: assign_target_spec_lookup_immutable

**Purpose:** Directly prove the ImmutableVar case for `assign_target_spec_lookup`

**Statement:**
```sml
Theorem assign_target_spec_lookup_immutable:
  ∀cx st n v P.
    valid_lookups cx st ∧
    cx.txn.is_creation ∧
    lookup_scoped_var st n = NONE ∧
    IS_SOME (lookup_immutable cx st n) ∧
    assign_target_spec cx st (BaseTargetV (ImmutableVar n) []) (Replace v) P ⇒
    assign_target_spec cx st (BaseTargetV (ImmutableVar n) []) (Replace v)
                       (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx (BaseTargetV (ImmutableVar n) []) (Replace v) st` >>
  Cases_on `q` >> gvs[] >>
  rename1 `assign_target _ _ _ st = (INL res, st')` >>
  (* Key step: show lookup_immutable cx st' n = SOME v *)
  (* Then use lookup_immutable_implies_lookup_name *)
  cheat (* placeholder - needs assign_target_immutable_replace_gives_lookup *)
QED
```

**What this lemma needs:**
1. `assign_target_immutable_replace_gives_lookup`: After `assign_target cx (BaseTargetV (ImmutableVar n) []) (Replace v) st = (INL _, st')`, we have `lookup_immutable cx st' n = SOME v`
2. `valid_lookups_preserved_after_immutable_assign`: `valid_lookups cx st ⇒ valid_lookups cx st'`
3. `lookup_immutable_implies_lookup_name`: Already exists in vyperLookupScript.sml

### Case Helper Lemma 2: assign_target_spec_update_immutable

**Purpose:** Directly prove the ImmutableVar case for `assign_target_spec_update`

**Statement:**
```sml
Theorem assign_target_spec_update_immutable:
  ∀cx st n bop v1 v2 v P.
    valid_lookups cx st ∧
    cx.txn.is_creation ∧
    lookup_scoped_var st n = NONE ∧
    lookup_immutable cx st n = SOME v1 ∧
    evaluate_binop bop v1 v2 = INL v ∧
    assign_target_spec cx st (BaseTargetV (ImmutableVar n) []) (Update bop v2) P ⇒
    assign_target_spec cx st (BaseTargetV (ImmutableVar n) []) (Update bop v2)
                       (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx (BaseTargetV (ImmutableVar n) []) (Update bop v2) st` >>
  Cases_on `q` >> gvs[] >>
  rename1 `assign_target _ _ _ st = (INL res, st')` >>
  (* Key step: show lookup_immutable cx st' n = SOME v *)
  (* Then use lookup_immutable_implies_lookup_name *)
  cheat (* placeholder - needs assign_target_immutable_update_gives_lookup *)
QED
```

**What this lemma needs:**
1. `assign_target_immutable_update_lookup`: After `assign_target cx (BaseTargetV (ImmutableVar n) []) (Update bop v2) st = (INL _, st')` with `lookup_immutable cx st n = SOME v1` and `evaluate_binop bop v1 v2 = INL v`, we have `lookup_immutable cx st' n = SOME v`
2. `valid_lookups_preserved_after_immutable_assign`: Same as above
3. `lookup_immutable_implies_lookup_name`: Already exists

---

## Core Helper Lemmas Required

### Lemma A: lookup_immutable_after_set_immutable (NEW)

**Purpose:** After `set_immutable`, `lookup_immutable` returns the new value

**Statement:**
```sml
Theorem lookup_immutable_after_set_immutable:
  ∀cx n v st st'.
    set_immutable cx NONE (string_to_num n) v st = (INL (), st') ⇒
    lookup_immutable cx st' n = SOME v
Proof
  rw[set_immutable_def, lookup_immutable_def, 
     bind_def, LET_THM, get_address_immutables_def,
     set_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  simp[alistTheory.ALOOKUP_ADELKEY,
       get_source_immutables_def, set_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
```

**Location:** Add to `semprop/vyperLookupScript.sml`

### Lemma B: assign_target_immutable_replace_gives_lookup (NEW)

**Purpose:** For ImmutableVar Replace, `lookup_immutable` returns the new value

**Statement:**
```sml
Theorem assign_target_immutable_replace_gives_lookup:
  ∀cx st n v res st'.
    IS_SOME (lookup_immutable cx st n) ∧
    assign_target cx (BaseTargetV (ImmutableVar n) []) (Replace v) st = (INL res, st') ⇒
    lookup_immutable cx st' n = SOME v
Proof
  rw[lookup_immutable_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, LET_THM, return_def] >>
  simp[lift_sum_def, assign_subscripts_def, ignore_bind_def, bind_def] >>
  Cases_on `FLOOKUP (get_source_immutables NONE x) (string_to_num n)` >> gvs[return_def, raise_def] >>
  simp[set_immutable_def, get_address_immutables_def, lift_option_def, bind_def,
       set_address_immutables_def, return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[alistTheory.ALOOKUP_ADELKEY,
       get_source_immutables_def, set_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
```

**Location:** Add to `semprop/vyperAssignTargetLemmasScript.sml`

### Lemma C: assign_target_immutable_update_gives_lookup (NEW)

**Purpose:** For ImmutableVar Update, `lookup_immutable` returns the computed value

**Statement:**
```sml
Theorem assign_target_immutable_update_lookup:
  ∀cx st n bop v1 v2 v res st'.
    lookup_immutable cx st n = SOME v1 ∧
    evaluate_binop bop v1 v2 = INL v ∧
    assign_target cx (BaseTargetV (ImmutableVar n) []) (Update bop v2) st = (INL res, st') ⇒
    lookup_immutable cx st' n = SOME v
Proof
  rw[lookup_immutable_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, LET_THM, return_def] >>
  simp[lift_sum_def, assign_subscripts_def, ignore_bind_def, bind_def] >>
  gvs[get_source_immutables_def, AllCaseEqs()] >>
  simp[set_immutable_def, get_address_immutables_def, lift_option_def, bind_def,
       set_address_immutables_def, return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[alistTheory.ALOOKUP_ADELKEY,
       get_source_immutables_def, set_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
```

**Location:** Add to `semprop/vyperAssignTargetLemmasScript.sml`

### Lemma D: valid_lookups_preserved_after_immutable_assign (NEW)

**Purpose:** `valid_lookups` is preserved after ImmutableVar assignment

**Statement:**
```sml
Theorem valid_lookups_preserved_after_immutable_assign:
  ∀cx st n v ao res st'.
    valid_lookups cx st ∧
    assign_target cx (BaseTargetV (ImmutableVar n) []) ao st = (INL res, st') ⇒
    valid_lookups cx st'
Proof
  rw[valid_lookups_def] >>
  (* Use assign_target_preserves_immutables_addr_dom *)
  `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` by
    (irule assign_target_preserves_immutables_addr_dom >> metis_tac[]) >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >> gvs[] >>
  qexists_tac `x` >> simp[] >>
  rpt strip_tac >>
  rename1 `var_in_scope st' varname` >>
  (* var_in_scope st' varname ⇒ var_in_scope st varname (scopes preserved) *)
  `var_in_scope st varname` by
    (fs[var_in_scope_def, lookup_scoped_var_def] >>
     drule (CONJUNCT1 assign_target_preserves_scopes_dom_lookup) >>
     disch_then (qspec_then `string_to_num varname` mp_tac) >> simp[]) >>
  (* Therefore FLOOKUP imms (string_to_num varname) = NONE *)
  first_x_assum drule >> strip_tac >>
  (* By immutables domain preservation, same in st' *)
  drule assign_target_preserves_immutables_dom >>
  disch_then (qspecl_then [`string_to_num varname`, `imms`, `x`] mp_tac) >> simp[]
QED
```

**Location:** Add to `semprop/vyperAssignTargetLemmasScript.sml`

---

## Dependency Graph

```
assign_target_spec_lookup (line 267 cheat)
    │
    ├─── assign_target_spec_lookup_immutable (NEW case helper)
    │        │
    │        ├─── assign_target_immutable_replace_gives_lookup (NEW - Lemma B)
    │        │        │
    │        │        └─── (unfolds assign_target, set_immutable definitions)
    │        │
    │        ├─── valid_lookups_preserved_after_immutable_assign (NEW - Lemma D)
    │        │        │
    │        │        ├─── assign_target_preserves_immutables_addr_dom (EXISTS)
    │        │        ├─── assign_target_preserves_scopes_dom_lookup (EXISTS)
    │        │        └─── assign_target_preserves_immutables_dom (EXISTS)
    │        │
    │        └─── lookup_immutable_implies_lookup_name (EXISTS)

assign_target_spec_update (line 360 cheat)
    │
    ├─── assign_target_spec_update_immutable (NEW case helper)
    │        │
    │        ├─── assign_target_immutable_update_gives_lookup (NEW - Lemma C)
    │        │        │
    │        │        └─── (unfolds assign_target, set_immutable definitions)
    │        │
    │        ├─── valid_lookups_preserved_after_immutable_assign (NEW - Lemma D, shared)
    │        │
    │        └─── lookup_immutable_implies_lookup_name (EXISTS)
```

---

## Implementation Plan

### Step 1: Add core helper lemmas to semprop/vyperLookupScript.sml

Add the following lemmas (in order):
1. `lookup_immutable_after_set_immutable` (Lemma A)
2. `assign_target_immutable_replace_gives_lookup` (Lemma B)  
3. `assign_target_immutable_update_gives_lookup` (Lemma C)

### Step 2: Add valid_lookups preservation lemma

Add to `hoare/vyperAssignTargetSpecScript.sml`:
- `valid_lookups_preserved_after_immutable_assign` (Lemma D)

### Step 3: Add case helper lemmas

Add to `hoare/vyperAssignTargetSpecScript.sml`:
- `assign_target_spec_lookup_immutable`
- `assign_target_spec_update_immutable`

### Step 4: Complete the main theorems

Update the cheated proofs:
- `assign_target_spec_lookup` (line 267): Use `assign_target_spec_lookup_immutable`
- `assign_target_spec_update` (line 360): Use `assign_target_spec_update_immutable`

---

## Estimated Effort

| Lemma | Estimated Time | Difficulty |
|-------|----------------|------------|
| lookup_immutable_after_set_immutable | 30 min | Easy |
| assign_target_immutable_replace_gives_lookup | 1 hour | Medium |
| assign_target_immutable_update_gives_lookup | 1 hour | Medium |
| valid_lookups_preserved_after_immutable_assign | 1 hour | Medium |
| assign_target_spec_lookup_immutable | 30 min | Easy (uses above) |
| assign_target_spec_update_immutable | 30 min | Easy (uses above) |
| Complete main theorems | 30 min | Easy |
| **Total** | **~5 hours** | |

---

## Risk Assessment

- **LOW RISK**: Core helper lemmas follow similar patterns to existing lemmas
- **LOW RISK**: The `set_immutable`/`lookup_immutable` interaction is straightforward (FLOOKUP_UPDATE)
- **MEDIUM RISK**: The proofs involve unfolding several monad operations, which can be tedious
- **LOW RISK**: Existing infrastructure (`assign_target_preserves_*`) provides the domain preservation we need
