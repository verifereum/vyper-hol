# Plan: HashMap Preservation Theorems

## Goal
Prove preservation theorems for `write_hashmap` and `update_hashmap` (state field preservation),
and independence theorems for `read_hashmap` and `lookup_hashmap` (scopes independence).

## Architecture

**New file:** `semantics/prop/vyperHashMapPreservationScript.sml`
- Ancestors: `vyperHashMap vyperLookupStorageScopes vyperStorageBackend`

**Foundation additions to:** `semantics/prop/vyperStorageBackendScript.sml`
- `set_storage` field preservation lemmas (needed by write_hashmap proofs)

## Phase 1: Foundation — set_storage field preservation

Add to `vyperStorageBackendScript.sml`:

1. **`set_storage_scopes`**: `(set_storage cx st b s').scopes = st.scopes`
   - Proof: Cases on `b`, simp with set_storage_def

2. **`set_storage_immutables`**: `(set_storage cx st b s').immutables = st.immutables`
   - Proof: Same pattern

3. **`set_storage_logs`**: `(set_storage cx st b s').logs = st.logs`
   - Proof: Same pattern

4. **`get_storage_after_set_other`**: `b1 ≠ b2 ⇒ get_storage cx (set_storage cx st b1 s') b2 = get_storage cx st b2`
   - Proof: Cases on b1, b2, simp

## Phase 2: write_hashmap state field preservation

In `vyperHashMapPreservationScript.sml`:

5. **`write_hashmap_scopes`**: `(write_hashmap cx st href kv v).scopes = st.scopes`
   - Proof: Cases on href/vt, simp with write_hashmap_def, set_storage_scopes, AllCaseEqs

6. **`write_hashmap_immutables`**: `(write_hashmap cx st href kv v).immutables = st.immutables`
   - Proof: Same pattern with set_storage_immutables

7. **`write_hashmap_logs`**: `(write_hashmap cx st href kv v).logs = st.logs`
   - Proof: Same pattern with set_storage_logs

## Phase 3: Scope operations preserved by write_hashmap

8. **`lookup_name_write_hashmap`**: `lookup_name (write_hashmap cx st href kv v) m = lookup_name st m`
   - Proof: simp[lookup_name_def, write_hashmap_scopes]

9. **`lookup_name_typed_write_hashmap`**: `lookup_name_typed (write_hashmap cx st href kv v) m = lookup_name_typed st m`
   - Proof: simp[lookup_name_typed_def, write_hashmap_scopes]

10. **`var_in_scope_write_hashmap`**: `var_in_scope (write_hashmap cx st href kv v) m ⇔ var_in_scope st m`
    - Proof: simp[var_in_scope_def, lookup_name_write_hashmap]

## Phase 4: lookup_toplevel_name preserved by write_hashmap

11. **`lookup_toplevel_name_write_hashmap`**: `lookup_toplevel_name cx (write_hashmap cx st href kv v) mid m = lookup_toplevel_name cx st mid m`
    - Key insight: write_hashmap changes accounts/tStorage but lookup_toplevel_name
      goes through lookup_global which reads immutables (unchanged) and storage slots.
      For HashMapVarDecl variables, lookup_global doesn't read storage — just computes slot.
      For StorageVarDecl/immutable variables, lookup_global reads from storage slots.
    - However, `write_hashmap` calls `set_storage` which replaces the full storage backend,
      so StorageVarDecl reads from the same modified storage. The slots written by hashmap_write
      (keccak-based) are different from regular variable slots, but proving this requires
      collision assumptions.
    - **Approach**: Prove this via the `lookup_global_scopes_fst` pattern but for storage.
      Actually, lookup_global for HashMapVarDecl is state-independent; for StorageVarDecl
      it reads specific storage slots. We'd need `hashmap_write` to be transparent to those slots.
    - **DEFERRED**: This requires non-trivial storage-slot-disjointness conditions.
      Instead, rely on `is_leaf_hashmap_lookup_state_independent` for hashmap lookups.

## Phase 5: update_hashmap state field preservation

12. **`update_hashmap_scopes`**: `(update_hashmap cx st mid n kv v).scopes = st.scopes`
    - Proof: simp[update_hashmap_def], CASE_TAC, use write_hashmap_scopes

13. **`update_hashmap_immutables`**: `(update_hashmap cx st mid n kv v).immutables = st.immutables`
    - Proof: Same pattern

14. **`update_hashmap_logs`**: `(update_hashmap cx st mid n kv v).logs = st.logs`
    - Proof: Same pattern

## Phase 6: Scope operations preserved by update_hashmap

15. **`lookup_name_update_hashmap`**: `lookup_name (update_hashmap cx st mid n kv v) m = lookup_name st m`
    - Proof: simp[lookup_name_def, update_hashmap_scopes]

16. **`lookup_name_typed_update_hashmap`**: `lookup_name_typed (update_hashmap cx st mid n kv v) m = lookup_name_typed st m`

17. **`var_in_scope_update_hashmap`**: `var_in_scope (update_hashmap cx st mid n kv v) m ⇔ var_in_scope st m`

## Phase 7: read_hashmap/lookup_hashmap scopes independence

18. **`read_hashmap_scopes`**: `read_hashmap cx (st with scopes := s) href kv = read_hashmap cx st href kv`
    - Proof: Cases on href/vt, simp with read_hashmap_def, get_storage_def

19. **`lookup_hashmap_scopes`**: `lookup_hashmap cx (st with scopes := s) mid n kv = lookup_hashmap cx st mid n kv`
    - Proof: simp[lookup_hashmap_def, lookup_toplevel_name_scopes, read_hashmap_scopes]

## Phase 8: lookup_hashmap scope operation independence

20. **`lookup_hashmap_update_name`**: `lookup_hashmap cx (update_name st n v) mid m kv = lookup_hashmap cx st mid m kv`
    - Proof: Via lookup_toplevel_name_update_name + read_hashmap_scopes pattern

21. **`lookup_hashmap_declare_name`**: similar

22. **`lookup_hashmap_open_scope`**: similar

23. **`lookup_hashmap_tl_scopes`**: similar

## Phase 9: Cross-backend independence for read_hashmap after write_hashmap

24. **`read_hashmap_after_write_other_backend`**:
    `href1.is_t ≠ href2.is_t ⇒
     read_hashmap cx (write_hashmap cx st href1 kv1 v) href2 kv2 = read_hashmap cx st href2 kv2`
    - Proof: Different backends don't interfere, use get_storage_after_set_other

## Summary

| Phase | Count | File |
|-------|-------|------|
| 1. set_storage foundations | 4 | vyperStorageBackendScript.sml |
| 2-4. write_hashmap preservation | 6 | vyperHashMapPreservationScript.sml |
| 5-6. update_hashmap preservation | 6 | vyperHashMapPreservationScript.sml |
| 7-8. read/lookup_hashmap independence | 6 | vyperHashMapPreservationScript.sml |
| 9. cross-backend | 1 | vyperHashMapPreservationScript.sml |
| **Total** | **23** | |
