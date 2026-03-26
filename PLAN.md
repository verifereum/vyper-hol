# Plan: lookup_toplevel_name_write_hashmap

## Problem

`lookup_toplevel_name cx st mid m` may read from storage when `m` is a
`StorageVarDecl` variable (non-array).  `write_hashmap cx st href kv v`
modifies storage.  We need a condition under which the lookup is unchanged.

## Key Observations

1. **`write_hashmap`** modifies storage at Keccak-derived slots:
   `hashmap_slot_for bslot kt kv + offset` for `offset < type_slot_size tv`.

2. **`lookup_toplevel_name`** goes through `lookup_global`, which has three branches:
   - *Immutables*: reads `st.immutables` — unaffected by storage writes.
   - *HashMapVarDecl*: computes slot and returns `HashMapRef` — no storage read.
   - *StorageVarDecl*:
     - *ArrayTV*: returns `ArrayRef` — no storage read.
     - *Non-ArrayTV*: calls `read_storage_slot`, which does `decode_value` on storage.

3. Only the StorageVarDecl/non-ArrayTV case reads storage, and only on one backend.
   If that backend differs from the hashmap's, or the slot ranges are disjoint,
   `decode_value` returns the same result.

## Definitions

### `hashmap_var_slots_disjoint` (in vyperHashMapStorageScript.sml)

Per-key disjointness between a hashmap entry's slot range and a variable's slot
range.  Structurally parallel to the existing `hashmap_slots_disjoint` (which
captures key-to-key disjointness within the same hashmap).

```sml
hashmap_var_slots_disjoint bslot kt hm_tv kv var_off var_tv ⇔
  let hm_off = w2n (hashmap_slot_for bslot kt kv) in
    hm_off + type_slot_size hm_tv ≤ dimword(:256) ∧
    var_off + type_slot_size var_tv ≤ dimword(:256) ∧
    (hm_off + type_slot_size hm_tv ≤ var_off ∨
     var_off + type_slot_size var_tv ≤ hm_off)
```

### `no_hashmap_var_collision` (in vyperHashMapStorageScript.sml)

All-keys variant, analogous to `no_hashmap_collision`.
Captures the Keccak collision-freedom assumption for hashmap-vs-variable slots.

```sml
no_hashmap_var_collision bslot kt hm_tv var_off var_tv ⇔
  ∀kv. hashmap_var_slots_disjoint bslot kt hm_tv kv var_off var_tv
```

## Theorems

### Storage-level helper: `decode_value_after_hashmap_write`

In vyperHashMapStorageScript.sml (alongside existing `hashmap_read_after_write_other`):

```
hashmap_write storage base kt hm_tv kv v = SOME storage' ∧
value_has_type hm_tv v ∧
hashmap_var_slots_disjoint base kt hm_tv kv var_off var_tv ⇒
decode_value storage' var_off var_tv = decode_value storage var_off var_tv
```

Proof: Expand `hashmap_write_def`, apply `decode_value_disjoint_writes_word` with
`sz = type_slot_size hm_tv`, discharge write-offset bound via `encode_writes_bounded`.
Same proof pattern as `hashmap_read_after_write_other`.

### Main theorem: `lookup_toplevel_name_write_hashmap`

In vyperHashMapPreservationScript.sml:

```
∀cx st b bslot kt t kv v mid m.
  (∀tv var_b var_off var_tv.
     evaluate_type (get_tenv cx) t = SOME tv ∧
     storage_var_info cx mid m = SOME (var_b, var_off, var_tv) ∧
     b = var_b ⇒
     hashmap_var_slots_disjoint bslot kt tv kv var_off var_tv) ⇒
  lookup_toplevel_name cx
    (write_hashmap cx st (HashMapRef b bslot kt (Type t)) kv v) mid m =
  lookup_toplevel_name cx st mid m
```

The precondition is vacuously true when:
- Variable `m` is not a StorageVarDecl (storage_var_info returns NONE)
- The hashmap and variable are on different backends (b ≠ var_b)

Proof outline:
1. Expand `write_hashmap_def`; CASE_TAC on `evaluate_type` and `hashmap_write`.
   - NONE cases: state is unchanged, trivial.
   - SOME cases: state is `set_storage cx st b storage'`.
2. Expand `lookup_toplevel_name_def` → `lookup_global`.
3. Case-split through `lookup_global` (follow `lookup_global_scopes_fst` template):
   - *Immutables*: `set_storage` preserves immutables → same result.
   - *HashMapVarDecl*: no storage read → same result.
   - *StorageVarDecl / ArrayTV*: no storage read → same result.
   - *StorageVarDecl / non-ArrayTV*: use `read_storage_slot` preservation:
     - If `is_transient ≠ b`: `get_storage_after_set_other` → same storage.
     - If `is_transient = b`: `get_storage_after_set` + `decode_value_after_hashmap_write`
       → same `decode_value` under the disjointness precondition.

Local helpers needed:
- `get_immutables_set_storage_fst[local]`: FST of get_immutables unchanged after set_storage
- `get_immutables_set_storage_snd[local]`: SND tracks the modified state
- `read_storage_slot_set_storage_fst[local]`: FST of read_storage_slot under disjointness

### Corollary: `update_hashmap_preserves_lookup`

```
∀cx st mid_h n_h kv v mid m.
  is_leaf_hashmap cx mid_h n_h ∧
  (∀href tv var_b var_off var_tv.
     lookup_toplevel_name cx st mid_h n_h = SOME href ∧
     hashmap_ref_value_tv cx href = SOME tv ∧
     storage_var_info cx mid m = SOME (var_b, var_off, var_tv) ∧
     hashmap_ref_is_t href = var_b ⇒
     hashmap_var_slots_disjoint (hashmap_ref_bslot href) (hashmap_ref_kt href)
       tv kv var_off var_tv) ⇒
  lookup_toplevel_name cx (update_hashmap cx st mid_h n_h kv v) mid m =
  lookup_toplevel_name cx st mid m
```

Actually, this corollary is complex because it needs to extract fields from href.
It may be simpler to just use `update_hashmap_def` + `lookup_toplevel_name_write_hashmap`
directly. Defer the corollary — prove `lookup_toplevel_name_write_hashmap` first.

## File Changes

| File | Changes |
|------|---------|
| `semantics/prop/vyperHashMapStorageScript.sml` | Add `hashmap_var_slots_disjoint`, `no_hashmap_var_collision`, `decode_value_after_hashmap_write` |
| `semantics/prop/vyperHashMapPreservationScript.sml` | Add `lookup_toplevel_name_write_hashmap` |
