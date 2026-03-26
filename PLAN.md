# Storable Value Type Preservation Lemmas

## Goal

Prove that array mutation operations (`array_set_index`, `assign_subscripts`) preserve
`value_has_type`. These are "transfer lemmas" showing that well-typed arrays remain
well-typed after element updates.

## File

New file: `semantics/prop/vyperStorableValuePropsScript.sml`
- Ancestors: `vyperArray vyperTyping`
- Combines array operation properties with typing properties

## Lemma Inventory

### Layer 1: Sorted list helpers for insert_sarray / ADELKEY

These are needed because `value_has_type` for `SArrayV` requires `SORTED $< (MAP FST sparse)`.

1. **MEM_MAP_FST_insert_sarray**
   ```
   ∀k v al y. MEM y (MAP FST (insert_sarray k v al)) ⇔ y = k ∨ MEM y (MAP FST al)
   ```
   *Proof:* Induction on `insert_sarray_ind`, case splits on k vs k1.

2. **SORTED_insert_sarray**
   ```
   ∀k v al. SORTED $< (MAP FST al) ⇒ SORTED $< (MAP FST (insert_sarray k v al))
   ```
   *Proof:* Induction on `insert_sarray_ind`. Use `SORTED_EQ` (from sortingTheory,
   requires `transitive $<`) + `MEM_MAP_FST_insert_sarray` for the recursive case
   (k1 < k) to show all elements of the result are > k1.

3. **MEM_MAP_FST_ADELKEY**
   ```
   ∀k al y. MEM y (MAP FST (ADELKEY k al)) ⇒ MEM y (MAP FST al)
   ```
   *Proof:* Induction on `al`, case split on key equality.

4. **SORTED_ADELKEY**
   ```
   ∀k al. SORTED $< (MAP FST al) ⇒ SORTED $< (MAP FST (ADELKEY k al))
   ```
   *Proof:* Induction on `al`. Use `SORTED_EQ` + `MEM_MAP_FST_ADELKEY` for the
   recursive case to show all elements remain > head.

### Layer 2: sparse_has_type / all_have_type preservation

5. **sparse_has_type_ADELKEY**
   ```
   ∀k tv n al. sparse_has_type tv n al ⇒ sparse_has_type tv n (ADELKEY k al)
   ```
   *Proof:* Induction on `al`. When k = head key, the tail already has
   `sparse_has_type`. When k ≠ head key, reconstruct from head properties + IH on tail.

6. **sparse_has_type_insert_sarray**
   ```
   ∀k v tv n al.
     SORTED $< (MAP FST al) ∧ sparse_has_type tv n al ∧
     k < n ∧ v ≠ default_value tv ∧ value_has_type tv v ⇒
     sparse_has_type tv n (insert_sarray k v al)
   ```
   *Proof:* Induction on `insert_sarray_ind`.
   - k = k1: replace entry, tail unchanged
   - k < k1: prepend (k,v), original list becomes tail
   - k1 < k: head preserved, IH on tail (SORTED gives SORTED tail)

7. **all_have_type_TAKE_DROP**
   ```
   ∀tv vs j v.
     all_have_type tv vs ∧ value_has_type tv v ⇒
     all_have_type tv (TAKE j vs ++ [v] ++ DROP (SUC j) vs)
   ```
   *Proof:* Rewrite via `all_have_type_EVERY`, then use `EVERY_APPEND`, `EVERY_TAKE`,
   `EVERY_DROP` (or equivalent MEM-based reasoning) to decompose.

### Layer 3: Core preservation lemma

8. **array_set_index_preserves_type**
   ```
   ∀elem_tv bound a i new_val a'.
     value_has_type (ArrayTV elem_tv bound) (ArrayV a) ∧
     value_has_type elem_tv new_val ∧
     array_set_index (ArrayTV elem_tv bound) a i new_val = INL (ArrayV a') ⇒
     value_has_type (ArrayTV elem_tv bound) (ArrayV a')
   ```
   *Proof:* Cases on `bound`, then cases on `a`:
   - **DynArrayV vs**: Result is `DynArrayV (TAKE j vs ++ [new_val] ++ DROP (SUC j) vs)`.
     Length preserved (same as original). `all_have_type` by `all_have_type_TAKE_DROP`.
   - **SArrayV al**: Result is `SArrayV (if new_val = default then ADELKEY ... else insert_sarray ...)`.
     `SORTED` by `SORTED_ADELKEY` / `SORTED_insert_sarray`.
     `sparse_has_type` by `sparse_has_type_ADELKEY` / `sparse_has_type_insert_sarray`.

### Layer 4: assign_subscripts wrappers

9. **assign_subscripts_replace_preserves_type**
   ```
   ∀elem_tv bound a i new_val a'.
     value_has_type (ArrayTV elem_tv bound) (ArrayV a) ∧
     value_has_type elem_tv new_val ∧
     assign_subscripts (ArrayTV elem_tv bound) (ArrayV a)
       [IntSubscript i] (Replace new_val) = INL (ArrayV a') ⇒
     value_has_type (ArrayTV elem_tv bound) (ArrayV a')
   ```
   *Proof:* `assign_subscripts` with `Replace` reduces to `array_set_index`
   (via `assign_subscripts_array_replace`). Apply `array_set_index_preserves_type`.

10. **assign_subscripts_update_preserves_type**
    ```
    ∀elem_tv bound a i ty bop v_rhs a'.
      value_has_type (ArrayTV elem_tv bound) (ArrayV a) ∧
      (∀old_v new_v.
         array_index (ArrayTV elem_tv bound) a i = SOME old_v ∧
         evaluate_binop (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
           NoneTV bop old_v v_rhs = INL new_v ⇒
         value_has_type elem_tv new_v) ∧
      assign_subscripts (ArrayTV elem_tv bound) (ArrayV a)
        [IntSubscript i] (Update ty bop v_rhs) = INL (ArrayV a') ⇒
      value_has_type (ArrayTV elem_tv bound) (ArrayV a')
    ```
    *Proof:* Unfold `assign_subscripts` for the `[IntSubscript i]` + `Update` case.
    Extract the intermediate values (old element from `array_index`, binop result).
    The hypothesis gives `value_has_type elem_tv new_v`. Then apply
    `array_set_index_preserves_type`.

## Proof Order

1 → 2 (SORTED_insert_sarray needs MEM helper)
3 → 4 (SORTED_ADELKEY needs MEM helper)
5, 6, 7 independent of each other (but 6 uses SORTED from ancestors)
1-7 → 8 (core lemma uses all helpers)
8 → 9, 10 (wrappers use core lemma)

## Build Verification

After all proofs: `Holmake` in `semantics/prop/` — must pass with no CHEAT warnings.
