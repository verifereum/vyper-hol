# Proof Plan: vyperArrayScript.sml

## Overview

16 cheated theorems about array operations (index, set, pop, append, elements).
All definitions are in `vyperInterpreterScript.sml`. The three array value constructors are:
- `DynArrayV tv n vs` — dynamic array (mutable, dynamic, list-backed)
- `SArrayV tv n al` — static array (mutable, not dynamic, sparse alist-backed)
- `TupleV vs` — tuple (immutable, not dynamic, list-backed)

## Helper Lemmas Needed

### H1: `ALOOKUP_insert_sarray_same`
```
∀k v al. ALOOKUP (insert_sarray k v al) k = SOME v
```
**Proof:** Induction on `al` via `insert_sarray_ind`. Base: `ALOOKUP [(k,v)] k = SOME v`. Step: case split `k = k1` / `k < k1` / else. All cases trivial with `simp`.

### H2: `ALOOKUP_insert_sarray_other`
```
∀k k' v al. k ≠ k' ⇒ ALOOKUP (insert_sarray k v al) k' = ALOOKUP al k'
```
**Proof:** Induction on `al` via `insert_sarray_ind`. Case split on `k = k1` / `k < k1` / else. For `k < k1`, the new element is prepended but `k ≠ k'` so ALOOKUP skips it. For recursive case, IH applies.

### H3: `TAKE_DROP_LUPDATE` (optional, simplifies DynArrayV proofs)
```
∀n e l. n < LENGTH l ⇒ TAKE n l ++ [e] ++ DROP (SUC n) l = LUPDATE e n l
```
**Proof:** By `Induct_on 'l'`, `Cases_on 'n'`, `simp[LUPDATE_def]`.

This enables using `oEL_LUPDATE` and `LENGTH_LUPDATE` for DynArrayV cases instead of manual APPEND reasoning.

## Proof Plans by Theorem

### Group 1: Trivial (cases + simp)

**T1. `array_elements_length`** — `LENGTH (array_elements a) = array_length a`
- Cases on `a`
- DynArrayV/TupleV: `array_elements` returns `vs`, `array_length` returns `LENGTH vs`. Trivial.
- SArrayV: `array_elements` returns `GENLIST f n`, length is `n` by `LENGTH_GENLIST`. `array_length` returns `n`.
- Tactics: `Cases_on 'a' >> simp[array_elements_def, array_length_def, LENGTH_GENLIST]`

**T2. `array_elements_after_pop`** — `pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_elements a' = FRONT (array_elements a)`
- Only DynArrayV case succeeds (SArrayV/TupleV: `pop_element` returns INR).
- `a = DynArrayV tv n vs`, `vs ≠ []`, `a' = DynArrayV tv n (FRONT vs)`.
- `array_elements a' = FRONT vs = FRONT (array_elements a)`. Direct.
- Tactics: `Cases_on 'a' >> simp[pop_element_def, array_elements_def] >> rw[] >> gvs[]`

### Group 2: Simple case analysis + integer arithmetic

**T3. `array_index_valid`** — `valid_index a i ⇔ IS_SOME (array_index a i)`
- Cases on `a`, unfold `valid_index_def`, `array_index_def`, `array_length_def`
- DynArrayV/TupleV: `IS_SOME (oEL (Num i) vs)` iff `Num i < LENGTH vs` (by `oEL_THM`). Combined with `0 ≤ i` guard, matches `valid_index`.
- SArrayV: When `0 ≤ i ∧ Num i < n`, `array_index` is `case ALOOKUP al (Num i) of NONE => SOME (default_value t) | SOME v => SOME v`, always `IS_SOME`. When out of bounds, returns `NONE`.
- Key theorems: `oEL_THM`, `NUM_OF_INT`, `INT_OF_NUM_LT`
- SArrayV case: `Cases_on 'ALOOKUP al (Num i)'` to show both branches give `SOME`.

**T4. `array_set_index_valid`** — `array_is_mutable a ∧ valid_index a i ⇔ ∃a'. array_set_index a i v = INL (ArrayV a')`
- Cases on `a`, use `EQ_IMP_TAC`
- DynArrayV: both sides reduce to `0 ≤ i ∧ Num i < LENGTH vs`. Forward: exhibit witness. Backward: extract from INL.
- SArrayV: both sides reduce to `0 ≤ i ∧ Num i < n`.
- TupleV: `array_is_mutable = F` makes LHS false; `array_set_index` always returns INR makes RHS false.

**T5. `array_pop_valid`** — `array_is_dynamic a ∧ array_length a ≠ 0 ⇔ ∃a'. pop_element (ArrayV a) = INL (ArrayV a')`
- Cases on `a`
- DynArrayV: LHS = `LENGTH vs ≠ 0` = `vs ≠ []`. RHS: `pop_element` succeeds iff `vs ≠ []`.
- SArrayV/TupleV: `array_is_dynamic = F`, both sides false.

### Group 3: Length preservation

**T6. `array_length_after_set`** — `array_set_index a i v = INL (ArrayV a') ⇒ array_length a' = array_length a`
- Cases on `a`
- DynArrayV: Via H3, `LENGTH (LUPDATE v j vs) = LENGTH vs` by `LENGTH_LUPDATE`. Or directly: `LENGTH (TAKE j vs ++ [v] ++ DROP (SUC j) vs) = j + 1 + (LENGTH vs - SUC j) = LENGTH vs`.
- SArrayV: `array_length a' = n = array_length a`. Trivial.
- TupleV: contradiction (`array_set_index` returns INR).

**T7. `array_length_after_pop`** — `pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_length a' = array_length a - 1`
- Only DynArrayV. `array_length a' = LENGTH (FRONT vs)`.
- By `LENGTH_FRONT`: `LENGTH (FRONT vs) = PRE (LENGTH vs)` when `vs ≠ []`.
- `PRE (LENGTH vs) = LENGTH vs - 1`.

**T8. `array_length_after_append`** — `append_element (ArrayV a) v = INL (ArrayV a') ⇒ array_length a' = array_length a + 1`
- Only DynArrayV. `a' = DynArrayV tv n (SNOC v' vs)` where `safe_cast tv v = SOME v'`.
- `LENGTH (SNOC v' vs) = SUC (LENGTH vs)` by `LENGTH_SNOC`.

### Group 4: Index operations (need insert_sarray helpers)

**T9. `array_index_after_set_same`** — `array_set_index a i v = INL (ArrayV a') ⇒ array_index a' i = SOME v`
- Cases on `a`
- DynArrayV: Via H3 + `oEL_LUPDATE`: `oEL j (LUPDATE v j vs) = SOME v` when `j < LENGTH vs`.
- SArrayV, `v = default_value tv`: `ALOOKUP (ADELKEY j al) j = NONE` by `ALOOKUP_ADELKEY`. So result is `SOME (default_value tv) = SOME v`. ✓
- SArrayV, `v ≠ default_value tv`: `ALOOKUP (insert_sarray j v al) j = SOME v` by **H1**. ✓
- TupleV: contradiction.

**T10. `array_index_after_set_other`** — `i ≠ j ∧ array_set_index a i v = INL (ArrayV a') ⇒ array_index a' j = array_index a j`
- Cases on `a`
- DynArrayV: Via H3 + `oEL_LUPDATE`: since `Num i ≠ Num j` (from `i ≠ j` when both `≥ 0`), `oEL (Num j) (LUPDATE v (Num i) vs) = oEL (Num j) vs`.
  - Edge: if `¬(0 ≤ j)`, both sides are NONE. Trivial.
  - If `0 ≤ i ∧ 0 ≤ j ∧ i ≠ j`: `Num i ≠ Num j` by integer injectivity.
- SArrayV: `ALOOKUP_ADELKEY` (for `v = default_value tv`) or **H2** (for `v ≠ default_value tv`).
- TupleV: contradiction.

**T11. `array_index_after_append`** — `append_element (ArrayV a) v = INL (ArrayV a') ⇒ ∃ty v'. safe_cast ty v = SOME v' ∧ array_index a' &(array_length a) = SOME v'`
- Only DynArrayV. From `append_element_def`: `safe_cast tv v = SOME v'`, `a' = DynArrayV tv n (SNOC v' vs)`.
- `array_index a' &(LENGTH vs) = oEL (Num (&(LENGTH vs))) (SNOC v' vs) = oEL (LENGTH vs) (SNOC v' vs)`.
- By `oEL_EQ_EL`: need `LENGTH vs < LENGTH (SNOC v' vs)` (= `SUC (LENGTH vs)`) ✓.
- `EL (LENGTH vs) (SNOC v' vs) = v'` by `EL_LENGTH_SNOC`. So result is `SOME v'`.
- Witnesses: `ty := tv`, `v' := ` the safe_cast result.

**T12. `array_index_after_pop`** (FIXED) — `valid_index a' i ∧ pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_index a i = array_index a' i`
- Only DynArrayV. `a = DynArrayV tv n vs`, `vs ≠ []`, `a' = DynArrayV tv n (FRONT vs)`.
- `valid_index a' i` gives `0 ≤ i ∧ Num i < LENGTH (FRONT vs)` = `Num i < PRE (LENGTH vs)`.
- Since `Num i < PRE (LENGTH vs) < LENGTH vs`, both `oEL (Num i) vs` and `oEL (Num i) (FRONT vs)` are defined.
- By `oEL_EQ_EL` on both sides: need `EL (Num i) vs = EL (Num i) (FRONT vs)`.
- By `EL_FRONT`: `n < LENGTH (FRONT l) ∧ ¬NULL l ⇒ EL n (FRONT l) = EL n l`. ✓
- Tactics sketch:
  ```
  Cases_on 'a' >> simp[pop_element_def] >> rw[] >> gvs[]
  >> simp[array_index_def, array_length_def]
  >> rw[oEL_THM] >> gvs[LENGTH_FRONT]
  >> irule EL_FRONT >> simp[LENGTH_FRONT]
  ```

**T13. `array_index_after_append_other`** (FIXED) — `valid_index a i ∧ append_element (ArrayV a) v = INL (ArrayV a') ⇒ array_index a' i = array_index a i`
- Only DynArrayV. `a = DynArrayV tv n vs`, `a' = DynArrayV tv n (SNOC v' vs)` where `safe_cast tv v = SOME v'`.
- `valid_index a i` gives `0 ≤ i ∧ Num i < LENGTH vs`.
- `array_index a' i = oEL (Num i) (SNOC v' vs)`.
- `array_index a i = oEL (Num i) vs`.
- By `oEL_EQ_EL` on both: `Num i < LENGTH (SNOC v' vs)` ✓ (since `LENGTH vs < SUC (LENGTH vs)`).
- `EL (Num i) (SNOC v' vs) = EL (Num i) vs` by `EL_SNOC` (since `Num i < LENGTH vs`). ✓
- Tactics sketch:
  ```
  Cases_on 'a' >> simp[append_element_def] >> rw[]
  >> gvs[AllCaseEqs()]
  >> simp[array_index_def, array_length_def]
  >> rw[oEL_THM, LENGTH_SNOC]
  >> irule EL_SNOC >> simp[]
  ```

### Group 5: Elements structural (medium difficulty)

**T14. `array_elements_index`** — `valid_index a i ⇒ (EL (Num i) (array_elements a) = v ⇔ array_index a i = SOME v)`
- Cases on `a`
- DynArrayV/TupleV: `EL (Num i) vs = v ⇔ oEL (Num i) vs = SOME v`. By `oEL_EQ_EL` with `Num i < LENGTH vs` from valid_index: reduces to `EL (Num i) vs = v ⇔ v = EL (Num i) vs`. Trivial (eq symmetry).
- SArrayV: `EL (Num i) (GENLIST f n) = f (Num i)` by `EL_GENLIST` (with `Num i < n`). And `array_index` gives `SOME (f (Num i))`. So `f (Num i) = v ⇔ SOME (f (Num i)) = SOME v`. Trivial.

**T15. `array_elements_after_append`** (FIXED) — `append_element (ArrayV a) v = INL (ArrayV a') ⇒ ∃ty v'. safe_cast ty v = SOME v' ∧ array_elements a' = array_elements a ++ [v']`
- Only DynArrayV. `a = DynArrayV tv n vs`, `safe_cast tv v = SOME v'`, `a' = DynArrayV tv n (SNOC v' vs)`.
- `array_elements a' = SNOC v' vs = vs ++ [v']` by `SNOC_APPEND`.
- `array_elements a = vs`.
- Witnesses: `ty := tv`, `v' :=` the safe_cast result.
- Tactics sketch:
  ```
  Cases_on 'a' >> simp[append_element_def] >> rw[]
  >> gvs[AllCaseEqs()]
  >> simp[array_elements_def, SNOC_APPEND]
  >> qexists_tac 'tv' >> simp[]
  ```

### Group 6: Elements after mutation (hardest)

**T16. `array_elements_after_set`** — `array_set_index a i v = INL (ArrayV a') ⇒ array_elements a' = TAKE (Num i) (array_elements a) ++ [v] ++ DROP (SUC (Num i)) (array_elements a)`
- DynArrayV: Direct. `array_elements a' = TAKE j vs ++ [v] ++ DROP (SUC j) vs` and `array_elements a = vs`. Identical.
- SArrayV: Need to show GENLIST equality element-wise. Strategy:
  1. Both sides have length `n`. LHS: `LENGTH (GENLIST f' n) = n`. RHS: `LENGTH (TAKE j (GENLIST f n) ++ [v] ++ DROP (SUC j) (GENLIST f n))` = `j + 1 + (n - SUC j) = n`.
  2. Show `EL k` agrees for all `k < n` using `LIST_EQ_REWRITE`.
  3. For `k < j`: LHS = `f' k`, RHS = `EL k (TAKE j (GENLIST f n)) = f k`. Need `f' k = f k`, i.e. ALOOKUP unchanged at `k ≠ j`. By H2 / `ALOOKUP_ADELKEY`.
  4. For `k = j`: LHS = `f' j = v` (by H1 / `ALOOKUP_ADELKEY`). RHS = `v` (middle element).
  5. For `k > j`: LHS = `f' k = f k` (by H2 / `ALOOKUP_ADELKEY`). RHS = `EL (k - SUC j) (DROP (SUC j) (GENLIST f n)) = EL k (GENLIST f n) = f k`.
  - Consider extracting the SArrayV case as a separate helper lemma due to complexity.
  - Key theorems: `LIST_EQ_REWRITE`, `EL_GENLIST`, `EL_APPEND1/2`, `EL_TAKE`, `EL_DROP`, `LENGTH_GENLIST`, `LENGTH_TAKE`, `LENGTH_DROP`, `ALOOKUP_ADELKEY`, H1, H2.
- TupleV: contradiction.

## Dependency Order

Prove in this order:
1. **H1, H2** (insert_sarray helpers) — needed by T9, T10, T16
2. **H3** (optional TAKE_DROP_LUPDATE) — simplifies T6, T9, T10
3. **T1** (array_elements_length) — standalone, trivial
4. **T2** (array_elements_after_pop) — standalone, trivial
5. **T3** (array_index_valid) — standalone
6. **T4** (array_set_index_valid) — standalone
7. **T5** (array_pop_valid) — standalone
8. **T6** (array_length_after_set) — uses H3 optionally
9. **T7** (array_length_after_pop) — standalone
10. **T8** (array_length_after_append) — standalone
11. **T9** (array_index_after_set_same) — uses H1
12. **T10** (array_index_after_set_other) — uses H2
13. **T11** (array_index_after_append) — standalone
14. **T12** (array_index_after_pop) — standalone (FIXED)
15. **T13** (array_index_after_append_other) — standalone (FIXED)
16. **T14** (array_elements_index) — standalone
17. **T15** (array_elements_after_append) — standalone (FIXED)
18. **T16** (array_elements_after_set) — uses H1, H2, hardest

## Estimated Complexity

- **Trivial** (1-3 tactics): T1, T2, T7, T8
- **Easy** (5-10 tactics): T3, T4, T5, T6, T12, T13, T15, H1, H2
- **Medium** (10-20 tactics): T9, T10, T11, T14, H3
- **Hard** (20-40 tactics): T16 (SArrayV case needs element-wise reasoning)
