# Plan: Remove CV-Termination Cheat for vyper_to_abi

## Goal

Remove the `cheat` from line 311 of `semantics/vyperABIScript.sml`:

```sml
val vyper_to_abi_pre_def = cv_auto_trans_pre_rec
  "vyper_to_abi_pre vyper_to_abi_list_pre vyper_to_abi_same_pre vyper_to_abi_sparse_pre"
  vyper_to_abi_def cheat;  (* <-- Replace cheat with actual termination tactic *)
```

## Background

The `cv_auto_trans_pre_rec` function translates a HOL4 recursive definition into a cv-computable form. It requires a termination proof for the cv-translated recursion, which operates on `cv` values (a universal datatype for computation).

The cv-translated definition `cv_vyper_to_abi_def` has 4 mutually recursive functions:
- `cv_vyper_to_abi` (INL case)
- `cv_vyper_to_abi_list` (INR INL case)
- `cv_vyper_to_abi_same` (INR INR INL case)
- `cv_vyper_to_abi_sparse` (INR INR INR case)

## How to See the Termination Goals

To see the exact termination goals, run in HOL4:

```sml
(* Start HOL session in semantics/ directory *)
load "cv_transLib"; load "vyperMiscTheory";
open cv_transLib cv_stdTheory cv_repTheory cvTheory;

(* Load definitions up to vyper_to_abi_def *)
use "vyperABIScript.sml";  (* Will fail at cv_auto_trans_pre_rec *)

(* Or manually load dependencies and define *)
load "contractABITheory"; load "vyperASTTheory"; load "vyperTypeValueTheory";
(* ... then copy definitions from vyperABIScript.sml ... *)

(* To see the termination goals, use a failing tactic: *)
val vyper_to_abi_pre_def = cv_auto_trans_pre_rec
  "vyper_to_abi_pre vyper_to_abi_list_pre vyper_to_abi_same_pre vyper_to_abi_sparse_pre"
  vyper_to_abi_def (
    WF_REL_TAC `measure (λx. 0)` (* Will fail, showing remaining goals *)
  );
```

Alternatively, examine `cv_vyper_to_abi_def_UNION_AUX` theorem which shows the recursive structure:
```sml
fetch "vyperABI" "cv_vyper_to_abi_def_UNION_AUX";
```

## The Measure

Based on analysis, the measure should be:

```sml
WF_REL_TAC `inv_image ($< LEX $< LEX $<)
  (λx. case x of
    | INL (env, t, v) => (cv$c2n (cv_size' env), cv_size t + cv_size v, 0)
    | INR (INL (env, ts, vs)) => (cv$c2n (cv_size' env), cv_size ts + cv_size vs, 0)
    | INR (INR (INL (env, t, vs))) => (cv$c2n (cv_size' env), cv_size t + cv_size vs, 0)
    | INR (INR (INR (env, t, tv, n, sparse))) =>
        (cv$c2n (cv_size' env), cv_size t + cv_size sparse + cv$c2n n, cv$c2n n))`
```

This uses lexicographic ordering with:
1. Environment size (for StructT recursion)
2. Type + value/sparse size + counter (for most cases)
3. Counter alone (for sparse decreasing n case)

## Termination Cases to Prove

After `WF_REL_TAC` and `rw[]`, there will be ~11 subgoals:

### Case 1: List recursive call (types and values both pairs)
**Goal**: `cv_size (cv_snd ts) + cv_size (cv_snd vs) < cv_size ts + cv_size vs`
**When**: `cv_ispair ts` and `cv_ispair vs`
**Proof**:
```sml
gvs[cv_termination_simp] >> rw[cv_snd_def, cv_size_def]
```

### Case 2: Same recursive call (value list is pair)
**Goal**: `cv_size t + cv_size (cv_snd vs) < cv_size t + cv_size vs`
**When**: `cv_ispair vs`
**Proof**:
```sml
gvs[cv_termination_simp] >> rw[cv_snd_def, cv_size_def]
```

### Case 3: Sparse recursive call with cv_sub
**Goal**: `cv$c2n (cv_sub n (Num 1)) < cv$c2n n`
**When**: `cv_lt (Num 0) n` holds
**Proof**:
```sml
gvs[cv_termination_simp, cv_sub_def, c2n_def]
(* cv_termination_simp gives: n = Num (SUC k) for some k *)
(* Then cv_sub (Num (SUC k)) (Num 1) = Num k, and k < SUC k *)
```

### Case 4: Sparse ALOOKUP result call
**Goal**: `cv_size t + cv_size (cv_snd (cv_ALOOKUP sparse k)) < cv_size t + cv_size sparse + c2n n + c2n n`
**When**: `cv_ispair (cv_ALOOKUP sparse k)` holds
**Proof**: Requires helper lemma `cv_ALOOKUP_snd_size` (see below)
```sml
drule cv_ALOOKUP_snd_size >> gvs[cv_termination_simp, c2n_def]
```

### Case 5: StructT recursive call (CRITICAL - most complex)
**Goal**: `cv$c2n (cv_size' (cv_delete k env)) < cv$c2n (cv_size' env)`
**When**: `cv_ispair (cv_lookup k env)` holds (struct found in env)
**Proof**: Requires complex induction using `cv_delete_ind` (see below)

### Cases 6-11: Various cv_snd projections
Similar to Cases 1-2, involving nested `cv_snd` applications.
**Proof**: Pattern match on cv structure, apply `cv_size_def` and `cv_snd_def`.

## Helper Lemmas Needed

### Lemma 1: cv_ALOOKUP_snd_size

```sml
Theorem cv_ALOOKUP_snd_size:
  ∀sparse k. cv$c2b (cv_ispair (cv_ALOOKUP sparse k)) ⇒
    cv_size (cv_snd (cv_ALOOKUP sparse k)) < cv_size sparse
Proof
  Induct_on `sparse`
  >- rw[Once cv_ALOOKUP_def]  (* Num case: cv_ALOOKUP returns Num 0, not a pair *)
  >- (rw[Once cv_ALOOKUP_def]
      (* Pair case: either key found or recurse *)
      >- (simp[Once cv_ALOOKUP_def, cv_if_def0]
          \\ gvs[cv_termination_simp, cv_size_def])
      >- (simp[Once cv_ALOOKUP_def, cv_if_def0]
          \\ first_x_assum drule \\ simp[]))
QED
```

**Status**: Proven interactively, works.

### Lemma 2: cv_delete_decreases_size (COMPLEX)

This is the critical lemma for StructT. Need to prove that when a key is found in the environment (via `cv_lookup`), deleting it decreases `cv_size'`.

**Reference**: See `evaluate_type_def` termination proof in `vyperTypeValueScript.sml:92-137`.

The proof structure is:
```sml
(* After WF_REL_TAC and handling simple cases, for StructT: *)
\\ disj1_tac  (* Choose first component of lex order *)
\\ pop_assum mp_tac
\\ qmatch_goalsub_abbrev_tac `cv_lookup ck`
\\ `cv_ispair ck = cv$Num 0`
   by (rw[Abbr`ck`, cv_string_to_num_def]
       \\ rw[Once keccakTheory.cv_l2n_def]
       \\ rw[cv_ispair_cv_add])
\\ pop_assum mp_tac
\\ qid_spec_tac `cv_env`
\\ qid_spec_tac `ck`
\\ rpt (pop_assum kall_tac)
\\ ho_match_mp_tac cv_delete_ind
\\ rpt gen_tac \\ strip_tac
\\ simp[Once cv_lookup_def]
\\ IF_CASES_TAC \\ gs[]
\\ strip_tac \\ gs[]
\\ reverse(IF_CASES_TAC \\ gs[])
>- (Cases_on `ck` \\ gs[]
    \\ IF_CASES_TAC \\ gs[]
    \\ Cases_on `cv_env` \\ gs[]
    \\ Cases_on `0 < m` \\ gs[]
    \\ simp[Once cv_delete_def]
    \\ rw[Once cv_size'_def]
    \\ rw[Once cv_size'_def])
\\ Cases_on `cv_env` \\ gs[]
\\ Cases_on `ck` \\ gs[]
\\ strip_tac
\\ simp[Once cv_delete_def]
\\ Cases_on `g` \\ gs[]
\\ Cases_on `m=0` \\ gs[]
>- (rw[] \\ gs[]
    \\ rw[Once cv_size'_def]
    \\ rw[Once cv_size'_def, SimpR ``prim_rec$<``]
    \\ rw[])
\\ simp[Once cv_size'_def, SimpR ``prim_rec$<``]
\\ qmatch_goalsub_rename_tac `2 < p`
\\ Cases_on `p=0` \\ gs[]
\\ Cases_on `p=1` \\ gs[]
\\ Cases_on `p=2` \\ gvs[]
>- (IF_CASES_TAC \\ gs[cv_size'_cv_mk_BN])
\\ IF_CASES_TAC \\ gs[]
```

**Key theorems needed**:
- `cv_delete_ind` - induction principle for cv_delete
- `cv_size'_def` - definition of cv_size' for sptree representation
- `cv_size'_cv_mk_BN` - size of BN nodes
- `cv_size'_cv_mk_BS` - size of BS nodes
- `cv_ispair_cv_add` - cv_add of nums is not a pair

### Lemma 3: cv_map_snd_size (for StructT field values)

```sml
(* Already exists in vyperMiscTheory *)
Theorem cv_size_cv_map_snd_le:
  ∀l. cv_size (cv_map_snd l) ≤ cv_size l
```

**Status**: Already proven, available in vyperMiscTheory.

## Implementation Plan

### Step 1: Add cv_ALOOKUP_snd_size theorem

Add before the `cv_auto_trans_pre_rec` call:

```sml
Theorem cv_ALOOKUP_snd_size:
  ∀sparse k. cv$c2b (cv_ispair (cv_ALOOKUP sparse k)) ⇒
    cv_size (cv_snd (cv_ALOOKUP sparse k)) < cv_size sparse
Proof
  Induct_on `sparse`
  >- rw[Once cv_stdTheory.cv_ALOOKUP_def]
  >- (rw[Once cv_stdTheory.cv_ALOOKUP_def]
      >- (simp[Once cv_stdTheory.cv_ALOOKUP_def, cvTheory.cv_if_def0]
          \\ gvs[cv_repTheory.cv_termination_simp, cvTheory.cv_size_def])
      >- (simp[Once cv_stdTheory.cv_ALOOKUP_def, cvTheory.cv_if_def0]
          \\ first_x_assum drule \\ simp[]))
QED
```

### Step 2: Write the termination tactic

```sml
val vyper_to_abi_pre_def = cv_auto_trans_pre_rec
  "vyper_to_abi_pre vyper_to_abi_list_pre vyper_to_abi_same_pre vyper_to_abi_sparse_pre"
  vyper_to_abi_def (
  WF_REL_TAC `inv_image ($< LEX $< LEX $<)
    (λx. case x of
      | INL (env, t, v) => (cv$c2n (cv_size' env), cv_size t + cv_size v, 0)
      | INR (INL (env, ts, vs)) => (cv$c2n (cv_size' env), cv_size ts + cv_size vs, 0)
      | INR (INR (INL (env, t, vs))) => (cv$c2n (cv_size' env), cv_size t + cv_size vs, 0)
      | INR (INR (INR (env, t, tv, n, sparse))) =>
          (cv$c2n (cv_size' env), cv_size t + cv_size sparse + cv$c2n n, cv$c2n n))`
  \\ rw[]
  (* Handle simple cv_snd cases *)
  \\ TRY (gvs[cv_repTheory.cv_termination_simp, cvTheory.cv_size_def, cvTheory.cv_snd_def]
          \\ rw[cvTheory.cv_snd_def, cvTheory.cv_size_def] \\ NO_TAC)
  (* Handle cv_sub for sparse n-1 *)
  \\ TRY (gvs[cv_repTheory.cv_termination_simp, cvTheory.cv_sub_def, cvTheory.c2n_def] \\ NO_TAC)
  (* Handle ALOOKUP result *)
  \\ TRY (drule cv_ALOOKUP_snd_size
          \\ gvs[cv_repTheory.cv_termination_simp, cvTheory.c2n_def] \\ NO_TAC)
  (* Handle StructT - the complex case *)
  \\ disj1_tac
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac `cv_lookup ck`
  \\ `cv_ispair ck = cv$Num 0`
     by (rw[Abbr`ck`, cv_string_to_num_def]
         \\ rw[Once keccakTheory.cv_l2n_def]
         \\ rw[cv_stdTheory.cv_ispair_cv_add])
  \\ pop_assum mp_tac
  \\ qid_spec_tac `cv_env`
  \\ qid_spec_tac `ck`
  \\ rpt (pop_assum kall_tac)
  \\ ho_match_mp_tac cv_stdTheory.cv_delete_ind
  \\ rpt gen_tac \\ strip_tac
  \\ simp[Once cv_stdTheory.cv_lookup_def]
  \\ IF_CASES_TAC \\ gs[]
  \\ strip_tac \\ gs[]
  \\ reverse(IF_CASES_TAC \\ gs[])
  >- (Cases_on `ck` \\ gs[]
      \\ IF_CASES_TAC \\ gs[]
      \\ Cases_on `cv_env` \\ gs[]
      \\ Cases_on `0 < m` \\ gs[]
      \\ simp[Once cv_stdTheory.cv_delete_def]
      \\ rw[Once cv_stdTheory.cv_size'_def]
      \\ rw[Once cv_stdTheory.cv_size'_def])
  \\ Cases_on `cv_env` \\ gs[]
  \\ Cases_on `ck` \\ gs[]
  \\ strip_tac
  \\ simp[Once cv_stdTheory.cv_delete_def]
  \\ Cases_on `g` \\ gs[]
  \\ Cases_on `m=0` \\ gs[]
  >- (rw[] \\ gs[]
      \\ rw[Once cv_stdTheory.cv_size'_def]
      \\ rw[Once cv_stdTheory.cv_size'_def, SimpR ``prim_rec$<``]
      \\ rw[])
  \\ simp[Once cv_stdTheory.cv_size'_def, SimpR ``prim_rec$<``]
  \\ qmatch_goalsub_rename_tac `2 < p`
  \\ Cases_on `p=0` \\ gs[]
  \\ Cases_on `p=1` \\ gs[]
  \\ Cases_on `p=2` \\ gvs[]
  >- (IF_CASES_TAC \\ gs[cv_stdTheory.cv_size'_cv_mk_BN])
  \\ IF_CASES_TAC \\ gs[]
);
```

### Step 3: Test iteratively

Run `Holmake vyperABITheory` and fix any remaining goals. Use:

```sml
(* To see remaining goals after partial progress *)
val vyper_to_abi_pre_def = cv_auto_trans_pre_rec
  "..." vyper_to_abi_def (
    ... partial_tactic ...
    \\ cheat  (* See what's left *)
  );
```

## Key Theorems Reference

From `cv_stdTheory`:
- `cv_ALOOKUP_def` - definition of cv_ALOOKUP
- `cv_delete_def` - definition of cv_delete
- `cv_delete_ind` - induction principle for cv_delete
- `cv_lookup_def` - definition of cv_lookup
- `cv_size'_def` - definition of cv_size' for sptree
- `cv_size'_cv_mk_BN` - cv_size' (cv_mk_BN x y) = cv_add (cv_size' x) (cv_size' y)
- `cv_size'_cv_mk_BS` - cv_size' (cv_mk_BS x y z) = cv_add (cv_add (cv_size' x) (cv_size' z)) (Num 1)
- `cv_ispair_cv_add` - cv_ispair (cv_add x y) = Num 0

From `cv_repTheory`:
- `cv_termination_simp` - rewrites c2b conditions to structural form

From `cvTheory`:
- `cv_size_def` - cv_size (Num n) = n, cv_size (Pair c d) = 1 + cv_size c + cv_size d
- `cv_snd_def` - cv_snd (Pair c d) = d, cv_snd (Num n) = Num 0
- `cv_fst_def` - cv_fst (Pair c d) = c, cv_fst (Num n) = Num 0
- `cv_sub_def` - cv_sub (Num m) (Num n) = Num (m - n)
- `cv_if_def0` - cv_if p q r = if c2b p then q else r
- `c2n_def` - c2n (Num n) = n, c2n (Pair _ _) = 0
- `c2b_def` - c2b x ⇔ ∃k. x = Num (SUC k)

From `vyperMiscTheory`:
- `cv_size_cv_map_snd_le` - cv_size (cv_map_snd l) ≤ cv_size l

## Estimated Effort

- Helper lemma `cv_ALOOKUP_snd_size`: ~10 lines, straightforward
- Simple termination cases: ~10 lines, mechanical
- StructT case (cv_delete): ~45 lines, requires careful case analysis

Total: ~65-70 lines of tactic code, medium complexity.

## Files to Modify

- `semantics/vyperABIScript.sml`: Replace `cheat` with termination tactic, add helper lemma
