# Proof Plan: Revert-to-Assert Pass Correctness

## 1. Pass Behavior Summary

The `revert-to-assert` pass transforms control flow patterns involving conditional jumps to revert blocks into assertion-based control flow.

**Source**: `~/vyper/trees/vyper-venom-ir-rewrite/vyper/venom/passes/revert_to_assert.py`

**Pattern 1** (revert on true):
```
jnz %cond, @revert_block, @else_block    →    %tmp = iszero %cond
revert_block: revert 0, 0                      assert %tmp
                                               jmp @else_block
```

**Pattern 2** (revert on false):
```
jnz %cond, @then_block, @revert_block    →    assert %cond
revert_block: revert 0, 0                      jmp @then_block
```

**Applicability conditions**:
- Revert block contains exactly one instruction: `revert 0, 0`
- Predecessor ends with `jnz` that targets the revert block

---

## 2. Semantic Equivalence Claims

### Pattern 1: `jnz cond, @revert, @else` ≡ `iszero cond; assert result; jmp @else`

| Condition | Original | Transformed |
|-----------|----------|-------------|
| `cond ≠ 0w` | jnz → @revert → `revert 0,0` → Revert | iszero → 0w, assert 0w → Revert |
| `cond = 0w` | jnz → @else | iszero → 1w, assert 1w → OK, jmp @else |

### Pattern 2: `jnz cond, @then, @revert` ≡ `assert cond; jmp @then`

| Condition | Original | Transformed |
|-----------|----------|-------------|
| `cond ≠ 0w` | jnz → @then | assert succeeds → OK, jmp @then |
| `cond = 0w` | jnz → @revert → `revert 0,0` → Revert | assert 0w → Revert |

---

## 3. Validation Against Definitions

### 3.1 JNZ Semantics (venomSemScript.sml:321-329)

```sml
| JNZ =>
    (case inst.inst_operands of
      [cond_op; Label if_nonzero; Label if_zero] =>
        (case eval_operand cond_op s of
          SOME cond =>
            if cond <> 0w then OK (jump_to if_nonzero s)
            else OK (jump_to if_zero s)
        | NONE => Error "undefined condition")
    | _ => Error "jnz requires cond and 2 labels")
```

**VERIFIED**: JNZ jumps to `if_nonzero` when `cond ≠ 0w`, to `if_zero` when `cond = 0w`.

### 3.2 ISZERO Semantics (venomSemScript.sml:243)

```sml
| ISZERO => exec_unop (\x. bool_to_word (x = 0w)) inst s
```

Where `bool_to_word T = 1w` and `bool_to_word F = 0w`.

**VERIFIED**: `iszero x` produces `1w` if `x = 0w`, else `0w`.

### 3.3 ASSERT Semantics (venomSemScript.sml:338-346)

```sml
| ASSERT =>
    (case inst.inst_operands of
      [cond_op] =>
        (case eval_operand cond_op s of
          SOME cond =>
            if cond = 0w then Revert (revert_state s)
            else OK s
        | NONE => Error "undefined operand")
    | _ => Error "assert requires 1 operand")
```

**VERIFIED**: `assert cond` reverts if `cond = 0w`, continues if `cond ≠ 0w`.

### 3.4 REVERT Semantics (venomSemScript.sml:334)

```sml
| REVERT => Revert (revert_state s)
```

**VERIFIED**: `revert` always returns `Revert (revert_state s)`.

---

## 4. Key Lemmas Required

### Lemma A: ISZERO produces expected value

```sml
step_iszero_value:
  ∀s cond cond_op out id.
    eval_operand cond_op s = SOME cond
  ⇒
    step_inst <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
```

### Lemma B: ASSERT behavior

```sml
step_assert_behavior:
  ∀s cond cond_op id.
    eval_operand cond_op s = SOME cond
  ⇒
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then Revert (revert_state s) else OK s
```

### Lemma C: Revert block execution

```sml
revert_block_exec:
  ∀fn bb s.
    bb.bb_instructions = [<| inst_opcode := REVERT;
                             inst_operands := [Lit 0w; Lit 0w]; ... |>]
  ⇒
    run_block fn bb (s with vs_inst_idx := 0) = Revert (revert_state s)
```

### Lemma D: ISZERO-ASSERT chain (Pattern 1)

```sml
iszero_assert_chain:
  ∀s cond cond_op iszero_out.
    eval_operand cond_op s = SOME cond ∧
    lookup_var iszero_out s = NONE  (* fresh *)
  ⇒
    let s1 = update_var iszero_out (bool_to_word (cond = 0w)) s in
    step_inst (assert_inst (Var iszero_out)) s1 =
      if cond ≠ 0w then Revert (revert_state s1) else OK s1
```

---

## 5. Main Correctness Theorems

### Theorem 1: Pattern 1 Correctness

```sml
revert_to_assert_pattern1_correct:
  ∀cond_op else_label iszero_out s cond.
    (* Preconditions *)
    eval_operand cond_op s = SOME cond ∧
    lookup_var iszero_out s = NONE  (* fresh variable *)
  ⇒
    (* Case: cond ≠ 0w - both revert *)
    (cond ≠ 0w ⇒
      (* Original: jnz takes revert branch, revert block reverts *)
      (* Transformed: iszero produces 0w, assert 0w reverts *)
      result_equiv
        (Revert (revert_state s))
        (Revert (revert_state (update_var iszero_out 0w s)))) ∧
    (* Case: cond = 0w - both continue to else *)
    (cond = 0w ⇒
      (* Original: jnz jumps to else *)
      (* Transformed: iszero produces 1w, assert passes, jmp else *)
      state_equiv_except {iszero_out}
        (jump_to else_label s)
        (jump_to else_label (update_var iszero_out 1w s)))
```

### Theorem 2: Pattern 2 Correctness

```sml
revert_to_assert_pattern2_correct:
  ∀cond_op then_label s cond.
    eval_operand cond_op s = SOME cond
  ⇒
    (* Case: cond ≠ 0w - both continue to then *)
    (cond ≠ 0w ⇒
      state_equiv (jump_to then_label s) (jump_to then_label s)) ∧
    (* Case: cond = 0w - both revert *)
    (cond = 0w ⇒
      result_equiv (Revert (revert_state s)) (Revert (revert_state s)))
```

---

## 6. Proof Strategy

### 6.1 Core Strategy: Case Split on Condition Value

Both patterns require splitting on `cond = 0w`:

**Pattern 1** (`jnz cond @revert @else`):
- **Case `cond ≠ 0w`**: Both revert, need `revert_state` equivalence
- **Case `cond = 0w`**: Both jump to else, need state equiv modulo fresh var

**Pattern 2** (`jnz cond @then @revert`):
- **Case `cond ≠ 0w`**: Both jump to then, trivial state equiv
- **Case `cond = 0w`**: Both revert, trivial

### 6.2 Fresh Variable Handling

Pattern 1 introduces a fresh variable for iszero output. Options:

1. **Relaxed equivalence**: Define `state_equiv_except vars s1 s2` ignoring vars
2. **Show deadness**: Prove the variable is never read after assertion
3. **Projection**: Project out fresh variable when comparing

**Recommended**: Option 1 - simplest and most general.

```sml
Definition state_equiv_except_def:
  state_equiv_except vars s1 s2 ⇔
    (∀v. v ∉ vars ⇒ lookup_var v s1 = lookup_var v s2) ∧
    s1.vs_memory = s2.vs_memory ∧
    s1.vs_storage = s2.vs_storage ∧
    (* ... other fields ... *)
End
```

### 6.3 Block-Level vs Instruction-Level

**Recommended: Block-level proof**
- Model transformation as replacing one basic block with another
- Prove the two blocks are semantically equivalent
- Cleaner and matches how the pass operates

---

## 7. Files to Create

```
venom/passes/revert_to_assert/
├── Holmakefile
├── revertAssertDefsScript.sml     # Transformation definitions (~150 LOC)
├── revertAssertPropsScript.sml    # Key lemmas (~300 LOC)
└── revertAssertCorrectScript.sml  # Main correctness theorems (~250 LOC)
```

### 7.1 revertAssertDefsScript.sml

```sml
(* Predicate: block is a simple revert block *)
Definition is_simple_revert_block_def:
  is_simple_revert_block bb ⇔
    LENGTH bb.bb_instructions = 1 ∧
    (HD bb.bb_instructions).inst_opcode = REVERT ∧
    (HD bb.bb_instructions).inst_operands = [Lit 0w; Lit 0w]
End

(* Predicate: instruction is jnz to revert block (pattern 1) *)
Definition is_jnz_to_revert_pattern1_def:
  is_jnz_to_revert_pattern1 inst revert_label ⇔
    inst.inst_opcode = JNZ ∧
    ∃cond else_label.
      inst.inst_operands = [cond; Label revert_label; Label else_label]
End

(* Predicate: instruction is jnz from revert block (pattern 2) *)
Definition is_jnz_to_revert_pattern2_def:
  is_jnz_to_revert_pattern2 inst revert_label ⇔
    inst.inst_opcode = JNZ ∧
    ∃cond then_label.
      inst.inst_operands = [cond; Label then_label; Label revert_label]
End

(* Relaxed state equivalence ignoring a set of variables *)
Definition state_equiv_except_def:
  state_equiv_except vars s1 s2 ⇔
    (∀v. v ∉ vars ⇒ lookup_var v s1 = lookup_var v s2) ∧
    s1.vs_memory = s2.vs_memory ∧
    s1.vs_storage = s2.vs_storage ∧
    s1.vs_transient = s2.vs_transient ∧
    s1.vs_current_bb = s2.vs_current_bb ∧
    s1.vs_inst_idx = s2.vs_inst_idx ∧
    s1.vs_prev_bb = s2.vs_prev_bb ∧
    s1.vs_halted = s2.vs_halted ∧
    s1.vs_reverted = s2.vs_reverted
End
```

### 7.2 revertAssertPropsScript.sml

Key lemmas about individual instruction behavior:

```sml
(* ISZERO produces correct value *)
Theorem step_iszero_value: ...

(* ASSERT reverts on zero *)
Theorem step_assert_zero_reverts: ...

(* ASSERT passes on non-zero *)
Theorem step_assert_nonzero_passes: ...

(* Simple revert block always reverts *)
Theorem simple_revert_block_reverts: ...

(* state_equiv_except is reflexive *)
Theorem state_equiv_except_refl: ...

(* state_equiv implies state_equiv_except *)
Theorem state_equiv_implies_except: ...

(* update_var preserves state_equiv_except for the updated var *)
Theorem update_var_state_equiv_except: ...
```

### 7.3 revertAssertCorrectScript.sml

Main correctness theorems:

```sml
(* Pattern 1: jnz cond @revert @else ≡ iszero; assert; jmp @else *)
Theorem pattern1_correct: ...

(* Pattern 2: jnz cond @then @revert ≡ assert; jmp @then *)
Theorem pattern2_correct: ...

(* Block-level correctness for pattern 1 *)
Theorem pattern1_block_equiv: ...

(* Block-level correctness for pattern 2 *)
Theorem pattern2_block_equiv: ...
```

---

## 8. Potential Difficulties

### 8.1 Fresh Variable Handling

**Issue**: Pattern 1 introduces `%tmp` for iszero output.

**Solution**: Use `state_equiv_except {tmp}` to show equivalence modulo the fresh variable. This is sound because:
1. The fresh variable is not in the original program
2. It's only used as input to the immediately following assert
3. After the assert, it's dead

### 8.2 Revert State Equivalence

**Issue**: Need to show `revert_state s1` ≈ `revert_state s2` when s1, s2 differ by fresh var.

**Solution**: `revert_state` only sets `vs_halted` and `vs_reverted` flags. It doesn't depend on variables, so:
```sml
revert_state (update_var x v s) = revert_state s with vs_vars := ...
```
The reverted states are equivalent in all observable ways.

### 8.3 Multi-Block Reasoning

**Issue**: Original code spans two blocks (pred + revert), transformed is one block.

**Solution**:
- For revert case: Show both produce `Revert` with equivalent states
- For continue case: Show both produce `OK` with equivalent jump destinations
- Don't need to reason about the unreachable revert block after transformation

---

## 9. Verdict

**PROVABLE**

All semantic claims verified against definitions. The proof is straightforward case analysis on the condition value. Main complexity is the fresh variable, handled by relaxed equivalence.

---

## 10. Estimated Effort

| File | Effort | Notes |
|------|--------|-------|
| revertAssertDefsScript.sml | 1-2 hours | Straightforward definitions |
| revertAssertPropsScript.sml | 3-4 hours | Lemmas about instructions |
| revertAssertCorrectScript.sml | 4-6 hours | Main correctness theorems |

**Total: ~8-12 hours**

---

## 11. Implementation Checklist

- [ ] Create directory structure `venom/passes/revert_to_assert/`
- [ ] Write Holmakefile with dependencies
- [ ] Implement `revertAssertDefsScript.sml`
  - [ ] `is_simple_revert_block`
  - [ ] `is_jnz_to_revert_pattern1/2`
  - [ ] `state_equiv_except`
- [ ] Implement `revertAssertPropsScript.sml`
  - [ ] `step_iszero_value`
  - [ ] `step_assert_zero_reverts`
  - [ ] `step_assert_nonzero_passes`
  - [ ] `simple_revert_block_reverts`
  - [ ] `state_equiv_except` properties
- [ ] Implement `revertAssertCorrectScript.sml`
  - [ ] Pattern 1 instruction-level correctness
  - [ ] Pattern 2 instruction-level correctness
  - [ ] Block-level equivalence theorems
- [ ] Build and verify no CHEAT warnings
