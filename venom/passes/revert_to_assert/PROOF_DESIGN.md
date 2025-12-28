# Proof Plan: Revert-to-Assert Pass Correctness

## Verdict: PROVABLE (with caveats on dead code removal)

**Unverified Assumption**: Dead code removal preserves semantics. Removing unreachable blocks doesn't affect execution. **Recommendation**: Defer dead code removal to a separate pass with its own correctness proof.

---

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

## 2. Transformation Hierarchy

```
transform_context : ir_context -> ir_context
    |
    v
transform_function : ir_function -> ir_function
    |
    v
transform_block : ir_function -> basic_block -> basic_block
    |
    v
transform_inst : ir_function -> instruction -> instruction list option
    |
    v
(pattern1_transform | pattern2_transform) : instruction -> instruction list
```

---

## 3. Semantic Equivalence Claims

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

## 4. Validation Against Definitions

### 4.1 JNZ Semantics (venomSemScript.sml)

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

### 4.2 ISZERO Semantics

```sml
| ISZERO => exec_unop (\x. bool_to_word (x = 0w)) inst s
```

Where `bool_to_word T = 1w` and `bool_to_word F = 0w`.

**VERIFIED**: `iszero x` produces `1w` if `x = 0w`, else `0w`.

### 4.3 ASSERT Semantics

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

### 4.4 REVERT Semantics

```sml
| REVERT => Revert (revert_state s)
```

**VERIFIED**: `revert` always returns `Revert (revert_state s)`.

---

## 5. Definitions to Add (rtaTransformScript.sml)

### 5.1 Instruction Builders

```sml
(* Fresh variable name for ISZERO output - uses instruction ID for uniqueness *)
Definition fresh_iszero_var_def:
  fresh_iszero_var id = STRCAT "rta_tmp_" (toString id)
End

(* ISZERO instruction: %out = iszero %cond *)
Definition mk_iszero_inst_def:
  mk_iszero_inst id cond_op out = <|
    inst_id := id;
    inst_opcode := ISZERO;
    inst_operands := [cond_op];
    inst_outputs := [out]
  |>
End

(* ASSERT instruction: assert %cond *)
Definition mk_assert_inst_def:
  mk_assert_inst id cond_op = <|
    inst_id := id;
    inst_opcode := ASSERT;
    inst_operands := [cond_op];
    inst_outputs := []
  |>
End

(* JMP instruction: jmp @label *)
Definition mk_jmp_inst_def:
  mk_jmp_inst id label = <|
    inst_id := id;
    inst_opcode := JMP;
    inst_operands := [Label label];
    inst_outputs := []
  |>
End
```

### 5.2 Revert Block Detection

```sml
(* Check if a label points to a simple revert block *)
Definition is_revert_label_def:
  is_revert_label fn lbl =
    case lookup_block lbl fn.fn_blocks of
      NONE => F
    | SOME bb => is_simple_revert_block bb
End
```

### 5.3 Pattern Transformers

```sml
(* Pattern 1: jnz %cond @revert @else => iszero; assert; jmp @else *)
Definition transform_pattern1_def:
  transform_pattern1 jnz_inst cond_op else_label =
    let id = jnz_inst.inst_id in
    let tmp = fresh_iszero_var id in
    [mk_iszero_inst id cond_op tmp;
     mk_assert_inst (id + 1) (Var tmp);
     mk_jmp_inst (id + 2) else_label]
End

(* Pattern 2: jnz %cond @then @revert => assert %cond; jmp @then *)
Definition transform_pattern2_def:
  transform_pattern2 jnz_inst cond_op then_label =
    let id = jnz_inst.inst_id in
    [mk_assert_inst id cond_op;
     mk_jmp_inst (id + 1) then_label]
End
```

### 5.4 Instruction Transformation

```sml
(* Try to transform a JNZ instruction *)
Definition transform_jnz_def:
  transform_jnz fn inst =
    if inst.inst_opcode <> JNZ then NONE
    else case inst.inst_operands of
      [cond_op; Label if_nonzero; Label if_zero] =>
        (* Pattern 1: revert on nonzero *)
        if is_revert_label fn if_nonzero then
          SOME (transform_pattern1 inst cond_op if_zero)
        (* Pattern 2: revert on zero *)
        else if is_revert_label fn if_zero then
          SOME (transform_pattern2 inst cond_op if_nonzero)
        else NONE
    | _ => NONE
End
```

### 5.5 Block Transformation

```sml
(* Transform all instructions in a block *)
Definition transform_block_insts_def:
  transform_block_insts fn [] = [] /\
  transform_block_insts fn (inst::rest) =
    case transform_jnz fn inst of
      SOME new_insts => new_insts ++ transform_block_insts fn rest
    | NONE => inst :: transform_block_insts fn rest
End

Definition transform_block_def:
  transform_block fn bb =
    bb with bb_instructions := transform_block_insts fn bb.bb_instructions
End
```

### 5.6 Function and Context Transformation

```sml
Definition transform_function_def:
  transform_function fn =
    fn with fn_blocks := MAP (transform_block fn) fn.fn_blocks
End

Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End
```

**Note**: Dead revert block removal is OMITTED. This keeps the proof simpler and the pass still correct (just doesn't optimize as much).

---

## 6. Correctness Theorems

### 6.1 Instruction-Level (Phase 1 - ALREADY PROVEN)

```sml
(* pattern1_transform_correct: ISZERO+ASSERT+JMP ≡ JNZ(revert,else) *)
(* pattern2_transform_correct: ASSERT+JMP ≡ JNZ(then,revert) *)
```

These are proven in `rtaCorrectTheory`.

### 6.2 Block Transformation Correctness

**Goal**:
```sml
Theorem transform_block_correct:
  !fn bb s.
    well_formed_block bb /\
    fresh_vars_unused fn bb s
  ==>
    let bb' = transform_block fn bb in
    let fresh = fresh_vars_in_transform fn bb in
    result_equiv_except fresh
      (run_block fn bb s)
      (run_block fn bb' s)
```

**Proof sketch**:
1. `bb.bb_instructions = prefix ++ [terminator]` where terminator is the last instruction.
2. Case split on terminator:
   - Not a transformable JNZ: `bb' = bb`, trivial by reflexivity
   - Pattern 1: Apply `pattern1_transform_correct` after prefix execution
   - Pattern 2: Apply `pattern2_transform_correct` after prefix execution

**Key lemma needed**:
```sml
run_block_prefix_same:
  !fn bb1 bb2 s.
    TAKE n bb1.bb_instructions = TAKE n bb2.bb_instructions /\
    s.vs_inst_idx = 0 /\
    n <= LENGTH bb1.bb_instructions /\
    n <= LENGTH bb2.bb_instructions
  ==>
    (* After n steps, states are equal *)
    run_n_steps n fn bb1 s = run_n_steps n fn bb2 s
```

### 6.3 Function Transformation Correctness

**Goal**:
```sml
Theorem transform_function_correct:
  !fn s fuel.
    well_formed_function fn /\
    fresh_vars_unused_in_function fn s
  ==>
    let fn' = transform_function fn in
    let fresh = all_fresh_vars fn in
    result_equiv_except fresh
      (run_function fuel fn s)
      (run_function fuel fn' s)
```

**Proof sketch**:
1. Induction on fuel
2. Base case (fuel = 0): Both return `Error "out of fuel"`. Trivial.
3. Inductive case:
   - Look up current block `bb` in `fn.fn_blocks`
   - Look up `bb' = transform_block fn bb` in `fn'.fn_blocks`
   - Apply `transform_block_correct`
   - Case on result, apply IH for `OK` case

**Key lemma needed**:
```sml
state_equiv_except_run_function:
  !fresh fn s1 s2 fuel.
    state_equiv_except fresh s1 s2
  ==>
    result_equiv_except fresh
      (run_function fuel fn s1)
      (run_function fuel fn s2)
```

### 6.4 Context Transformation Correctness

**Goal**:
```sml
Theorem transform_context_correct:
  !ctx s fuel entry.
    well_formed_context ctx /\
    fresh_vars_unused_in_context ctx s
  ==>
    let ctx' = transform_context ctx in
    let fresh = all_fresh_vars_context ctx in
    result_equiv_except fresh
      (run_context fuel ctx entry s)
      (run_context fuel ctx' entry s)
```

Direct from `transform_function_correct`.

---

## 7. Well-Formedness Assumptions

```sml
(* Fresh variables not in initial state *)
Definition fresh_vars_unused_def:
  fresh_vars_unused fn s <=>
    !id. lookup_var (fresh_iszero_var id) s = NONE
End
```

Block well-formedness (non-empty, ends with terminator) is an orthogonal IR invariant, assumed separately if needed.

---

## 8. Required Helper Lemmas

### Already Proven (Phase 1)
1. `pattern1_transform_correct` - ISZERO+ASSERT+JMP correctness
2. `pattern2_transform_correct` - ASSERT+JMP correctness
3. `pattern1_block_correct`, `pattern2_block_correct` - block-level result equiv
4. `step_iszero_value`, `step_assert_behavior`, `step_jnz_behavior` - instruction semantics
5. `state_equiv_except_*` properties - equivalence relation

### Needs Proving
1. **`run_block_prefix_deterministic`**: Identical instruction prefixes produce identical states
2. **`transform_block_insts_preserves_prefix`**: Non-JNZ instructions unchanged
3. **`fresh_var_not_in_state`**: `fresh_iszero_var id` not in state (well-formedness assumption)
4. **`lookup_block_map_transform`**: Block lookup works in transformed function
5. **`state_equiv_except_run_block`**: Equivalence preserved through run_block

---

## 9. Potential Difficulties

### 9.1 Fresh Variable Handling

**Issue**: Pattern 1 introduces `%tmp` for iszero output.

**Solution**: Use `state_equiv_except {tmp}` to show equivalence modulo the fresh variable. This is sound because:
1. The fresh variable is not in the original program
2. It's only used as input to the immediately following assert
3. After the assert, it's dead

### 9.2 Revert State Equivalence

**Issue**: Need to show `revert_state s1` ≈ `revert_state s2` when s1, s2 differ by fresh var.

**Solution**: `revert_state` only sets `vs_halted` and `vs_reverted` flags. It doesn't depend on variables.

### 9.3 Fresh Variable Naming

Must assume input programs don't use `rta_tmp_*` names. Alternatively, use a more sophisticated fresh name generation.

### 9.4 Instruction IDs

The transformed instructions reuse/increment the original JNZ's ID. Must ensure no ID collisions. Could use `3*id`, `3*id+1`, `3*id+2` to guarantee uniqueness.

---

## 10. Proof Strategy Summary

1. **Define transformations** (trivial)
2. **Prove prefix lemma**: Identical prefixes → identical intermediate states
3. **Prove block correctness**: By case on terminator, using Phase 1 + prefix lemma
4. **Prove function correctness**: By induction on fuel, using block correctness + equiv preservation
5. **Prove context correctness**: Direct from function correctness

---

## 11. Files Structure

```
venom/passes/revert_to_assert/
├── Holmakefile
├── rtaDefsScript.sml         # Pattern predicates, state_equiv_except (~150 LOC)
├── rtaPropsScript.sml        # Instruction lemmas (~300 LOC)
├── rtaCorrectScript.sml      # Pattern correctness theorems (~250 LOC)
└── rtaTransformScript.sml    # Transformation definitions + correctness (TODO)
```

---

## 12. Current Status

### Completed ✓
- [x] Pattern predicates: `is_simple_revert_block`, `is_jnz_to_revert_pattern1/2`
- [x] State equivalence: `state_equiv_except` and properties
- [x] Instruction lemmas: `step_iszero_value`, `step_assert_behavior`, etc.
- [x] Pattern correctness: `pattern1_transform_correct`, `pattern2_transform_correct`
- [x] Block correctness: `pattern1_block_correct`, `pattern2_block_correct`

### Remaining
- [ ] Instruction builders (`mk_iszero_inst`, etc.)
- [ ] Pattern transformers (`transform_pattern1/2`)
- [ ] Block transformation definition
- [ ] Block transformation correctness
- [ ] Function transformation definition + correctness
- [ ] Context transformation definition + correctness
