# SSA Construction Pass

This pass converts Venom IR from non-SSA form to SSA form using the classic
dominator-based algorithm.

## Toplevel Definitions

### Transformation

**`mkSsaTransformTheory`:**
- `transform_block` - Transform a basic block (rename uses/definitions)
- `transform_function` - Transform an entire function to SSA form
- `collect_fn_defs` - Collect variable definitions for PHI placement
- `remove_degenerate_phis` - Simplify trivial PHIs after renaming

### Well-formedness

**`mkSsaWellFormedTheory`:**
- `valid_ssa_transform fn fn_ssa vm` - The transformation is valid:
  - Function names match
  - Block counts match
  - Instructions are SSA-compatible under variable mapping `vm`
  - Input function is well-formed (`wf_input_fn`)

## Toplevel Correctness Theorems

**`mkSsaFunctionTheory`:**

```sml
Theorem ssa_construction_correct:
  !fuel fn fn_ssa vm s_orig s_ssa result.
    valid_ssa_transform fn fn_ssa vm /\
    ssa_state_equiv vm s_orig s_ssa /\
    run_function fuel fn s_orig = result ==>
    ?result_ssa.
      run_function fuel fn_ssa s_ssa = result_ssa /\
      ssa_result_equiv vm result result_ssa
```

This states that if:
- The SSA transformation is valid (produces `fn_ssa` from `fn` with mapping `vm`)
- The initial states are SSA-equivalent under `vm`

Then executing the original and transformed functions produces equivalent results.

**`mkSsaFunctionTheory`:**

```sml
Theorem ssa_construction_context_correct:
  !ctx fn_name fuel fn fn_ssa vm s_orig s_ssa result.
    MEM fn ctx.ctx_functions /\
    fn.fn_name = fn_name /\
    valid_ssa_transform fn fn_ssa vm /\
    ssa_state_equiv vm s_orig s_ssa /\
    run_function fuel fn s_orig = result ==>
    ?result_ssa.
      run_function fuel fn_ssa s_ssa = result_ssa /\
      ssa_result_equiv vm result result_ssa
```

Context-level variant that shows the theorem holds for any function in the context.

## Key Definitions

- `ssa_state_equiv vm s1 s2` - States are equivalent under variable mapping `vm`
- `ssa_result_equiv vm r1 r2` - Execution results are equivalent under `vm`
- `inst_ssa_compatible vm inst inst_ssa` - Instructions correspond under `vm`
